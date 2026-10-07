# Viewing a member from a prefix: scalac's `asSeenFrom` vs IntelliJ's substitutor chain, a cost model

## Problem

PR #5 changed how IntelliJ rewrites `C.this` when it views a member's type from a prefix. The rewrite is now scalac's: an owner-chain walk anchored at the member's class, running inside `ScSubstitutor`'s fused, lazily applied update chain. This note asks what that costs and where. I derive a cost model for both designs from the code, then check it in three ways: counters and an async-profiler run on highlighting scala/scala's `Typers.scala`, a synthetic depth sweep on the real plugin, and toy re-implementations of both algorithms with counters (this repo). The model predicts one hot spot. The measurements confirm it, but it accounts for about a tenth of plugin CPU, not most of it.

**Short answer:** the asymptotics of the two designs are close. IntelliJ's cost comes from constants and from repetition: each this-leaf walk calls an uncached, exhaustive `BaseTypes.baseType`, and the same walks are recomputed hundreds of times. There is also one latent exponential, in path depth, from uncached canonicalization. Fusion is irrelevant at the chain lengths that actually occur. Memoizing `baseType` and canonicalization are the cheap fixes. A single `memberType(pre, m)` entry point (design note §8.2 in the PR #5 comments) is the structural fix.

Results in one paragraph. On one highlight of `Typers.scala` (6.7k lines), PR #5 applies 2.33M substitutors. Their mean length is 1.84 links, 54% have one link, and 99.3% are fused. They run 1.85M this-walks over only 4,067 distinct `(this, target, class)` triples (99.8% repeats) and 232k `BaseTypes.baseType` calls over 2,080 distinct `(type, class)` keys (99.1% repeats). async-profiler puts all substitution work at 10% of plugin CPU: 7.9% is the walk, three quarters of that `baseType`. Memoizing `baseType` and the walk gives a paired median of about 0.91× base on Typers, with per-rep ratios ranging 0.85–1.39. On synthetic cakes the model's second prediction holds and is the sharper finding. Canonicalizing a prefix path re-canonicalizes its own prefix through the uncached `designatorSingletonType`, so cost grows about ×2.8 per level of path depth (20 references at depth 8: 2.04M substitutor applications, 2.1 s). Memoizing canonicalization flattens it (11.8k applications, 0.18 s).

Sources: scalac at scala/scala b4ad4458da (`src/reflect/scala/reflect/internal`, cited as `TypeMaps.scala:N` etc.), IntelliJ at retronym/intellij-scala `fdd8ed14ad` (PR #5 tip; paths below `scala/scala-impl/src/org/jetbrains/plugins/scala/lang/psi/`).

## Parameters

| symbol | meaning |
|---|---|
| `n` | nodes in the type being mapped (`n_ℓ` leaves, `n_i` internal) |
| `t` | this-type leaves (`C.this`) in it |
| `q` | class-type-parameter leaves in it |
| `d` | owner-chain steps the walk takes from the member's class until the cursor matches the this-type's class (≤ owner depth) |
| `p` | prefix path length (`a.b.c` has `p = 3`) |
| `L` | linearization size of the (widened) prefix's class at a walk step |
| `V`, `E` | nodes and edges of the base-type DAG that IntelliJ's `BaseTypes.dfs` visits (`V ≥ L`; types deduplicated by equality, not by class) |
| `k` | links in a substitutor chain; `r ≤ k` of them are this-type links |
| `c` | candidates per selection whose type gets computed (overloads, unfiltered processors) |
| `R` | scalac `relativize`: asSeenFrom + instantiation of one base-type-sequence element (a small type, `Owner.this#P[args]`) |
| `B_s`, `B_i` | one `baseType` lookup: scalac, IntelliJ |
| `W` | one IntelliJ this-walk (`doUpdateThisTypeFromClass`) |
| `N` | one `isMoreNarrow` |
| `C(p)` | canonicalizing a path of length `p` (`collapseSingletonPath`) |

## scalac: one `asSeenFrom`

`tp.asSeenFrom(pre, clazz)` (`Types.scala:677`) returns `tp` in O(1) when `tp.isTrivial` (a flag memoized on `TypeRef`/`SingleType`, `Types.scala:1423,2373`) or `skipPrefixOf(pre, clazz)`. Otherwise it allocates one `AsSeenFromMap` and maps `tp` once (`TypeMaps.scala:417,443`). Every node costs a match. Three cases do more.

- **This-leaf** (`thisTypeAsSeen`, `TypeMaps.scala:636`). The loop climbs `clazz.owner` and `(pre baseType clazz).prefix` in step until `matchesPrefixAndClass` holds, at most `d` steps. Each step pays `matchesPrefixAndClass` (`TypeMaps.scala:577`), which compares `clazz == candidate` first and only on equality does `pre.widen.baseTypeIndex(clazz)`. That is a linear scan of an `Int` array of symbol ids over the cached base type sequence (`BaseTypeSeqs.scala:119`), O(L). Each non-matching step also pays `pre baseType clazz`. For a class `TypeRef` that is `relativize(sym.info.baseType(clazz))` (`Types.scala:2492`): another O(L) index scan of the class's cached BTS plus `R`, the asSeenFrom and instantiation of one small element (`Types.scala:2447`). `ThisType` and `SingleType` delegate to `underlying` (`Types.scala:167`), and `SingleType.underlying` is cached per period (`Types.scala:1435`).
- **Class-type-parameter leaf** (`classParameterAsSeen`, `TypeMaps.scala:554`). The same loop, ending in `correspondingTypeArgument`, O(#tparams). Before it, `isTypeParamOfEnclosingClass` (`TypeMaps.scala:456–470`) loops the enclosing classes of `seenFromClass`, each `encl isSubClass base` being one more BTS index scan (`Symbols.scala:3290`): O(d·L).
- **Singleton prefix** (`singleTypeAsSeen`). Maps the prefix, O(p).

So, with the BTS caches warm:

`T_s(asSeenFrom) = O(n + t·d·(L + R) + q·d·(L + R))`, and O(1) if `tp` is trivial.

`R` is itself an `asSeenFrom`, but of a BTS element whose size is the size of a parent clause, and its own walk usually matches at its first step (`Owner.this` against `Owner`). Uncached, the first `baseTypeSeq` of a class costs O(L) element thunks (`BaseTypeSeqs.scala:75` evaluates them lazily). `TypeRef` instances are hash-consed, so the per-`TypeRef` BTS (`Types.scala:2613`) is shared across uses. `memberType` adds a one-entry cache per method symbol keyed on `pre eq` (`Symbols.scala:3086–3114`, until typer is done). **Every per-use step of a scalac walk is an index scan over a cached array; nothing is recomputed structurally.**

## IntelliJ: building a chain

A resolve result carries a substitutor that is extended as resolution proceeds:

1. **Signature substitutor**, per class, cached (`MixinNodes.SuperTypesData`, `impl/toplevel/typedef/MixinNodes.scala:217`, `ModTracker.libraryAware`). For each base class `S` in the linearization it holds `bind(S.tparams) >> link(C.this, S) >> dependentLink` (`:247–252`). That is O(L) links per class, built once.
2. **`TypeDefinitionMembers.process`** (`:359–361`): `sig.followed(state.substitutor)` for every signature delivered to the processor, an array copy of O(k) (`ScSubstitutor.followed`, `types/recursiveUpdate/ScSubstitutor.scala:96`).
3. **`BaseProcessor`** adds links while it widens the qualifier. The projection's `actualSubst` (`ScProjectionType.actualImpl`, `types/api/designator/ScProjectionType.scala:77`, `cachedWithRecursionGuard` keyed on the projected type) contributes one. So do the self-type route (`BaseProcessor.scala:206`), the type-parameter-bound route (`:279`) and `processElement`'s `followed` (`:406`).
4. **`substitutorWithThisType(owner(m))`** (`ScalaResolveState.scala:112`, called from `MethodResolveProcessor.scala:132`, `SignatureProcessor.scala:146,231`, the implicit processors and `ConstructorResolveProcessor`) prepends `link(fromType, owner(m))`. Its construction canonicalizes the target (`ScSubstitutor.scala:219` → `ThisTypeSubstitution.canonicalizeTarget` → `ScProjectionType.collapseSingletonPath`, `ScProjectionType.scala:340`).

Per candidate this is `O(k + C(p))`. `C(p)` is the interesting term. `collapseSingletonPath` recurses on the prefix (fuel 8) and, for each stable element, calls `designatorSingletonType` (`ScProjectionType.scala:46`), which is **not cached**. That applies `actualSubst` to the val's declared type, i.e. a chain application with its own walks. When that application rewrites the prefix of a projection, `updateProjectionType` canonicalizes again (`SubtypeUpdater.scala:118`) and re-collapses the same prefix. So `C(p) = 2·C(p−1) + A(val type)` in the worst case: **exponential in `p`, capped by fuel 8 at 2⁸**. Whether the doubling happens depends on whether path elements' declared types are this-prefixed projections; §Measurements checks this on the real plugin.

## IntelliJ: applying a chain

`ScSubstitutor.apply` (`ScSubstitutor.scala:58`) → `recursiveUpdateImpl` (`:69`).

- **Fused** (all links are `LeafSubstitution`, `hasNonLeafSubstitutions` false, `:42`). At a non-leaf node the first link answers `ProcessSubtypes` and the node's children are visited with the whole chain: one check. At a leaf, each link answers `ReplaceWith` and the next link runs on the result: k checks. A replacement that is not a leaf (a this-leaf rewritten to a path `a.b.c`) is then traversed by the remaining links (`:80`). Total checks are `n_i + n_ℓ·k`, plus re-traversal of replacements, `Σ size(res_j)·(k − j)`.
- **Unfused** (any non-leaf link). Each link does its own full traversal and allocates an intermediate type (`:85–87`): `k·n` node visits.

Fusion therefore saves the `(k−1)·n_i` internal-node revisits and `k−1` intermediate types. It does not save leaf work: that is O(n_ℓ·k) either way, whereas scalac does O(n_ℓ) with one map. Projections rebuilt over a changed prefix pay `C(p)` (`SubtypeUpdater.scala:118`).

Each this-leaf meets every this-link, so there are `t·r` walks per application, plus walks triggered inside them (below). One walk, `ThisTypeSubstitution.doUpdateThisTypeFromClass` (`ThisTypeSubstitution.scala:81`), takes up to `d` owner steps. Each step pays the following.

- `isInheritorDeep` (`:89`): O(1), a set lookup in the cached `superPathsDeep` (`ScTemplateDefinitionImpl.scala:215,227`, `ModTracker.physicalPsiChange`).
- `isMoreNarrow` (`:190`): `N`. It is tail-recursive over the target's declared type, self type, bound or alias. Every step goes through `extractAll` (`:237`), which reads cached element types and `actualElement`. It is bounded by the length `h` of that declared-type chain. `visited` breaks cycles only for bindings, type parameters and type definitions (`:192–215`), so the bound I can justify is O(h) with h finite on well-formed code. A proof that the other four cases strictly descend would tighten it.
- `BaseTypes.baseType(target, clazz)` (`types/BaseTypes.scala:128`) when the cursor doesn't match. That is `B_i`, below.
- At the end, `doUpdateThisType` (`:64`) climbs the target's prefix, up to `p` steps of `N`. `ownerChainMatches` (`:148`) climbs `clazz`'s owners, O(d), with `isInheritorDeep`.

So `W = O(d·(N + B_i) + p·N)`.

`B_i`, **IntelliJ's `baseType`, is uncached and exhaustive**: `(Iterator(t) ++ dfs(t)).filter(_.extractClass.contains(clazz)).toList` (`BaseTypes.scala:129`). It walks the whole base-type DAG of `t` even after finding `clazz`, then merges if several arms match (`mergeSameClass`, `:144`). Each visited node costs the following.

- `supersOf` (`:192`): for a class type, its declared parents with the type's substitutor applied (`declaredSuperTypes`, `:229`). That is a chain application per parent, and a this-link in that substitutor (a bare projection's `actualSubst`) makes it a nested walk. A singleton is first widened through `designatorSingletonType` (`:216`), uncached, another application. A this-type goes through its class type and self type (`:204`).
- Hashing it into `seenTypes`, O(size).
- `extractClass`.

So `B_i = O(Σ_{v∈V} (deg(v)·(A(parent) + size(parent))))`, roughly O(E·s) plus nested walks, against scalac's O(L) scan plus one `R`. Nesting is bounded only by `TypeRecursionGuard.MaxSubstitutionDepth = 64` (`TypeRecursionGuard.scala:24`).

Putting it together, one application costs

`T_i(apply) = O(n_i + n_ℓ·k + Σ_j size(res_j)·(k−j) + t·r·W + (#rebuilt projections)·C(p))`, with `W = O(d·(N + B_i) + p·N)`.

The term-by-term comparison with scalac's `O(n + t·d·(L + R))` is:

- `n_ℓ·k` vs `n`. Fusion makes this cheap when k is small.
- `t·r` vs `t` walks. Every this-link walks every this-leaf.
- `B_i = O(E·s + nested walks)` vs `L + R`. This is the dominant constant.

## Per-reference totals

For a selection chain `q₁.q₂…q_p.m` with `c` candidates per hop:

- **scalac**: `Σ_hops (findMember + c·T_s)`. Each hop's qualifier type is materialized once, and `SingleType.underlying` and the BTS are cached.
- **IntelliJ**: `Σ_hops (processType + c·(k + C(p)) + a·T_i)`. `processType` gets `actual` from a cache. `a` is the number of times a resolved candidate's type is actually computed. Laziness means the chain is applied *each time* a consumer asks for a type: parameter types in applicability checking, the return type, conformance, annotators. No cache keyed on (chain, type) exists, so `a` is a property of the callers, not of the design. Typers.scala measures it below.

## Measurements

Setup: worktree at `fdd8ed14ad` plus counters (local branch `claude/asf-perf-model`, worktree `asf-perf`; `AsfStats` counters are off unless `ASF_STATS=true`). The harness is `TypersHighlightingTimingTest` with the real JDK 17 and scala-asm on the classpath, scala/scala b4ad4458da sources as a source root, caches dropped before every highlight. Batch sbt, one or two at a time. The machine was shared with other sessions (load average 16–21), so wall-clock numbers are noisy. Counters are exact and deterministic run to run. Raw outputs are in `data/`.

### Counters on Typers.scala (one highlight, warm JIT)

| quantity | value | reading |
|---|---|---|
| substitutor applications | 2.33M | 9.3 per candidate signature delivered (251k) |
| chain length `k` | mean 1.84; k=1 54%, k≤4 98%, max ≤32 | chains are short |
| this-links per chain `r` | mean 1.72 | most chains are this-links |
| unfused applications | 16k (0.7%) | fusion's benefit is nearly unused |
| update checks | 8.1M (3.5 per application) | the types are tiny: `n` is a handful of nodes |
| this-walks | 1.85M, of which 0.70M nested inside another walk | 0.79 per application |
| distinct walk keys `(this, target, class)` | 4,067 | **99.8% of walks are repeats** |
| owner steps / prefix steps per walk | 1.09 / 0.66 | `d` and `p` are ≈1 in practice |
| `isMoreNarrow` steps | 1.69M (0.91 per walk) | `N` is cheap |
| `BaseTypes.baseType` calls | 232k (0.13 per walk) | |
| distinct `(type, class)` keys | 2,080 | **99.1% repeats** |
| base-type DAG nodes visited per call | mean 16.3; 21% visit 33–128 | `V` ≫ the one hit needed |
| merged (several arms of the class) | 0.5% | |
| canonicalizations | 1.20M (0.39M at link construction, the rest at projection rebuild); nested 0.9% | |
| `followed` concatenations | 392k, mean result 4.0 links | |

**The model's terms are all small (`k≈2`, `d≈1`, `p≈1`, `n` tiny). The cost is repetition: the same few thousand walks and base types are recomputed hundreds of times each.**

### Profile (async-profiler, cpu, 1 ms, one warm highlight, counters off)

Shares are inclusive, as a fraction of samples with a plugin frame (83% of all samples):

| frames | share |
|---|---|
| union of `ScSubstitutor.apply`, `canonicalizeTarget`, `BaseTypes.baseType`, the walk | **10.0%** |
| `ScSubstitutor.apply` (incl. walks) | 9.7% |
| the walk (`doUpdateThisTypeFromClass`) | 7.9%, of which `BaseTypes.baseType` 75%, `supersOf` 59%, nested `apply` 22%, `isInheritor` 17%, `designatorSingletonType` 13%, `isMoreNarrow` 13% |
| `BaseTypes.baseType` | 5.9% |
| `designatorSingletonType` | 3.7% |
| `canonicalizeTarget` | 1.7% |
| for scale: conformance / `TypeDefinitionMembers` / `MixinNodes` | 21% / 15% / 11% |
| unrelated: `ScalaColorSchemeAnnotator` → `ScProjectionType.presentableText` | 3.5% |

**The profile agrees with the model on where substitution time goes (the walk's uncached `baseType`) and bounds the prize: about 6–8% of plugin CPU on this file.**

### Memoization A/B on Typers.scala (variants interleaved per rep in one JVM)

Experiment-only, unscoped `ConcurrentHashMap` memos, cleared with the caches before each highlight. A real cache would be keyed on a modification tracker.

| run | base | memo `baseType` | memo `baseType` + walk | memo canonicalize | all three |
|---|---|---|---|---|---|
| 4 warm reps, median ms | 14,422 | 13,410 | 13,846 | | |
| 10 warm reps, median ms (load ≈ 20) | 18,937 | 17,778 | 17,129 | | |
| paired ratio vs base, median of 10 | 1 | 0.94 | 0.91 | | |
| 6 warm reps, median ms (load ≈ 21) | 17,025 | | | 18,634 | 20,089 |

Error count stayed 0 in every variant. **A 5–9% gain from memoizing `baseType` and the walk is consistent with the profile, but the noise on this machine is about as large as the gain. The canonicalization memo has nothing to save on Typers.**

### Synthetic depth sweep on the real plugin

`D{d}.scala` (in `data/synth`) nests traits `O1 ⊃ … ⊃ Od`, each with `class Ci` and `val v(i+1): O(i+1)`. In `Od`, `B1[A] <: … <: B4[A]`, `B4` declares `def m: (O1.this.C1, …, Od.this.Cd, A)`, and `val x: B1[Int]`. Twenty references `Top.v1.v2…vd.x.m`. A deliberate error shows that the inferred type is right at every depth: `(Top.v1.C1, Top.v1.v2.C2, …, Int)`.

| d | applications | walks | canonicalizations (nested) | `baseType` | ms | applications, canon memo | walks, canon memo | ms, canon memo |
|---|---|---|---|---|---|---|---|---|
| 1 | 1,961 | 320 | 710 (60) | 60 | 76 | 1,625 | 242 | 79 |
| 2 | 4,518 | 1,213 | 1,690 (538) | 180 | 89 | 2,205 | 648 | 78 |
| 3 | 11,876 | 3,873 | 4,566 (2,539) | 340 | 111 | 3,307 | 1,301 | 100 |
| 4 | 31,153 | 11,165 | 12,039 (8,938) | 604 | 139 | 4,517 | 2,114 | 103 |
| 5 | 84,488 | 31,449 | 32,523 (28,052) | 943 | 165 | 6,057 | 3,270 | 103 |
| 6 | 249,710 | 94,559 | 95,986 (89,494) | 1,573 | 312 | 7,735 | 4,548 | 114 |
| 7 | 719,131 | 273,761 | 275,631 (266,699) | 2,272 | 688 | 9,702 | 6,124 | 123 |
| 8 | 2,043,555 | 779,739 | 782,148 (770,219) | 3,144 | 2,068 | 11,762 | 7,736 | 182 |

The base column grows about ×2.8 per level. That matches `C(p) = 2·C(p−1) + A`, with the application itself spawning walks. Fuel does not bound it, because the nested canonicalization starts in `updateProjectionType` with fresh fuel 8; only `TypeRecursionGuard`'s depth 64 does. **With canonicalization memoized, growth is roughly quadratic in `d` (walks ≈ 120·d²). The exponential is a real latent hot spot that ordinary code (Typers: 0.9% nesting) rarely reaches.**

### Toy models (this repo, `results.md`)

Both designs are re-implemented over a small type language (`src/`), with the exact control flow of `thisTypeAsSeen` / `classParameterAsSeen` / BTS on one side and `recursiveUpdateImpl` / `doUpdateThisTypeFromClass` / exhaustive `baseType` / `collapseSingletonPath` on the other. Both compute the same types on every workload (0 mismatches). Counters per operation, after warming the class-level caches both designs keep:

- **Type size `n`** (E1). Both are linear. IntelliJ's update checks are about 6n at k=5 (`n_i + n_ℓ·k`), scalac's map nodes about 1.7n.
- **Linearization `L`** (E3, L = 1→32). scalac's BTS scan grows 24→832 int comparisons and its time stays flat. IntelliJ's visited base-type nodes grow 8→536, hashed nodes 0→1,488 and nested applications 44→552, so time grows ≈15×. **`B_i` is O(E·s) against scalac's O(L) scan, and it shows.**
- **Owner depth `d`** (E2). IntelliJ's canonicalizations double per level (27→6,885 for d=1→8). That reproduces the real plugin's exponential, at ×2 rather than ×2.8 because the toy has fewer nested walks per level.
- **Chain length `k`, fused vs unfused** (E5, n=255, n_ℓ=128). Fused: node visits constant (481), update checks +128 per link, i.e. `n_ℓ`. Unfused: +208 node visits per link. **Fusion removes the internal-node revisits, as claimed. It cannot remove the per-leaf check per link, and at the observed k≈2 there is little to remove.**
- **Memoization** (E6, warm memo tables). `baseType` memo: 214 µs → 16 µs per operation. Walk memo: → 13 µs. All three: 10 µs, below scalac's ~17 µs, because a hit skips the walk entirely while scalac recomputes its walk on every use.
- **Per reference** (E7). Both scale with `c`. At `d ≤ 4` IntelliJ is 1–4× scalac; at `d = 8` it is 20–45× (the canonicalization exponential).

## Strengths and weaknesses that follow from the model

**IntelliJ's chain.**

- *Fusion* saves `(k−1)·n_i` revisits and `k−1` intermediate types per application. It is a good idea when chains are long and types are big. Typers has neither (mean k=1.84, ~3.5 checks per application), so fusion is close to irrelevant, and its leaf cost `n_ℓ·k` is never better than scalac's `n`.
- *Laziness* wins when a resolve result's type is never asked for: candidates rejected by name, kind or accessibility before typing. It loses when the type is asked for repeatedly. The chain is re-applied for every consumer (9.3 applications per candidate on Typers), and nothing caches `(chain, type) → type`. scalac pays `memberType` once per (pre, sym) during typer through `typeAsMemberOf`'s one-entry cache.
- *Every this-link sees every this-leaf* (`t·r` walks), including leaves introduced by an earlier link's replacement. scalac rewrites each leaf once. At `r≈1.7` this is a small factor.
- *`BaseTypes.baseType`* is the real weakness: uncached, exhaustive (`toList` instead of first hit), structurally deduplicated (types hashed, and each parent re-substituted per visit), and re-entrant (parents' substitutors carry links that start nested walks). scalac's equivalent is an index scan of an array cached per class and per hash-consed `TypeRef`.
- *Canonicalization at construction and at rebuild* keeps paths from compounding (the reason it exists, `ThisTypeSubstitution.scala:268–276`). Its uncached `designatorSingletonType` makes it exponential in path depth.

**scalac's `asSeenFrom`.**

- One traversal and one walk per leaf. Every per-step operation reads a cache (BTS, `SingleType.underlying`, hash-consed `TypeRef`s).
- It recomputes the walk for every leaf and every use too. It has no memo of `(this, pre, clazz)`, but its per-step constant is so small that it doesn't need one.
- It materializes the member type eagerly per `(pre, sym)`, so there is no chain to grow and nothing to fuse.

**Bottom line: the designs have the same shape of cost (one owner-chain walk per this-leaf, a base-type lookup per step). IntelliJ's version has a large constant (`B_i`), a repetition factor (laziness without a result cache) and one exponential (canonicalization). None of them requires abandoning the chain.**

## Recommendations

1. **Cache `BaseTypes.baseType(t, clazz)`**, keyed on `(t, clazz)` and scoped to a PSI modification tracker (as `superPathsDeep` is). Also make it stop at the first hit when no merge is possible, i.e. when `clazz` has no type parameters or `t`'s DAG has one path to it. It is 99.1% repeats on Typers, 5.9% of plugin CPU, and the toy shows a 13× per-operation gain. Low risk: it is a pure function of `t` and the PSI.
2. **Cache canonicalization** (`canonicalizeTarget` or `designatorSingletonType`) per projection, same scoping. This removes the exponential in path depth (2.1 s → 0.18 s at depth 8) and costs nothing on ordinary code. Of the three, this is the one that fixes a complexity class rather than a constant.
3. **Memoize the walk** on `(ScThisType, target, seenFromClass)` only if (1) leaves a measurable residue. It is 99.8% repeats, but its key includes arbitrary target types, so it is less obviously safe under recursion guards than (1).
4. **Longer term, move toward §8.2's single `memberType(pre, m)` entry point.** Compute a member's type once per `(prefix, member)` and cache it, as scalac's `typeAsMemberOf` does. Hand that type to consumers instead of re-applying a chain per consumer. This attacks the repetition factor (9.3 applications per candidate) at its source. It also makes the chain mostly a carrier of bindings, which is what fusion is good at. The cost model suggests doing (1) and (2) first: they are local, measurable and independent of the redesign.
5. Don't invest in fusion or in shortening chains. At the observed `k` there is nothing to win.

## Caveats

- **Timing noise.** The machine ran other sessions throughout (load average 16–21). Warm-rep medians drifted between runs from 13 s to 19 s for the same code. The A/B gains (≤10%) are at the noise floor. The counters and the profile shares are the solid evidence; repeat the A/B on a quiet machine before deciding on (1) alone.
- **One file.** Typers.scala is cake-heavy but shallow-pathed. Files with deep stable paths (`global.analyzer.typer.infer…`) or wide linearizations would weigh `B_i` and `C(p)` more.
- **Memo correctness.** The A/B memos are unscoped maps cleared between highlights. Error counts were unchanged (0 on Typers, the expected single error per synthetic file), but the broad test set was not run against them. Values computed under a tripped `cachedWithRecursionGuard` could be memoized, and a production cache must respect that.
- **Bounds I couldn't tighten.** `isMoreNarrow` is bounded by the declared-type chain length on well-formed code (measured: ~0.5 steps per call); a descent argument for its four `visited`-free cases would make that a proof. The nesting of walks inside `baseType` is bounded only by `TypeRecursionGuard` (64) in the model; measured nesting was 38% of walks, at shallow depth.
- **Toy fidelity.** The toy omits self types, refinements, aliases, existentials, overloading and scalac's `captureThis`. Its IntelliJ side reproduces one quirk (an applied projection's parents are substituted with the argument binding only, `ParameterizedType.substitutor`), and both sides still agree on every workload. Absolute toy timings mean little; the counters and their growth rates are the point.
- **Counter overhead.** `ASF_STATS_KEYS` hashes keys on hot paths, so the counter runs' own timings (20–29 s) are inflated. Profile and A/B runs had counters off.
