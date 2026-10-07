# asf-chain-toy

Toy models of two designs for viewing a member's type from a prefix, with work counters:

- **scalac** (`src/Scalac.scala`): one `AsSeenFromMap(pre, clazz)` per use, `thisTypeAsSeen` / `classParameterAsSeen` climbing `clazz`'s owner chain in step with `pre baseType clazz`, base type sequences cached per class, `SingleType.underlying` cached. After scala/scala b4ad4458da `TypeMaps.scala` / `Types.scala` / `BaseTypeSeqs.scala`.
- **IntelliJ** (`src/IntelliJ.scala`): an array-of-updates substitutor (`TParamSub`, `ThisSub`), concatenated by `followed`, leaf updates fused into one traversal, the this-walk calling an uncached exhaustive `BaseTypes.baseType`, projections canonicalized when rebuilt and at link construction. After retronym/intellij-scala PR #5 (fdd8ed14ad) `ScSubstitutor` / `ThisTypeSubstitution` / `BaseTypes` / `ScProjectionType`.

The type language (`src/Model.scala`) has this-types, class type parameters, class types with a prefix, singleton paths and an opaque internal node. `src/Main.scala` generates a cake-shaped workload with independent knobs (owner depth `d`, linearization `L`, type size `n`, this-leaf fraction) and checks that both designs compute the same type (`mismatches: 0`).

The cost-model write-up that uses these results is `WRITEUP.md` in this repo. The real-plugin instrumentation it reports on (counters, memo flags, profiling harness) is retronym/intellij-scala#15.

```bash
scala-cli run . -- all      # or one of: n d L t k cache ref
```

Counters are the robust output. Wall-clock columns are medians of 7 batches and only indicative.
