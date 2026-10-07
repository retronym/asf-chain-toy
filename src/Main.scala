package asftoy

import scala.util.Random

/** A cake-shaped workload with independent knobs:
 *  - `d`: owner-chain depth. Traits O1 ⊃ O2 ⊃ ... ⊃ Od, reached by the path `v1.v2...vd` (so prefix path
 *    length p = d + 1 including the final val `x`).
 *  - `L`: linearization of the prefix class. Inside Od: `B1[A1] <: B2[A1] <: ... <: BL[A(L-1)]`, each parent
 *    written as `Od.this#B(j+1)[Aj]`.
 *  - `n`: size of the member's info (a binary tree of `Fun` nodes); `tFrac`/`qFrac` of its leaves are this-types
 *    (drawn from O1.this..Od.this, BL.this) and BL's type parameter.
 *  The member `m` is declared in BL and selected on `pre = v1.v2...vd.x.type` where `x: Od.this#B1[Int]`. */
final case class Workload(d: Int, L: Int, n: Int, tFrac: Double = 0.25, qFrac: Double = 0.25, seed: Int = 1) {
  val top = new Cls("Top", null, Nil)
  val os: Vector[Cls] = (1 to d).foldLeft(Vector.empty[Cls]) { (acc, i) => acc :+ new Cls(s"O$i", acc.lastOption.orNull, Nil) }
  val od = os.last
  val bs: Vector[Cls] = (1 to L).toVector.map(j => new Cls(s"B$j", od, List(new TParam(s"A$j"))))
  for (j <- 0 until L - 1) bs(j).parents = List(Ref(ThisT(od), bs(j + 1), List(TParamT(bs(j).tparams.head))))
  val bl = bs.last

  val vs: Vector[Val] = os.indices.toVector.map { i =>
    if (i == 0) new Val("v1", top, Ref(Root, os(0), Nil))
    else new Val(s"v${i + 1}", os(i - 1), Ref(ThisT(os(i - 1)), os(i), Nil))
  }
  val paths: Vector[Type] = vs.indices.toVector.map(i => vs.take(i + 1).foldLeft(Root: Type)((p, v) => Single(p, v)))
  val x = new Val("x", od, Ref(ThisT(od), bs.head, List(Const("Int"))))
  val pre: Type = Single(paths.last, x)

  val m: Val = {
    val rnd = new Random(seed)
    val leaves = (n + 1) / 2
    val t = math.max(1, math.round(leaves * tFrac).toInt)
    val q = math.round(leaves * qFrac).toInt
    val thisCands = os.map(ThisT(_)) :+ ThisT(bl)
    val ls = rnd.shuffle(
      Vector.fill(t)(thisCands(rnd.nextInt(thisCands.size)): Type) ++
      Vector.fill(q)(TParamT(bl.tparams.head): Type) ++
      Vector.fill(math.max(0, leaves - t - q))(Const("K"): Type))
    def build(xs: Vector[Type]): Type =
      if (xs.size == 1) xs.head else { val (a, b) = xs.splitAt(xs.size / 2); Fun(List(build(a)), build(b)) }
    new Val("m", bl, build(ls))
  }
  def thisLeaves: Int = { def c(t: Type): Int = t match { case _: ThisT => 1; case Fun(ps, r) => ps.map(c).sum + c(r); case _ => 0 }; c(m.tpe) }
}

object Main {
  def resetAll(): Unit = { Counters.reset(); Scalac.clearCaches(); IntelliJ.clearCaches() }

  /** Counters for one operation, after a warm-up pass that fills the class-level caches both designs keep
   *  (BTS per class, MixinNodes signature substitutors) — the per-use cost is what we compare. */
  def measure(w: Workload)(op: Workload => Type): (Type, Map[String, Long]) = {
    resetAll()
    op(w)                    // warm class-level caches (and, when enabled, the per-use memo tables)
    Counters.reset()
    if (!keepMemo) { Scalac.clearPerUse(); IntelliJ.clearPerUse() }
    val r = op(w)
    (r, Counters.snapshot)
  }
  var keepMemo = false

  def scalacOp(w: Workload): Type = Scalac.memberInfo(w.pre, w.m)
  def ijOp(w: Workload): Type = IntelliJ.memberInfo(w.pre, w.m)

  def nanos(w: Workload, reps: Int)(op: Workload => Type): Double = {
    Counters.enabled = false
    try {
      resetAll(); op(w)
      val samples = (1 to 7).map { _ =>
        val t0 = System.nanoTime()
        var i = 0
        while (i < reps) { if (!keepMemo) { Scalac.clearPerUse(); IntelliJ.clearPerUse() }; op(w); i += 1 }
        (System.nanoTime() - t0).toDouble / reps
      }
      samples.sorted.apply(3)
    } finally Counters.enabled = true
  }

  def g(m: Map[String, Long], k: String) = m.getOrElse(k, 0L)

  val scalacCols = Seq("scalac.nodes", "scalac.thisSteps", "scalac.tparamSteps", "scalac.enclScan", "scalac.baseType", "scalac.btsScan", "scalac.relativize", "scalac.asSeenFrom")
  val ijCols = Seq("ij.apply", "ij.updateChecks", "ij.nodes", "ij.thisWalks", "ij.ownerSteps", "ij.prefixSteps", "ij.baseType", "ij.baseTypeVisited", "ij.supersOf", "ij.hashedNodes", "ij.canonicalize", "ij.designatorSingletonType", "ij.linkCreated", "ij.followedCopied")

  def table(title: String, knob: String, rows: Seq[(String, Workload)], timeReps: Int = 200): Unit = {
    println(s"\n### $title\n")
    println(s"| ${if (knob == "n") "n" else knob + " | n"} | this-leaves | scalac ns | IJ ns | IJ/scalac | " + (scalacCols ++ ijCols).map(_.replace("scalac.", "s.").replace("ij.", "ij.")).mkString(" | ") + " |")
    println("|" + Seq.fill((if (knob == "n") 5 else 6) + scalacCols.size + ijCols.size)("---").mkString("|") + "|")
    for ((label, w) <- rows) {
      val (rs, cs) = measure(w)(scalacOp)
      val (ri, ci) = measure(w)(ijOp)
      if (rs != ri) { mismatches += 1; if (mismatches <= 3) println(s"<!-- MISMATCH $label\n scalac ${Types.show(rs)}\n ij     ${Types.show(ri)} -->") }
      val ts = nanos(w, timeReps)(scalacOp)
      val ti = nanos(w, timeReps)(ijOp)
      println(f"| ${if (knob == "n") label else label + " | " + w.n} | ${w.thisLeaves} | $ts%.0f | $ti%.0f | ${ti / ts}%.1f | " + scalacCols.map(g(cs, _)).mkString(" | ") + " | " + ijCols.map(g(ci, _)).mkString(" | ") + " |")
    }
  }
  var mismatches = 0

  def main(args: Array[String]): Unit = {
    val which = args.headOption.getOrElse("all")
    def on(s: String) = which == "all" || which == s

    if (on("n")) table("E1: type size n (d=3, L=4)", "n", Seq(15, 63, 255, 1023, 4095).map(n => n.toString -> Workload(3, 4, n)))
    if (on("d")) table("E2: owner depth d (n=63, L=4)", "d", (1 to 8).map(d => d.toString -> Workload(d, 4, 63)))
    if (on("L")) table("E3: linearization L (n=63, d=3)", "L", Seq(1, 2, 4, 8, 16, 32).map(l => l.toString -> Workload(3, l, 63)))
    if (on("t")) table("E4: this-leaf fraction (n=255, d=3, L=4)", "tFrac", Seq(0.0, 0.05, 0.1, 0.25, 0.5, 0.75).map(f => f.toString -> Workload(3, 4, 255, tFrac = f, qFrac = 0.1)))
    if (on("k")) fusion()
    if (on("cache")) caching()
    if (on("ref")) perReference()
    println(s"\nscalac/IntelliJ result mismatches: $mismatches")
  }

  /** E5: chain length k, fused vs unfused, on one type. Extra links are bindings of an unrelated type
   *  parameter (identity on this type), as a long resolution chain carries. */
  def fusion(): Unit = {
    println("\n### E5: chain length k, fused vs unfused (n=255, d=3, L=4)\n")
    println("| extra links | k | fused ns | unfused ns | fused updateChecks | fused nodes | unfused updateChecks | unfused nodes | thisWalks | scalac ns (one asSeenFrom) |")
    println("|---|---|---|---|---|---|---|---|---|---|")
    val w = Workload(3, 4, 255)
    val dummy = new TParam("Z")
    for (extra <- Seq(0, 1, 2, 4, 8, 16, 32)) {
      val extraSubst = (1 to extra).foldLeft(IntelliJ.empty)((s, _) => s.followed(new IntelliJ.Subst(Array(IntelliJ.TParamSub(Map(dummy -> Const("Q")))))))
      def op(w: Workload) = IntelliJ.resolveChain(w.pre, w.m).followed(extraSubst)(w.m.tpe)
      val k = { resetAll(); IntelliJ.resolveChain(w.pre, w.m).followed(extraSubst).k }
      IntelliJ.forceUnfused = false
      val (_, cf) = measure(w)(op); val tf = nanos(w, 200)(op)
      IntelliJ.forceUnfused = true
      val (_, cu) = measure(w)(op); val tu = nanos(w, 200)(op)
      IntelliJ.forceUnfused = false
      val ts = nanos(w, 200)(scalacOp)
      println(f"| $extra | $k | $tf%.0f | $tu%.0f | ${g(cf, "ij.updateChecks")} | ${g(cf, "ij.nodes")} | ${g(cu, "ij.updateChecks")} | ${g(cu, "ij.nodes")} | ${g(cf, "ij.thisWalks")} | $ts%.0f |")
    }
  }

  /** E6: what each memo buys, per operation, with per-use memo tables kept warm (as a long-lived cache would be). */
  def caching(): Unit = {
    println("\n### E6: memoization variants (n=255, d=4, L=8), memo tables warm\n")
    println("| variant | IJ ns | scalac ns | thisWalks | ij.baseType | baseTypeVisited | canonicalize | designatorSingletonType |")
    println("|---|---|---|---|---|---|---|---|")
    val w = Workload(4, 8, 255)
    val variants = Seq[(String, () => Unit)](
      "PR #5 as is"            -> (() => ()),
      "cache baseType"         -> (() => IntelliJ.cacheBaseType = true),
      "cache singleton"        -> (() => IntelliJ.cacheSingleton = true),
      "cache baseType+singleton" -> (() => { IntelliJ.cacheBaseType = true; IntelliJ.cacheSingleton = true }),
      "cache this-walk"        -> (() => IntelliJ.cacheWalk = true),
      "all three"              -> (() => { IntelliJ.cacheBaseType = true; IntelliJ.cacheSingleton = true; IntelliJ.cacheWalk = true }))
    for ((name, set) <- variants) {
      IntelliJ.cacheBaseType = false; IntelliJ.cacheSingleton = false; IntelliJ.cacheWalk = false
      set()
      keepMemo = true
      val (_, c) = measure(w)(ijOp); val ti = nanos(w, 200)(ijOp); val ts = nanos(w, 200)(scalacOp)
      keepMemo = false
      println(f"| $name | $ti%.0f | $ts%.0f | ${g(c, "ij.thisWalks")} | ${g(c, "ij.baseType")} | ${g(c, "ij.baseTypeVisited")} | ${g(c, "ij.canonicalize")} | ${g(c, "ij.designatorSingletonType")} |")
    }
    IntelliJ.cacheBaseType = false; IntelliJ.cacheSingleton = false; IntelliJ.cacheWalk = false
  }

  /** E7: one reference `v1.v2...vd.x.m`, resolved hop by hop with `c` same-named candidates per hop
   *  (overloads or an unfiltered processor). scalac: findMember + one memberType per candidate; IntelliJ: per
   *  candidate a chain built at resolution and applied to the member's declared type. Per-use caches cold. */
  def perReference(): Unit = {
    println("\n### E7: per reference `v1...vd.x.m`, c candidates per hop (n=63, L=4)\n")
    println("| d | c | scalac ns | IJ ns | IJ/scalac | s.asSeenFrom | s.baseType | ij.apply | ij.linkCreated | ij.canonicalize | ij.thisWalks | ij.baseType | ij.baseTypeVisited |")
    println("|---|---|---|---|---|---|---|---|---|---|---|---|---|")
    for (d <- Seq(1, 2, 4, 8); c <- Seq(1, 4)) {
      val w = Workload(d, 4, 63)
      val hops: Seq[(Type, Val)] = (w.vs.indices.tail.map(i => (w.paths(i - 1), w.vs(i))) :+ (w.paths.last, w.x)) :+ (w.pre, w.m)
      def sOp(w: Workload): Type = { var r: Type = null; for ((q, v) <- hops; _ <- 1 to c) r = Scalac.memberInfo(q, v); r }
      def iOp(w: Workload): Type = { var r: Type = null; for ((q, v) <- hops; _ <- 1 to c) r = IntelliJ.memberInfo(q, v); r }
      val (_, cs) = measure(w)(sOp); val (_, ci) = measure(w)(iOp)
      val ts = nanos(w, 100)(sOp); val ti = nanos(w, 100)(iOp)
      println(f"| $d | $c | $ts%.0f | $ti%.0f | ${ti / ts}%.1f | ${g(cs, "scalac.asSeenFrom")} | ${g(cs, "scalac.baseType")} | ${g(ci, "ij.apply")} | ${g(ci, "ij.linkCreated")} | ${g(ci, "ij.canonicalize")} | ${g(ci, "ij.thisWalks")} | ${g(ci, "ij.baseType")} | ${g(ci, "ij.baseTypeVisited")} |")
    }
  }
}
