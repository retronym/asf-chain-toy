package asftoy

import scala.collection.mutable
import Counters.inc

/** IntelliJ's design, after `ScSubstitutor` / `ThisTypeSubstitution` / `BaseTypes` on
 *  retronym/intellij-scala PR #5 (fdd8ed14ad).
 *
 *  - a substitutor is an array of updates; `followed` concatenates (ScSubstitutor.scala:96);
 *  - leaf-only updates are fused into one traversal (`recursiveUpdateImpl`, ScSubstitutor.scala:68):
 *    a non-leaf node costs one update check, a leaf costs one check per remaining link, and a link's
 *    replacement is re-traversed by the rest of the chain;
 *  - a `ThisTypeSubstitution` link rewrites each `C.this` leaf by an owner-chain walk
 *    (`doUpdateThisTypeFromClass`) that calls the uncached, exhaustive, merged `BaseTypes.baseType`;
 *  - a projection rebuilt over a rewritten prefix is canonicalized (SubtypeUpdater.scala:118), as is a
 *    link's target at construction (ScSubstitutor.scala:219); `collapseSingletonPath` widens each stable
 *    path element through `designatorSingletonType`, itself a chain application.
 *
 *  Switches model the variants the write-up discusses. */
object IntelliJ {
  var forceUnfused      = false // pretend a non-leaf update is present: one traversal per link
  var cacheBaseType     = false // memoize BaseTypes.baseType on (type, class)
  var cacheWalk         = false // memoize the this-walk on (this, target, class)
  var cacheSingleton    = false // memoize designatorSingletonType per path

  sealed trait Update
  final case class TParamSub(map: Map[TParam, Type]) extends Update
  final case class ThisSub(target: Type, seenFromClass: Cls) extends Update

  final class Subst(val ups: Array[Update], val from: Int = 0) {
    def isEmpty = ups.length == 0
    def next = new Subst(ups, from + 1)
    def followed(o: Subst): Subst =
      if (isEmpty) o else if (o.isEmpty) this
      else { inc("ij.followed"); inc("ij.followedCopied", ups.length + o.ups.length); new Subst(ups ++ o.ups) }
    def k = ups.length
    def apply(t: Type): Type = { inc("ij.apply"); inc("ij.apply.k", ups.length); recursiveUpdateImpl(t, this) }
    override def toString = ups.mkString(" >> ")
  }
  val empty = new Subst(Array())
  def bind(c: Cls, args: List[Type]): Subst =
    if (c.tparams.isEmpty) empty else new Subst(Array(TParamSub(c.tparams.zip(args).toMap)))

  /** ScSubstitutor.apply(updateThisType, seenFromClass), ScSubstitutor.scala:216 */
  def link(target: Type, seenFromClass: Cls): Subst =
    if (seenFromClass == null) empty
    else { inc("ij.linkCreated"); new Subst(Array(ThisSub(canonicalize(target), seenFromClass))) }

  private def isLeaf(t: Type) = t match {
    case _: ThisT | _: TParamT | _: Const => true
    case Root => true
    case _ => false
  }

  private sealed trait After
  private final case class ReplaceWith(t: Type) extends After
  private case object ProcessSubtypes extends After

  private def runUpdate(u: Update, t: Type): After = {
    inc("ij.updateChecks")
    if (!isLeaf(t)) ProcessSubtypes
    else (u, t) match {
      case (TParamSub(m), TParamT(p)) => ReplaceWith(m.getOrElse(p, t))
      case (ThisSub(target, cls), th: ThisT) => ReplaceWith(thisWalk(th, target, cls))
      case _ => ReplaceWith(t)
    }
  }

  private def recursiveUpdateImpl(t: Type, s: Subst): Type =
    if (s.from >= s.ups.length) t
    else {
      val u = s.ups(s.from)
      runUpdate(u, t) match {
        case ReplaceWith(res) => recursiveUpdateImpl(res, s.next)
        case ProcessSubtypes =>
          if (forceUnfused) {
            val withCurrent = updateSubtypes(t, new Subst(Array(u)))
            recursiveUpdateImpl(withCurrent, s.next)
          } else updateSubtypes(t, s)
      }
    }

  /** SubtypeUpdater.updateSubtypes; projections over a rewritten prefix are canonicalized. */
  private def updateSubtypes(t: Type, s: Subst): Type = {
    inc("ij.nodes")
    t match {
      case Ref(pre, c, args) =>
        val pre1 = recursiveUpdateImpl(pre, s); val args1 = args.map(recursiveUpdateImpl(_, s))
        if ((pre1 eq pre) && args1.lazyZip(args).forall(_ eq _)) t
        else if (pre1 eq pre) Ref(pre, c, args1)
        else canonicalize(Ref(pre1, c, args1))
      case Single(pre, v) =>
        val pre1 = recursiveUpdateImpl(pre, s)
        if (pre1 eq pre) t else canonicalize(Single(pre1, v))
      case Fun(ps, r) => Fun(ps.map(recursiveUpdateImpl(_, s)), recursiveUpdateImpl(r, s))
      case other => other
    }
  }

  // ---------------------------------------------------------------- canonicalization
  private val singletonCache = mutable.HashMap[Single, Type]()

  /** ScProjectionType.designatorSingletonType: the val's declared type through the projection's
   *  `actualSubst` (a link onto the prefix, none when the prefix is a this-type). Not cached in PR #5. */
  def designatorSingletonType(s: Single): Type = {
    def compute = {
      inc("ij.designatorSingletonType")
      actualSubst(s.pre, s.v.owner) match {
        case sub if sub.isEmpty => s.v.tpe
        case sub                => sub(s.v.tpe)
      }
    }
    if (cacheSingleton) singletonCache.getOrElseUpdate(s, compute) else compute
  }

  /** ScProjectionType.actualImpl (ScProjectionType.scala:77), `cachedWithRecursionGuard` keyed on the
   *  projected type: the link onto the prefix (none when the prefix is a this-type). Long-lived cache. */
  private val actualCache = mutable.HashMap[(Type, Cls), Subst]()
  def actualSubst(pre: Type, owner: Cls): Subst = pre match {
    case Root | _: ThisT => empty
    case _ => actualCache.getOrElseUpdate((pre, owner), { inc("ij.actualComputed"); link(pre, owner) })
  }

  /** ScProjectionType.collapseSingletonPath (fuel 8): collapse the prefix, then a stable element whose
   *  singleton type is itself a path. */
  def canonicalize(t: Type, fuel: Int = 8): Type = {
    inc("ij.canonicalize")
    t match {
      case s @ Single(pre, v) if fuel > 0 =>
        val pre1 = canonicalize(pre, fuel - 1)
        val w = if (pre1 eq pre) s else Single(pre1, v)
        designatorSingletonType(w) match {
          case single: Single if single != w => canonicalize(single, fuel - 1)
          case _                             => w
        }
      case r @ Ref(pre, c, args) if fuel > 0 =>
        val pre1 = canonicalize(pre, fuel - 1)
        if (pre1 eq pre) r else Ref(pre1, c, args)
      case other => other
    }
  }

  // ---------------------------------------------------------------- BaseTypes.baseType
  private val baseTypeCache = mutable.HashMap[(Type, Cls), Option[Type]]()

  private def extractClass(t: Type): Option[Cls] = t match {
    case Ref(_, c, _) => Some(c)
    case ThisT(c)     => Some(c)
    case _            => None
  }

  /** BaseTypes.supersOf: direct supertypes, substituting each declared parent. */
  private def supersOf(t: Type): Seq[Type] = {
    inc("ij.supersOf")
    t match {
      case ThisT(c)  => supersOf(c.selfRef)
      case s: Single => supersOf(designatorSingletonType(s))
      case Ref(pre, c, args) =>
        // ClassType.unapply: an applied type uses only its argument binding (ParameterizedType.substitutor);
        // a bare projection over a path uses `actualSubst`, i.e. a link onto the prefix.
        val subst =
          if (args.nonEmpty) bind(c, args)
          else actualSubst(pre, c.owner)
        c.parents.map(p => if (subst.isEmpty) p else subst(p))
      case _ => Nil
    }
  }

  /** BaseTypes.scala:128: `(Iterator(t) ++ dfs(t)).filter(_.extractClass.contains(clazz)).toList`, merged. */
  def baseType(t: Type, clazz: Cls): Option[Type] = {
    def compute: Option[Type] = {
      inc("ij.baseType")
      val seen = mutable.HashSet[Type]()
      val stack = mutable.Stack[Type]()
      val out = mutable.ListBuffer[Type]()
      def visit(x: Type): Unit = { inc("ij.baseTypeVisited"); if (extractClass(x).contains(clazz)) out += x }
      visit(t)
      supersOf(t).reverseIterator.foreach(x => { inc("ij.hashedNodes", Types.size(x)); if (seen.add(x)) stack.push(x) })
      while (stack.nonEmpty) {
        val x = stack.pop()
        visit(x)
        supersOf(x).reverseIterator.foreach(y => { inc("ij.hashedNodes", Types.size(y)); if (seen.add(y)) stack.push(y) })
      }
      val d = out.distinct
      if (d.size > 1) inc("ij.baseTypeMerged")
      d.headOption
    }
    if (cacheBaseType) baseTypeCache.getOrElseUpdate((t, clazz), compute) else compute
  }

  // ---------------------------------------------------------------- the this-walk
  private val walkCache = mutable.HashMap[(ThisT, Type, Cls), Type]()

  def thisWalk(th: ThisT, target: Type, cls: Cls): Type = {
    def compute = { inc("ij.thisWalks"); doUpdateThisTypeFromClass(th, target, cls) }
    if (cacheWalk) walkCache.getOrElseUpdate((th, target, cls), compute) else compute
  }

  private def isInheritorDeep(c: Cls, base: Cls) = (c ne base) && c.isSubClass(base) // cached superPathsDeep set
  private def isSameOrInheritor(c: Cls, th: ThisT) = (c eq th.c) || isInheritorDeep(c, th.c)

  private def containingClassType(t: Type): Option[Type] = t match {
    case ThisT(c) if c.owner != null => Some(ThisT(c.owner))
    case Ref(pre, _, _) if pre ne Root => Some(pre)
    case Single(pre, _) if pre ne Root => Some(pre)
    case _ => None
  }

  // ThisTypeSubstitution.isMoreNarrow (the cases our toy can produce)
  private def isMoreNarrow(target: Type, th: ThisT): Boolean = {
    inc("ij.narrowSteps")
    target match {
      case ThisT(c)     => isSameOrInheritor(c, th)
      case Ref(_, c, _) => isSameOrInheritor(c, th)
      case Single(_, v) => v.tpe match {
        case ThisT(c) if c eq th.c => false
        case nt                    => isMoreNarrow(nt, th)
      }
      case _ => false
    }
  }

  @annotation.tailrec
  private def doUpdateThisType(th: ThisT, target: Type): Type = {
    inc("ij.prefixSteps")
    if (isMoreNarrow(target, th)) target
    else containingClassType(target) match {
      case Some(tc) => doUpdateThisType(th, tc)
      case None     => th
    }
  }

  @annotation.tailrec
  private def ownerChainReaches(c: Cls, th: ThisT): Boolean =
    if (c == null) false else if (isSameOrInheritor(c, th)) true else ownerChainReaches(c.owner, th)

  private def targetDenotesLeafClass(target: Type, th: ThisT): Boolean = {
    def denotes(t: Type) = extractClass(t).contains(th.c)
    denotes(target) || (target match { case s: Single => denotes(s.v.tpe); case _ => false })
  }

  private def ownerChainMatches(c: Cls, target: Type, th: ThisT) =
    ownerChainReaches(c, th) || targetDenotesLeafClass(target, th)

  @annotation.tailrec
  private def doUpdateThisTypeFromClass(th: ThisT, target: Type, clazz: Cls): Type = {
    inc("ij.ownerSteps")
    if (isInheritorDeep(th.c, clazz) && isMoreNarrow(target, th)) doUpdateThisType(th, target)
    else if ((clazz eq th.c) || clazz.owner == null) {
      if (ownerChainMatches(clazz, target, th)) doUpdateThisType(th, target) else th
    } else baseType(target, clazz).flatMap(containingClassType) match {
      case Some(tc) => doUpdateThisTypeFromClass(th, tc, clazz.owner)
      case None =>
        if (ownerChainMatches(clazz, target, th)) doUpdateThisType(th, target) else th
    }
  }

  def clearCaches(): Unit = { baseTypeCache.clear(); walkCache.clear(); singletonCache.clear(); sigCache.clear(); actualCache.clear() }
  /** The memo tables the variants add (none exist in PR #5); MixinNodes' signature substitutors stay. */
  def clearPerUse(): Unit = { baseTypeCache.clear(); walkCache.clear(); singletonCache.clear() }

  // ---------------------------------------------------------------- resolution: building the chain
  /** MixinNodes.SuperTypesData (cached per class): the signature substitutor for a member of base class
   *  `b` seen in class `c` = bind(b's tparams as seen from c) >> link(c.this, b). */
  private val sigCache = mutable.HashMap[(Cls, Cls), Subst]()
  def signatureSubst(c: Cls, b: Cls): Subst = sigCache.getOrElseUpdate((c, b), {
    inc("ij.sigSubstComputed")
    val bt = Scalac.baseType(ThisT(c), b).get // the class-level hierarchy is cached in both designs
    val bindArgs = if (b.tparams.isEmpty) empty else bind(b, bt.args)
    if (c eq b) empty else bindArgs.followed(link(ThisT(c), b))
  })

  /** The substitutor a resolve result for member `m` carries when found on qualifier type `qual`:
   *  `substitutorWithThisType(owner(m))` = link(fromType, owner(m)) >> sig_{C, owner(m)} >> state.substitutor,
   *  where C and state.substitutor come from processing `qual` (BaseProcessor.processType). */
  def resolveChain(qual: Type, m: Val): Subst = {
    inc("ij.resolveChain")
    // processType(qual): widen a path to its class type, collecting the state substitutor
    def process(t: Type): (Cls, Subst) = t match {
      case s: Single => process(designatorSingletonType(s))
      case ThisT(c)  => (c, empty)
      case Ref(pre, c, args) =>
        val proj = actualSubst(pre, c.owner)
        (c, proj.followed(bind(c, args)))
      case _ => sys.error(s"cannot process $t")
    }
    val (c, stateSubst) = process(qual)
    val fromType = qual match { case _: Single => Some(qual); case _ => None }
    val sig = signatureSubst(c, m.owner).followed(stateSubst)
    fromType.fold(sig)(ft => link(ft, m.owner).followed(sig))
  }

  def memberInfo(qual: Type, m: Val): Type = resolveChain(qual, m)(m.tpe)
}
