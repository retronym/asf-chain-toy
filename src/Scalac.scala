package asftoy

import scala.collection.mutable
import Counters.inc

/** scalac's design, after `TypeMaps.AsSeenFromMap` and `Types.baseType` / `BaseTypeSeqs`
 *  (scala/scala b4ad4458da, src/reflect/scala/reflect/internal).
 *
 *  - one `TypeMap` per `asSeenFrom(pre, clazz)`, applied to a member's info;
 *  - `thisTypeAsSeen` / `classParameterAsSeen` climb `clazz`'s owner chain in step with `pre baseType clazz`;
 *  - the base type sequence is cached per class (and per TypeRef, hash-consed); `baseType` on a class
 *    TypeRef is an index scan of the cached BTS plus `relativize` of the found element;
 *  - `SingleType.underlying` is cached per (hash-consed) singleton type. */
object Scalac {
  final class BTS(val classes: Array[Cls], val elems: Array[Ref])

  private val btsCache = mutable.HashMap[Cls, BTS]()
  private val underlyingCache = mutable.HashMap[Single, Type]()
  def clearCaches(): Unit = { btsCache.clear(); underlyingCache.clear() }
  /** scalac's caches (BTS, SingleType.underlying) live for a whole phase: nothing is per use. */
  def clearPerUse(): Unit = ()

  /** Types.scala:1614 `baseTypeSeq` (cached per period): elements in the class's own view. */
  def bts(c: Cls): BTS = btsCache.getOrElseUpdate(c, {
    inc("scalac.btsComputed")
    val lin = c.linearization
    val elems = lin.map { b =>
      if (b eq c) c.selfRef
      else {
        val p = c.parents.find(_.c.isSubClass(b)).get
        baseType(p, b).get
      }
    }
    new BTS(lin.toArray, elems.toArray)
  })

  /** BaseTypeSeqs.scala:119 `baseTypeIndex`: a linear scan over the cached sequence. */
  def baseTypeIndex(tp: Type, clazz: Cls): Int = widenToClass(tp) match {
    case Some(c) =>
      val cs = bts(c).classes
      var i = 0
      while (i < cs.length) { inc("scalac.btsScan"); if (cs(i) eq clazz) return i; i += 1 }
      -1
    case None => -1
  }

  private def widenToClass(tp: Type): Option[Cls] = tp match {
    case ThisT(c)       => Some(c)
    case Ref(_, c, _)   => Some(c)
    case s: Single      => widenToClass(underlying(s))
    case _              => None
  }

  /** Types.scala:1435 `SingleType.underlying`, cached: `pre.memberType(sym)`. */
  def underlying(s: Single): Type = underlyingCache.getOrElseUpdate(s, {
    inc("scalac.underlyingComputed")
    if (s.pre eq Root) s.v.tpe else asSeenFrom(s.v.tpe, s.pre, s.v.owner)
  })

  /** Types.scala:2492 `TypeRef.baseType`: `relativize(sym.info.baseType(clazz))`; ThisType/SingleType
   *  delegate to their underlying type (Types.scala:167). */
  def baseType(tp: Type, clazz: Cls): Option[Ref] = {
    inc("scalac.baseType")
    tp match {
      case r @ Ref(_, c, _) =>
        if (c eq clazz) Some(r)
        else {
          val b = bts(c)
          val i = { val cs = b.classes; var j = 0; while (j < cs.length && !(cs(j) eq clazz)) { inc("scalac.btsScan"); j += 1 }; j }
          if (i >= b.classes.length) None else Some(relativize(r, b.elems(i)).asInstanceOf[Ref])
        }
      case ThisT(c)  => baseType(c.selfRef, clazz)
      case s: Single => baseType(underlying(s), clazz)
      case _         => None
    }
  }

  /** Types.scala:2447 `relativize`: asSeenFrom the TypeRef's prefix, then instantiate its type arguments. */
  def relativize(r: Ref, tp: Type): Type =
    if (isTrivial(tp)) tp
    else {
      inc("scalac.relativize")
      val seen = asSeenFrom(tp, r.pre, r.c.owner)
      instantiate(seen, r.c.tparams, r.args)
    }

  def instantiate(tp: Type, from: List[TParam], to: List[Type]): Type =
    if (from.isEmpty) tp
    else {
      val m = from.zip(to).toMap
      def go(t: Type): Type = { inc("scalac.substNodes"); t match {
        case TParamT(p)        => m.getOrElse(p, t)
        case Ref(pre, c, args) => Ref(go(pre), c, args.map(go))
        case Single(pre, v)    => Single(go(pre), v)
        case Fun(ps, r)        => Fun(ps.map(go), go(r))
        case other             => other
      }}
      go(tp)
    }

  /** Memoized in scalac (a flag on TypeRef/SingleType); here recomputed but not counted as work. */
  def isTrivial(t: Type): Boolean = t match {
    case ThisT(_) | TParamT(_) => false
    case Ref(pre, _, args)     => isTrivial(pre) && args.forall(isTrivial)
    case Single(pre, _)        => isTrivial(pre)
    case Fun(ps, r)            => ps.forall(isTrivial) && isTrivial(r)
    case _                     => true
  }

  private def skipPrefixOf(pre: Type, clazz: Cls) = (pre eq Root) || clazz == null

  /** Types.scala:677 `asSeenFrom`. */
  def asSeenFrom(tp: Type, pre: Type, clazz: Cls): Type = {
    inc("scalac.asSeenFrom")
    if (isTrivial(tp) || skipPrefixOf(pre, clazz)) tp
    else { inc("scalac.asSeenFromMaps"); new AsSeenFromMap(pre, clazz)(tp) }
  }

  /** TypeMaps.scala:417 */
  final class AsSeenFromMap(seenFromPrefix: Type, seenFromClass: Cls) {
    def apply(tp: Type): Type = {
      inc("scalac.nodes")
      tp match {
        case th: ThisT => thisTypeAsSeen(th)
        case s @ Single(pre, v) =>
          val pre1 = apply(pre)
          if (pre1 eq pre) s else Single(pre1, v)
        case tpt @ TParamT(p) if isTypeParamOfEnclosingClass(p) => classParameterAsSeen(tpt)
        case Ref(pre, c, args) =>
          val pre1 = apply(pre); val args1 = args.map(apply)
          if ((pre1 eq pre) && args1.lazyZip(args).forall(_ eq _)) tp else Ref(pre1, c, args1)
        case Fun(ps, r) => Fun(ps.map(apply), apply(r))
        case other => other
      }
    }

    // TypeMaps.scala:456 isBaseClassOfEnclosingClass: `encl isSubClass base` is a BTS index scan.
    private def isTypeParamOfEnclosingClass(p: TParam): Boolean = {
      var encl = seenFromClass
      while (encl != null) {
        inc("scalac.enclScan")
        if (baseTypeIndex(ThisT(encl), p.owner) >= 0) return true
        encl = encl.owner
      }
      false
    }

    // TypeMaps.scala:577
    private def matchesPrefixAndClass(pre: Type, clazz: Cls)(candidate: Cls) =
      (clazz eq candidate) && baseTypeIndex(pre, clazz) != -1

    private def prefixOf(o: Option[Ref]): Type = o.fold(Root: Type)(_.pre)

    // TypeMaps.scala:636
    private def thisTypeAsSeen(tp: ThisT): Type = {
      @annotation.tailrec def loop(pre: Type, clazz: Cls): Type = {
        inc("scalac.thisSteps")
        if (skipPrefixOf(pre, clazz)) tp
        else if (!matchesPrefixAndClass(pre, clazz)(tp.c)) loop(prefixOf(baseType(pre, clazz)), clazz.owner)
        else pre // stable prefixes only in this toy (no captureThis)
      }
      loop(seenFromPrefix, seenFromClass)
    }

    // TypeMaps.scala:554
    private def classParameterAsSeen(tp: TParamT): Type = {
      val owner = tp.p.owner
      @annotation.tailrec def loop(pre: Type, clazz: Cls): Type = {
        inc("scalac.tparamSteps")
        if (skipPrefixOf(pre, clazz)) tp
        else if (!matchesPrefixAndClass(pre, clazz)(owner)) loop(prefixOf(baseType(pre, clazz)), clazz.owner)
        else baseType(pre, clazz) match {
          case Some(Ref(_, _, args)) => args(owner.tparams.indexOf(tp.p))
          case None                  => tp
        }
      }
      loop(seenFromPrefix, seenFromClass)
    }
  }

  /** Types.scala:706 `memberInfo`: `sym.info.asSeenFrom(this, sym.owner)`. */
  def memberInfo(pre: Type, m: Val): Type = asSeenFrom(m.tpe, pre, m.owner)
}
