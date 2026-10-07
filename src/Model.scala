package asftoy

import scala.collection.mutable

/** A toy Scala-like type language, just rich enough to exercise asSeenFrom:
 *  this-types, class type parameters, class types with a prefix, singleton paths, and an
 *  opaque internal node (`Fun`) standing for "the rest of a type". */
sealed trait Type
/** `c.this` */
final case class ThisT(c: Cls) extends Type
/** A class type parameter `p` (owned by `p.owner`). */
final case class TParamT(p: TParam) extends Type
/** A trivial leaf (`Int`, a top-level class, ...). */
final case class Const(name: String) extends Type
/** `pre#c[args]`: a class type whose prefix is `pre` (`c.owner.this` for a member class seen from inside). */
final case class Ref(pre: Type, c: Cls, args: List[Type]) extends Type
/** `pre.v.type`: a stable path. */
final case class Single(pre: Type, v: Val) extends Type
/** An internal node standing for the non-path structure of a type (function, method, tuple...). */
final case class Fun(params: List[Type], res: Type) extends Type

object Root extends Type { override def toString = "<root>" }

final class TParam(val name: String) {
  var owner: Cls = null
  override def toString = name
}

final class Val(val name: String, val owner: Cls, tpe0: => Type) {
  lazy val tpe: Type = tpe0 // declared type, in `owner`'s view
  override def toString = s"$owner.$name"
}

/** A class/trait. `owner == null` means top level (prefix `Root`). `parents` are written in this class's
 *  own view: they mention `ThisT(owner chain)` and `TParamT(tparams)`. */
final class Cls(val name: String, val owner: Cls, val tparams: List[TParam]) {
  tparams.foreach(_.owner = this)
  var parents: List[Ref] = Nil
  override def toString = name

  def thisPrefix: Type = if (owner == null) Root else ThisT(owner)
  /** The type of `C.this` widened: `Owner.this#C[T1..Tn]`. */
  def selfRef: Ref = Ref(thisPrefix, this, tparams.map(TParamT(_)))

  /** Owner chain, innermost first. */
  def ownerChain: List[Cls] = Iterator.iterate(this)(_.owner).takeWhile(_ != null).toList

  // ---- linearization, cached once per class (both designs cache the class-level hierarchy:
  //      scalac in `baseTypeSeq`, IntelliJ in `superPathsDeep` / `MixinNodes.SuperTypesData`).
  lazy val linearization: List[Cls] = (this :: parents.flatMap(_.c.linearization)).distinct
  lazy val superSet: Set[Cls] = linearization.toSet
  def isSubClass(that: Cls): Boolean = superSet.contains(that)
}

/** Counters shared by both designs. Keys are strings so the report can print whatever was touched. */
object Counters {
  private val m = mutable.LinkedHashMap[String, Long]()
  var enabled = true
  inline def inc(k: String, by: Long = 1): Unit = if (enabled) m.update(k, m.getOrElse(k, 0L) + by)
  def get(k: String): Long = m.getOrElse(k, 0L)
  def reset(): Unit = m.clear()
  def snapshot: Map[String, Long] = m.toMap
}

object Types {
  def size(t: Type): Int = t match {
    case Ref(pre, _, args) => 1 + size(pre) + args.map(size).sum
    case Single(pre, _)    => 1 + size(pre)
    case Fun(ps, r)        => 1 + ps.map(size).sum + size(r)
    case _                 => 1
  }
  def show(t: Type): String = t match {
    case ThisT(c)          => s"$c.this"
    case TParamT(p)        => p.name
    case Const(n)          => n
    case Root              => "_root_"
    case Ref(Root, c, as)  => c.name + (if (as.isEmpty) "" else as.map(show).mkString("[", ",", "]"))
    case Ref(p, c, as)     => show(p) + "#" + c.name + (if (as.isEmpty) "" else as.map(show).mkString("[", ",", "]"))
    case Single(Root, v)   => v.name + ".type"
    case Single(p, v)      => showPath(p) + "." + v.name + ".type"
    case Fun(ps, r)        => ps.map(show).mkString("(", ",", ")") + "=>" + show(r)
  }
  private def showPath(t: Type): String = t match {
    case Single(Root, v) => v.name
    case Single(p, v)    => showPath(p) + "." + v.name
    case ThisT(c)        => s"$c.this"
    case other           => show(other)
  }
}
