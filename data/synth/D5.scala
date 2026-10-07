package d5

trait O1 {
  class C1
  val v2: O2
  trait O2 {
    class C2
    val v3: O3
    trait O3 {
      class C3
      val v4: O4
      trait O4 {
        class C4
        val v5: O5
        trait O5 {
          class C5
          trait B4[A4] { def m: (O1.this.C1, O2.this.C2, O3.this.C3, O4.this.C4, O5.this.C5, A4) }
          trait B3[A3] extends B4[A3]
          trait B2[A2] extends B3[A2]
          trait B1[A1] extends B2[A1]
          val x: B1[Int]
        }
      }
    }
  }
}
object Top { val v1: O1 = null }
object Use {
  val r0 = Top.v1.v2.v3.v4.v5.x.m
  val r1 = Top.v1.v2.v3.v4.v5.x.m
  val r2 = Top.v1.v2.v3.v4.v5.x.m
  val r3 = Top.v1.v2.v3.v4.v5.x.m
  val r4 = Top.v1.v2.v3.v4.v5.x.m
  val r5 = Top.v1.v2.v3.v4.v5.x.m
  val r6 = Top.v1.v2.v3.v4.v5.x.m
  val r7 = Top.v1.v2.v3.v4.v5.x.m
  val r8 = Top.v1.v2.v3.v4.v5.x.m
  val r9 = Top.v1.v2.v3.v4.v5.x.m
  val r10 = Top.v1.v2.v3.v4.v5.x.m
  val r11 = Top.v1.v2.v3.v4.v5.x.m
  val r12 = Top.v1.v2.v3.v4.v5.x.m
  val r13 = Top.v1.v2.v3.v4.v5.x.m
  val r14 = Top.v1.v2.v3.v4.v5.x.m
  val r15 = Top.v1.v2.v3.v4.v5.x.m
  val r16 = Top.v1.v2.v3.v4.v5.x.m
  val r17 = Top.v1.v2.v3.v4.v5.x.m
  val r18 = Top.v1.v2.v3.v4.v5.x.m
  val r19 = Top.v1.v2.v3.v4.v5.x.m
  val chk: (Top.v1.C1, Top.v1.v2.C2, Top.v1.v2.v3.C3, Top.v1.v2.v3.v4.C4, Top.v1.v2.v3.v4.v5.C5, Int) = r0
  val bad: Int = r0
}
