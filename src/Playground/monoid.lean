import Mathlib.Tactic

namespace Playground.monoid

structure A where
  a : Int
  b : Int
  c : Int

instance A_mul : Mul A :=
  ⟨fun x y => A.mk (x.a+y.a) (x.b+y.b+x.a*y.c) (x.c+y.c)⟩

def A_assoc : ∀ x y z : A, (x * y) * z = x * (y * z) := by
  intros x y z
  cases x with | mk xa xb xc =>
  cases y with | mk ya yb yc =>
  cases z with | mk za zb zc =>
  simp only [HMul.hMul, Mul.mul]
  congr 1
  · ring
  · simp; ring
  · ring

instance A_monoid : Monoid A where
  mul := (· * ·)
  mul_assoc := A_assoc
  one := A.mk 0 0 0
  one_mul := by
    intro x
    cases x with | mk xa xb xc =>
    show (A.mk 0 0 0 * A.mk xa xb xc) = A.mk xa xb xc
    simp only [HMul.hMul, Mul.mul]
    simp
  mul_one := by
    intro x
    cases x with | mk xa xb xc =>
    show (A.mk xa xb xc * A.mk 0 0 0) = A.mk xa xb xc
    simp only [HMul.hMul, Mul.mul]
    simp

end Playground.monoid
