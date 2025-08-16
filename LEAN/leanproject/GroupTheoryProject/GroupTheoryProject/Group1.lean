import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group
example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x
example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y
example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
  f.map_mul x y
example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
  f.map_zero
example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
  (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f
example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x
example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by group
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z -x) = y := by
  rw [add_sub_cancel]
--lean 4에서는 abel 전략 없음. lean 3에만 존재 : lean4는 직접 계산이 필요
example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  rw [add_assoc, add_assoc]
  rw [← add_assoc]
  rw [add_comm z x]
  rw [add_assoc]
  rw [add_assoc z y (-z)]
  rw [add_neg_cancel_left]
  rw [add_neg_cancel_right]
