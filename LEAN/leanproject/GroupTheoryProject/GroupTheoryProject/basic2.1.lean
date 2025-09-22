import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
open Real

example (a b c : ℝ) : a * b * c = b * (a * c) := by -- 실수 나타내고 싶다면 \R 로 써야 나타남
rw [mul_comm a b] -- 결합법칙 REWRITE 전술 (다시쓰기)
rw [mul_assoc b a c] -- 교환법칙 REWRITE 전술 (다시쓰기)

example (a b c : ℝ ) : a*b*c=b*c*a := by
rw [mul_assoc] --결합법칙 (b*c)
rw [mul_comm] --교환 법칙

example (a b c :ℝ) : a*b*c=b*c*a := by
rw[mul_assoc]
rw[mul_comm a] --a*? 을 ?*a 로 교환법칙

example (a b c : ℝ) : a*(b*c)=b*(c*a):= by
rw[mul_comm a]
rw[mul_assoc]

example (a b c d e f :ℝ)(h : a*b=c*d)(h':e=f) :a *(b * e)=c*(d*f):= by --example(변수지정: 변수집합)(가정1 : 조건을 쓰시오)(가정 2 : 조건을 쓰시오) : 밝히고 싶은 결론 : = by
rw[h'] --가정 h'이용
rw[←mul_assoc] -- 앞에 있는 두개의 문자에 결합법칙 적용
rw[h] --가정 h 이용
rw[mul_assoc] --이후 뒤쪽 두개의 문자에 결합법칙 적용

example (a b c d e f :ℝ)(h : a*b=c*d)(h':e=f) :a *(b * e)=c*(d*f):= by --example(변수지정: 변수집합)(가정1 : 조건을 쓰시오)(가정 2 : 조건을 쓰시오) : 밝히고 싶은 결론 : = by
rw[h', ← mul_assoc, h, mul_assoc] --이렇게 한번애 쓰기도 가능 !

example(a b c d e f : ℝ)(h : b*c = e*f):a*b*c*d = a*e*f*d:= by -- 차례대로 결합법칙 되어있는 꼴 ((a*b)*c)*d 라고 되어있음
rw[mul_assoc a]
rw[h]
rw[← mul_assoc]

example(a b c d :ℝ)(hyp : c=b*a-d)(hyp':d=a*b):c=0 := by
rw[hyp]
rw[hyp']
rw[mul_comm]
rw[sub_self] --동일한 항의 차 는 0이다

variable(a b cb d e f :ℝ) --이렇게 변수만 따로 지정하고
example(h:a*b=c*d)(h' :e=f): a*(b*e)=c*(d*f):= by --바로 (조건)으로 형성 해도 가능
rw[h', ← mul_assoc, h, mul_assoc]

variable(a b c:ℝ) -- check는 어떤 식인지 확인하는거
#check a
#check a+b
#check mul_comm a b
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check mul_add
#check add_mul

example : (a+b)*(a+b)= a*a + 2*(a*b)+b*b:= by
rw [add_mul, mul_add, mul_add] --분배법칙 앞에서 곱, 뒤에서 곱
rw [← add_assoc, add_assoc (a * a)] --
rw [mul_comm b a, ← two_mul] -- 2ab 에서

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc --과정식 까지 노트에 쓰듯이 보여주는 방법
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry -- 명확한 증명 없이 넘어가는 방법 (나중에 사용 할 수 있음음)
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp --hyp 에서 hyp' 사용
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp --exact : 골과 ~이 같다 : 전술

example : c * b * a = b * (a * c) := by
ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
ring --환의 공리 이용해서 증명하는 방법

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h] -- nth_rw : n번째 rewite 할껀지 표현 (h 사용해 2번째 골 rewite)
  rw [add_mul]

--------------------------------------------------------------
--basic2.2
variable (R : Type*) [Ring R]
example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
#check add_zero

namespace myring
theorem add_zero (a : ℝ) : a + 0 = a := by ring
theorem add_comm (a b : ℝ) : a + b = b + a := by ring
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry
theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
end myring

#check myring.add_comm a b
#check myring.add_zero a

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

theorem self_sub (a : R) : a - a = 0 := by
  sorry

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  sorry

variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry

--------------------------------------------------------------
--basic2.3
#check (le_refl : ∀ a : ℝ, a ≤ a) --le_refl(반사성) : 모든 실수 a에 대해서 a는 a보다 작거나 같다 확인하기
#check (le_trans : a ≤ b → b ≤ c → a ≤ c) --le_trans(추이성) : a가 b보다 작거나 같고, b가 c보다 작거나 같으면 a는 c보다 작거나 같다 확인하기

variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c) -- a≤b 대신에 h 사용
#check (le_trans h h' : a ≤ c) -- a≤b 대신에 h, b≤c 대신에 h' 사용

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans --apply 는 일반적 명제 또는 증명 가져와 현재 목표와 일치키시려는 전술
  · apply h₀ --들여써서 le_trans 가 구체적으로 어떤 가정으로 하위 목표를 도달하는지 설명
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀ -- apply gkrh 바로 쓰기 가능
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁ --le_trans는 h0 와 h1을 활용해 새로운 증명 만들어냄 (apply 없어도 가능)

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
le_refl x --x의 문자에 대하여 le_refl 적용

#check (le_refl : ∀ a, a ≤ a) --반사성
#check (le_trans : a ≤ b → b ≤ c → a ≤ c) --추이성
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c) --a가 b보다 작거나 같고, b가 c보다 작으면 a는 c보다 작다
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c) --a가 b보다 작고, b가 c보다 작거나 같으면 a는 c보다 작다
#check (lt_trans : a < b → b < c → a < c) --a가 b보다 작고, b가 c보다 작으면 a는 c보다 작다

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by --추이성 3번 쓰기
sorry

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith -- linarith : 선형부등식 전술 : 덧셈 뺄셈 상수곱셈이루어진 등식, 부등식 자동 증명 : lean이 알아서 모든 가설 분석해 조합하여 증명함


example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith -- linarith 은 등식도 이용 가능 : 선형 산술 규칙 종합적 처리 가능

--실수 부등식을 증명하는데 사용 할 수 있는 정리들
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b) --동치 \iff 로 나타낼 수 있음
#check (exp_lt_exp : exp a < exp b ↔ a < b)--동치
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left

example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp] --목표가 a ≤ b 로 바뀜
  apply h

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀ --h_0 적용 : 첫번째 골
    apply exp_lt_exp.mpr h₁ --동치명제 적용할때 mpr : ↔ 의 오른쪽에서 왼쪽으로 증명 : 두번째 골
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num --norm_num : 구체적 계산 전술

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry --have는 중간에 필요한 새로운 보조정리 또는 사실을 도입하고 증명하는 역할 : have [이름] : [명제] : = by
  apply log_le_log h₀
  sorry

example : 0 ≤ a ^ 2 := by
--apply ? : 어떤 전술을 써야할지 모를때 물음표 붙여서 힌트 얻기 (infoview에 나타남)
exact sq_nonneg a

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2*a*b = 2*a*b + 0 := by ring
    _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
    _ = a^2 + b^2 := by ring

example : 2*a*b ≤ a^2 + b^2 := by
  have h : 0 ≤ a^2 - 2*a*b + b^2
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

example : |a*b| ≤ (a^2 + b^2)/2 := by
  sorry

#check abs_le'.mpr

------------------------------------------------------------------------
--bssic2.4

-----------------------------------------------------------------------------
--basic2.5
variable {α : Type*} [PartialOrder α] -- 부분 순서 (?)
--일반적인 대수적 구조 는 R , G 와 같은 문자를 사용하지만, 그리스 문자는 특별한 구조가 ℝ Γ
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x) --부분순서 반사적
#check (le_trans : x ≤ y → y ≤ z → x ≤ z) --부분순서 교환
#check (le_antisymm : x ≤ y → y ≤ x → x = y) -- 부분 순서 반대칭

#check x < y
#check (lt_irrefl x : ¬ (x < x)) --비반사적 (어떤 원소도 자기자신보다 작을 수 없다.)
#check (lt_trans : x < y → y < z → x < z) --추이적적
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z) --부등식+등호 섞어 쓰기
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z) --

example : x < y ↔ x ≤ y ∧ x ≠ y := -- 필충 조건 증명
  lt_iff_le_and_ne

--inf, sup 설정 : \g l b (하한한) \l u b (상한)
variable {α : Type*} [Lattice α] -- latice :격자 구조 : 정수 구조
variable (x y z : α)
-- 상한과 하한의 활용 (격자의 예시)
-- 정수 같은 경우는 전 순서이기 때문에 inf, sup 이 항상 존재, min max 도 항상 존재
-- 부분집합에서는 포함 관계 또는 교집합 합집합으로 표현 가능
-- x가 거짓이거나 y가 참인경우 순서관계를 설정하고 진리값에서의 논리곱, 논리합 이용 가능
-- 약수관계를 갖는 자연수에서 최대공약수, 최소공배수
-- 벡터의 선형 부분공간에서 최대 하한은 공간의 교집합, 최소 상한은 공간의 합집합
#check x ⊓ y --최대 하한 greatest lower bound (infimum)
#check (inf_le_left : x ⊓ y ≤ x) --하한 은 x 보다 작거나 같다. (부등호는 전 순서 최소, 최대)
#check (inf_le_right : x ⊓ y ≤ y)  --하한 은 y 보다 작거나 같다. (부등호는 전 순서 최소, 최대)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y --최소 상한 least upper bound (supremum)
#check (le_sup_left : x ≤ x ⊔ y) -- 상한은 x 보다 크거나 같다.
#check (le_sup_right : y ≤ x ⊔ y) --상한은 y 보다 크거나 같다.
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by --inf 교환법칙
  -- le_antisymm 정리를 사용합니다. (A = B 를 증명하려면 A ≤ B 와 B ≤ A 를 증명하면 됩니다.)
  apply le_antisymm
  -- 1. x ⊓ y ≤ y ⊓ x 증명
  apply le_inf
  apply inf_le_right
  apply inf_le_left
  -- 2. y ⊓ x ≤ x ⊓ y 증명 (위와 동일한 논리)
  apply le_inf
  apply inf_le_right
  apply inf_le_left
example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by -- inf 결합법칙
  apply le_antisymm
  -- 1. x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z) 증명
  -- x ⊓ y ⊓ z ≤ x, x ⊓ y ⊓ z ≤ (y ⊓ z)
  apply le_inf --x ⊓ y ⊓ z ≤ x
  trans x ⊓ y -- trans는 추이적 증명을 도와줍니다 : x ⊓ y ⊓ z  ≤ x ⊓ y ≤ x
  apply inf_le_left -- x ⊓ y ⊓ z  ≤ x ⊓ y
  apply inf_le_left -- x ⊓ y ≤ x
  apply le_inf  --x ⊓ y ⊓ z ≤ (y ⊓ z)
  trans x ⊓ y --: x ⊓ y ⊓ z  ≤ x ⊓ y ≤ y, x ⊓ y ⊓ z  ≤ z
  apply inf_le_left -- x ⊓ y ⊓ z ≤ x ⊓ y
  apply inf_le_right -- x ⊓ y ≤ y
  apply inf_le_right --  x ⊓ y ⊓ z ≤ z
  apply le_inf
  -- 2. x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z 증명 (위와 유사)
  --x ⊓ (y ⊓ z) ≤ x ⊓ y , x ⊓ (y ⊓ z) ≤ z
  apply le_inf --x ⊓ (y ⊓ z) ≤ x ⊓ y
  apply inf_le_left -- x ⊓ (y ⊓ z) ≤ x
  trans y ⊓ z --x ⊓ (y ⊓ z) ≤ y ⊓ z ≤ y
  apply inf_le_right -- x ⊓ (y ⊓ z) ≤ y ⊓ z
  apply inf_le_left -- y ⊓ z ≤ y
  trans y ⊓ z --x ⊓ (y ⊓ z) ≤ y ⊓ z ≤ z
  apply inf_le_right  -- x ⊓ (y ⊓ z) ≤ y ⊓ z
  apply inf_le_right -- y ⊓ z ≤ z

example : x ⊔ y = y ⊔ x := by -- sup 교환법칙
  apply le_antisymm
  -- 1. x ⊔ y ≤ y ⊔ x 증명
  apply sup_le
  apply le_sup_right
  apply le_sup_left
  -- 2. y ⊔ x ≤ x ⊔ y 증명 (위와 동일한 논리)
  apply sup_le
  apply le_sup_right
  apply le_sup_left
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by --sup 결합법칙
  apply le_antisymm
   -- 1. (x ⊔ y) ⊔ z ≤ x ⊔ (y ⊔ z) 증명
  apply sup_le --x ⊔ y ≤ x ⊔ (y ⊔ z), z ≤ x ⊔ (y ⊔ z)

  apply sup_le --x ⊔ y ≤ x ⊔ (y ⊔ z)
  apply le_sup_left --x ≤ x ⊔ (y ⊔ z)
  trans y ⊔ z --y ≤ y ⊔ z ≤ x ⊔ (y ⊔ z)
  apply le_sup_left -- y ≤ y ⊔ z
  apply le_sup_right -- y ⊔ z ≤ x ⊔ (y ⊔ z)
  trans y ⊔ z -- z ≤ y ⊔ z ≤ x ⊔ (y ⊔ z)
  apply le_sup_right -- z ≤ y ⊔ z
  apply le_sup_right --y ⊔ z ≤ x ⊔ (y ⊔ z)
  -- 2.  x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z 증명
  apply sup_le --x ≤ (x ⊔ y) ⊔ z, y ⊔ z ≤ (x ⊔ y) ⊔ z

  trans x ⊔ y --x ≤ (x ⊔ y) ≤ (x ⊔ y) ⊔ z
  apply le_sup_left --(x ⊔ y) ≤ (x ⊔ y) ⊔ z
  apply le_sup_left -- x ≤ (x ⊔ y)

  apply sup_le -- y ⊔ z ≤ (x ⊔ y) ⊔ z
  trans x ⊔ y --y ≤ x ⊔ y ≤ (x ⊔ y) ⊔ z
  apply le_sup_right -- y ≤ x ⊔ y
  apply le_sup_left -- x ⊔ y ≤ (x ⊔ y) ⊔ z
  apply le_sup_right -- z ≤ (x ⊔ y) ⊔ z

theorem absorb1 : x ⊓ (x ⊔ y) = x := by --흡수 법칙?
  apply le_antisymm
  -- 1. x ⊓ (x ⊔ y) ≤ x 증명: infimum의 정의(inf_le_left)에 의해 항상 참입니다.
  apply inf_le_left
  -- 2. x ≤ x ⊓ (x ⊔ y) 증명: le_inf를 사용합니다.
  apply le_inf
  apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by --항상 \glb 부터 연산 한다
  apply le_antisymm
  -- 1. x ⊔ (x ⊓ y) ≤ x 증명: sup_le를 사용합니다.
  apply sup_le
  apply le_refl
  apply inf_le_left
  -- 2. x ≤ x ⊔ (x ⊓ y) 증명: supremum의 정의(le_sup_left)에 의해 항상 참입니다.
  apply le_sup_left

variable {α : Type*} [DistribLattice α] --분배격자 (수학적 구조 결합)
--x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z 와 x⊔(y⊓z)=(x⊔y)⊓(x⊔z) 가 성립하는 격자
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) --왼쪽 분배 법칙
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z) --오른쪽 분배 법칙
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) --왼쪽 분배
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z)) --오른쪽 분배

variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry --복잡함

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry --복잡함
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R] --엄격 순서 환
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b) --부등식 양변에 같은 수 더하기
#check (mul_pos : 0 < a → 0 < b → 0 < a * b) --두 양수 곱하면 양수
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  -- add_le_add_left 정리의 특수한 형태
  -- a ≤ b의 양변에 -a를 더하면, -a + a ≤ -a + b
  -- 0 ≤ b - a 와 같습니다.
  -- 이 과정은 linarith가 자동으로 처리해 줍니다.
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  -- 위와 반대 과정입니다.
  -- 0 ≤ b - a의 양변에 a를 더하면, a + 0 ≤ a + (b - a)
  -- a ≤ b 와 같습니다.
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
-- 1. 이전 예제로부터 a ≤ b가 0 ≤ b - a 와 동치임을 이용합니다.
  have h_sub : 0 ≤ b - a := by sorry
  -- 2. 'mul_nonneg' 정리에 의해, 음수가 아닌 두 수(b-a와 c)의 곱은 음수가 아닙니다.
  have h_mul_nonneg : 0 ≤ (b - a) * c := mul_nonneg h_sub h'
  -- 3. 분배법칙(right_distrib)을 사용하여 괄호를 전개합니다.
  rw [sub_mul] at h_mul_nonneg
  -- 4. 이제 목표는 0 ≤ b * c - a * c 이고, 이것은 a * c ≤ b * c 와 동치입니다.
  sorry

variable {X : Type*} [MetricSpace X] --Metricspece : 거리 공간 성질 가짐
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x) --대칭성
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z) --삼각부등식

example (x y : X) : 0 ≤ dist x y := by
  -- 1. 삼각 부등식 'dist x z ≤ dist x y + dist y z' 에서 z를 x로 특수화한 'dist x x ≤ dist x y + dist y x' 라는 사실을 'h'로 가져옴.
  have h : dist x x ≤ dist x y + dist y x := dist_triangle x y x
  -- 2. 'dist_self' (dist x x = 0) 와 'dist_comm' (dist y x = dist x y) 정리를 이용하여 'h'를 다시 씁니다(rewrite).
  rw [dist_self, dist_comm y x] at h
  -- 3. rw가 끝나면 'h'는 '0 ≤ dist x y + dist x y'가 됨. 어떤 값의 2배가 0보다 크거나 같다면, 원래 값도 0보다 크거나 같아야 합니다.
-- linarith 전술이 이 마지막 단계를 자동으로 해결해 줍니다.
  linarith
