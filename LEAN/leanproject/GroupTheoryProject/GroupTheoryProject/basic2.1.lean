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
  exact h --h가 목표와 같으므로 exact h

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
