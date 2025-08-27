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

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring


example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
