import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
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

variable(a b c:ℝ)
#check a
#check a+b
#check mul_comm a b
#check mul_assoc c a b
#check mul_comm a

example (a b c : ℝ ) :
