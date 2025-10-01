import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Group
import Mathlib.Tactic
import Mathlib.GroupTheory.Sylow
--------------------------------------------------------------------------------------------
--group9.1.3 subgroup
--------------------------------------------------------------------------------------------
--Type : 데이테들의 타입
---Type0 : 증명가능한 명제 들, 가장 낮은 레벨의 우주
---Type1 : 일반적인 데이터 타입, Nat, Int, Rat, Real 등등
---Type2 : Type1의 집합, Type3 : Type2의 집합, ...
---Type* : Type0, Type1, Type2, ... 모두 포함하는 타입 : lean이 알아서 적절한 레벨의 타입 추론

--괄호의 종류 : (), {}, []
---() : 명시적 인자 : 반드시 넣어야하는 인자 : 변수나 가정 선언
---{} : 암시적 인자 : 넣어도 되고 안넣어도 되는 인자 : lean이 알아서 추론
---[] : typeclass 인자자 : 타입의 구조나 성질을 만족 : 예를들어 Group, Ring, Field 등등

--example 작성 순서
---재사용할 중요한 정리는 theoream+이름 , 한번만 쓸 간단한 증명은 example
---{}선언 : 일반적인 타입 선언 (암무적 인자로 굳이 선언하지 않ㄴ아도 됨)
---[]선언 : typeclass 선언 (Group, Ring, Field 등등)
---( )선언 : 변수나 가정 선언 (반드시 넣어야하는 인자)
---: : 콜론 뒤 증명하고 싶은 결론 작성
---:= : 등호 뒤 증명 작성
example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) : x * y ∈ H := --곱셈에 닫혀있다./ := by 는 증명도구 사용할때/ :=는 증명 식 바로 제시할때
  H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) : x⁻¹ ∈ H := -- 역원원
  H.inv_mem hx
-- ℤ 는 ℚ의 덧셈 부분군 : 증명 위해 AddSubgroup ℚ 의 instance를 만들어야함 즉, ℚ 로 사영 했을때 ℤ 가 되어야 함. (상이 ℤ 가 되어야 함함)
example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)  --carrier: 부분군을 구성하는 실제 원소 지정 / (↑): 형 변환 즉 3을 3/1로 바꿈
  add_mem' := by --덧셈 닫힘
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩ --rfl 반사성 : 증명할 목표가 정의상 명백히 같을 때 (정의에 의해 전개 했을때 완전히 같은 형태로 판단될 때)
    use n + m
    simp -- (n : ℚ) + (m : ℚ)가 정의상 ((n + m) : ℚ)와 같다는 것을 자동으로 계산 :
  zero_mem' := by --항등원 존재재
    use 0
    simp
  neg_mem' := by -- 역원 존재
    rintro _ ⟨n, rfl⟩
    use -n
    simp
   --simp: 미리 등록된 정리(lemma)들과 현재 증명의 가정(hypothesis)들을 이용해 목표(goal)나 다른 가정들을 최대한 간단하게 만드는 것
    --simp [*] : * 안에 있는 모든 가정들을 사용해서 간단하게 만들어라
    --simp only [h₁, h₂, ...] : h₁, h₂, ... 만 사용해서 간단하게 만들어라
    --simp [-id₁, ...] : id₁ 만 사용하지 말고 나머지 가정들로 간단하게 만들어라
    --simp at h₁ h₂ ... : h₁, h₂ ... 에 있는 가정들을 간단하게 만들어라
    --simp at *: 기본 규칙으로 모든 가정과 결과를 간단하게 만들어라
    --simp [*] at * : * 안에 있는 모든 가정들을 사용해서 모든 가정과 결과를 간단하게 만들어라

  example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance --Type *을 이용해 H가 Group임을 추론가능
  --instance : 어떤 타입이 특정한 구조를 가지고 있음을 Lean에게 알려주는 방법 : mathlib에 미리 정의된 코드
  ---instance 덕분에 H 가 부분군이라고 선언하기만 하면 그뒤부터 H를 하나의 그룹으로 처리함 : H가 부분군이라는 사실만으로 H가 그룹임을 자동으로 알아챌 수 있었던 이유
  ---inferinstnace : 여기에서 필요한 타입클래스 인스턴스 찾기  : 자동 인스턴스 검색 / 오류해결 (인스턴스 합성하는데 실패 했다는 오류)

  example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance
 --전체 그룹 G의 원소 x 중에서, x가 부분군 H에 속한다는 조건을 만족하는 원소들만 모아서 만든 새로운 타입 :{} (부분타입 정의) : //~ (~을 만족하는)
 --subgroup 이라는 서술대신 타입을 사용하면 추가적인 구조 쉽게 부여 가능 (서술 대신 격자 연산등 다양한 연산 사용하여 다루기 편함)
  example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := --부분집합의 하한(포함관계에 의한)은 부분집합이고 이는 부분집합의 교집합과 같다
    rfl --정의 그자체 : 군의 정의

  example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by --subgroup.closure부분집합의 상합은 일반적으로 부분군이 아님 : 따라서 합집합에 의해 생성되는 부분군 설정
  rw [Subgroup.sup_eq_closure]

--G자체가 subgroup G의 타입을 갖지 않음 : Subgroup G 의 타입을 갖기 위해서는 G의 모든 원소가 Subgroup G 속해야 가능능 : 격자 구조 제공 : ⊤ 모든원소소
  example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) :=
  trivial
--G에서 격자구조의 최하위 부분군에 속한다 : 그 원소가 항등원 뿐이다. :⊥최하위 원소
  example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 :=
  Subgroup.mem_bot

  def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where --켤례부분군
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹} -- ∧  (~이고) : xHx⁻¹ 정의
  one_mem' := by --항등원
    dsimp --simp와 다르게 정의만 이용하는 수행
    sorry
  inv_mem' := by --역원
    dsimp
    sorry
  mul_mem' := by --곱셈 닫혀 있다.
    dsimp
    sorry
--map : (push forward/ 순상) ={f(h)|h∈ H }
--comap (pull back/durtkd)={g:G|f(g)∈ L}
example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) : --kernel
    g ∈ MonoidHom.ker f ↔ f g = 1 := --f(g)=1 인 g의 집합
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) : --f의 치역
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h := --f(g)=h인 g가 존재하는 h
  f.mem_range
-----------------------------------------------------------------excercise
section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup
--intro : 가정을 언급
--rintro : 가정을 분해해서 언급
--h : P ∧ Q 일때:  intro h: 가정 h 박스채로 사용 / rintro <hP, hQ> : 가정에서 P와 Q 분해 해서 고려하기 가능

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  rintro g hg --간단한 가정일때 <> 안씀 : g가 존재해서 g=φ(x)인 g 존재 : 가정 만족하는 g 존재
  exact hST hg --hST에 의해 hg가 T의 원소

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  rintro y ⟨x, hxS, rfl⟩ -- y가 존재해서 x는 S에 속하고 φ(x)=y를 만족함함
  let hxT := hST hxS -- x는 S에 속하고 hST에 의해 x는 T에 속한다.
  use x
  exact ⟨hxT, rfl⟩ --x ∈ T 이므로, y는 map φ T의 원소

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  -- 두 부분군이 같음을 보이려면, 두 부분군에 속한 원소가 같음을 보이면 된다.
  -- `ext` tactic은 이 목표를 `∀ x, x ∈ 좌변 ↔ x ∈ 우변` 으로 바꿔준다.
  ext x
  -- simp tactic은 comap과 comp의 정의를 자동으로 펼쳐서 증명한다.
  -- 좌변: x ∈ comap (ψ.comp φ) U  ↔ (ψ ∘ φ) x ∈ U ↔ ψ (φ x) ∈ U
  -- 우변: x ∈ comap φ (comap ψ U) ↔ φ x ∈ (comap ψ U) ↔ ψ (φ x) ∈ U
  -- 양변이 정의상 동일하므로 simp가 증명을 완료한다.
  simp [Subgroup.comap]

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : map (ψ.comp φ) S = map ψ (S.map φ) := by
  -- 3번 예제와 마찬가지로 `ext` tactic으로 시작한다.
  ext y
  -- simp tactic이 map과 comp의 정의를 펼쳐서 증명한다.
  -- 좌변: y ∈ map (ψ.comp φ) S ↔ ∃ x ∈ S, (ψ ∘ φ) x = y ↔ ∃ x ∈ S, ψ (φ x) = y
  -- 우변: y ∈ map ψ (S.map φ)   ↔ ∃ z ∈ S.map φ, ψ z = y
  -- z ∈ S.map φ는 다시 ∃ x ∈ S, φ x = z 를 의미하므로,
  -- 정리하면 ∃ x ∈ S, ψ (φ x) = y 가 되어 좌변과 동일하다.
  simp [Subgroup.map, MonoidHom.comp_apply]

end exercises
open scoped Classical

example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

open Subgroup

example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd --import Mathlib.GroupTheory.Sylow 필요

lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  sorry

#check card_dvd_of_le

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
  sorry
