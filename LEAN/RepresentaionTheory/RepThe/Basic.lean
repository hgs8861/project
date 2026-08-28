-- Basic.lean

import Mathlib  -- Mathlib 전체를 불러옴

namespace RepresentationTheory  -- 이름 충돌 방지를 위한 namespace 선언

variable (G : Type*) [Group G]
-- G : 임의의 타입, [Group G] 로 군 구조 부여
-- Type* 의 * 는 universe polymorphism (크기에 상관없이 작동)

variable (V : Type*) [AddCommGroup V] [Module ℂ V]
-- V : 임의의 타입
-- [AddCommGroup V] : V 에 가환군 구조 부여
-- [Module ℂ V] : V 에 ℂ-벡터공간 구조 부여

-- Definition 1.2.1: 군 표현
-- ρ : G → GL(V), 즉 G에서 V의 ℂ-선형 자기사상들의 군으로의 준동형
abbrev GroupRep (G : Type*) [Group G] (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  G →* (V →ₗ[ℂ] V)
-- →*  : 군 준동형 (MonoidHom). ρ(gh) = ρ(g) ∘ ρ(h) 를 자동 보장
-- →ₗ[ℂ] : ℂ에 대한 선형사상 (LinearMap)
-- abbrev : def 대신 사용. Lean이 타입 별칭을 자동으로 펼쳐서 ρ g 처럼 함수 적용 가능

-- Example 1.1.5: trivial representation
-- 모든 g ∈ G 를 항등사상 id_V 로 보내는 표현
def trivialRep : GroupRep G V where
  toFun    := fun _ => LinearMap.id
  -- _ : 인자 g 를 무시. 모든 g에 대해 항등사상 반환
  map_one' := rfl
  -- ρ(e) = id 조건. rfl : 양변이 definitionally equal 이므로 자동 증명
  map_mul' := fun _ _ => rfl
  -- ρ(gh) = ρ(g) ∘ ρ(h) 조건. 둘 다 id 이므로 자동 증명

-- Definition 1.1.6: 두 표현의 동치
-- f : V → W 가 G-linear 이고 isomorphism 이면 두 표현은 동형
structure RepIso
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W) where
  -- ρ : G → GL(V), π : G → GL(W) 는 비교할 두 표현
  toLinearEquiv : V ≃ₗ[ℂ] W
  -- ≃ₗ[ℂ] : ℂ-선형 동형사상 (가역 선형사상). →ₗ 과 달리 역사상 존재 보장
  comm : ∀ g : G, toLinearEquiv.toLinearMap ∘ₗ (ρ g) = (π g) ∘ₗ toLinearEquiv.toLinearMap
  -- 교환 조건: 모든 g ∈ G 에 대해 f ∘ ρ(g) = π(g) ∘ f
  -- ∘ₗ : 선형사상의 합성

-- Definition 1.4.1: G-linear map
-- f : V → W 가 모든 g에 대해 f ∘ ρ(g) = π(g) ∘ f 를 만족하는 선형사상
structure GLinearMap
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W) where
  toLinearMap : V →ₗ[ℂ] W
  -- →ₗ[ℂ] : 일반 선형사상. RepIso 와 달리 가역일 필요 없음
  comm : ∀ g : G, toLinearMap ∘ₗ (ρ g) = (π g) ∘ₗ toLinearMap
  -- 교환 조건: 모든 g ∈ G 에 대해 f ∘ ρ(g) = π(g) ∘ f
  -- RepIso 는 GLinearMap 중 toLinearMap 이 동형인 특수한 경우

end RepresentationTheory
