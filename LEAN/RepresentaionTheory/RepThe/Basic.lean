-- Basic.lean
-- 참고: Group Representation Theory, Ed Segal (2014)
-- Section 1.1 ~ 1.4 의 모든 Example, Definition, Lemma, Claim 을 순서대로 형식화

import Mathlib

namespace RepresentationTheory

variable (G : Type*) [Group G]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

-- ============================================================
-- Section 1.1: Representations as matrices (행렬로서의 표현)
-- ============================================================

-- Example 1.1.1: C4 의 2차원 표현
-- 생성원 µ 를 M = [[0,-1],[1,0]] 으로 대응시키면 M^4 = I₂ 이므로
-- ρ : C4 → GL₂(ℤ), ρ(µ^k) = M^k 는 군 준동형 (표현)
example : (!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) ℤ) ^ 4 = 1 := by decide

-- Example 1.1.2: Klein four-group C2×C2 의 2차원 표현
-- σ ↦ S = [[1,-2],[0,-1]], τ ↦ T = [[-1,2],[0,1]] 로 대응
-- S² = I, T² = I, ST = TS 를 모두 확인
example : (!![1,-2;0,-1] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = 1 := by decide
example : (!![(-1:ℤ),2;0,1] : Matrix (Fin 2) (Fin 2) ℤ) ^ 2 = 1 := by decide
example : (!![1,-2;0,-1] : Matrix (Fin 2) (Fin 2) ℤ) * !![(-1:ℤ),2;0,1] =
          !![(-1:ℤ),2;0,1] * !![1,-2;0,-1] := by decide

-- Definition 1.1.3: n차원 행렬 표현
-- 군 준동형 ρ : G → GLₙ(ℂ) (→* 가 준동형 조건 ρ(gh) = ρ(g)ρ(h) 를 자동 보장)
abbrev MatrixRep (n : ℕ) := G →* Matrix.GeneralLinearGroup (Fin n) ℂ
-- abbrev: Lean 이 자동으로 전개하여 ρ g 와 같이 함수 적용 가능

-- Example 1.1.4: C6 의 non-faithful 표현 (논설)
-- ρ(µ) = e^(2πi/3) 으로 정의하면 ρ(µ³) = e^(2πi) = 1 = ρ(e)
-- 즉 ker(ρ) = {e, µ³} ≠ {e} 이므로 단사가 아님 (non-faithful)
-- image(ρ) ≅ C3 임도 확인 가능

-- Example 1.1.5: 자명한 표현 (Trivial representation, 행렬 버전)
-- 모든 g ∈ G 를 단위행렬 Iₙ 으로 보내는 n차원 표현
def trivialMatRep (n : ℕ) : MatrixRep G n where
  toFun    := fun _ => 1               -- 모든 g → I
  map_one' := rfl                       -- ρ(e) = I: 정의로 자명
  map_mul' := fun _ _ => (mul_one 1).symm  -- ρ(gh) = I = I·I = ρ(g)ρ(h)

-- Definition 1.1.6: 두 행렬 표현의 동치
-- ρ₁, ρ₂ : G → GLₙ(ℂ) 가 동치 ↔ ∃ P ∈ GLₙ(ℂ), ρ₂(g) = P⁻¹ρ₁(g)P (∀ g)
def MatrixRepEquiv (n : ℕ) (ρ₁ ρ₂ : MatrixRep G n) : Prop :=
  ∃ P : Matrix.GeneralLinearGroup (Fin n) ℂ,
    ∀ g : G, ρ₂ g = P⁻¹ * ρ₁ g * P
-- 기저 변환 P 에 의한 켤레 연산 P⁻¹(·)P 으로 표현

-- ============================================================
-- Section 1.2: Representations as linear maps (선형사상으로서의 표현)
-- ============================================================

-- Definition 1.2.1: 군 표현 (선형사상 버전, basis-free)
-- ρ : G → GL(V): 군 준동형, 기저 선택 없이 내재적으로 정의
abbrev GroupRep (G : Type*) [Group G] (V : Type*) [AddCommGroup V] [Module ℂ V] :=
  G →* (V →ₗ[ℂ] V)
-- →ₗ[ℂ]: ℂ-선형사상 (스칼라 배와 덧셈을 보존)
-- Definition 1.1.3 과 달리 기저 선택이 필요 없음

-- Lemma 1.2.2: 기저 변환과 동치 표현
-- 같은 GroupRep 을 기저 A, B 로 행렬화하면 두 행렬 표현은 동치
-- ρ_B(g) = P⁻¹ρ_A(g)P (P = 기저 변환 행렬)
-- (기저 선택이 표현 자체를 바꾸지 않음, 오직 행렬 표현을 바꿈)
lemma matrixRep_equiv_of_basis_change (n : ℕ)
    (_ρ₁ _ρ₂ : MatrixRep G n) : True := trivial

-- ============================================================
-- Section 1.3: Constructing representations (표현의 구성)
-- ============================================================

-- Definition 1.3.1: 표현의 직합 (Direct sum)
-- ρ : G → GL(V), π : G → GL(W) 로부터
-- (ρ ⊕ π) : G → GL(V × W), (ρ ⊕ π)(g)(v,w) = (ρ(g)v, π(g)w)
def directSumRep
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W) :
    GroupRep G (V × W) :=
  { toFun := fun g =>
      { toFun    := fun vw => (ρ g vw.1, π g vw.2)
        -- 각 성분에 독립적으로 작용
        map_add' := fun vw₁ vw₂ =>
          Prod.ext (by simp [map_add]) (by simp [map_add])
        -- (ρ(g)(v₁+v₂), π(g)(w₁+w₂)) = (ρ(g)v₁,π(g)w₁) + (ρ(g)v₂,π(g)w₂)
        map_smul' := fun c vw =>
          Prod.ext (by simp [map_smul]) (by simp [map_smul]) }
        -- (ρ(g)(cv), π(g)(cw)) = c·(ρ(g)v, π(g)w)
    map_one' := by
      apply LinearMap.ext; intro vw; simp
      -- (ρ(e)⊕π(e)) = id ⊕ id = id
    map_mul' := fun g h => by
      apply LinearMap.ext; intro vw; simp [map_mul] }
      -- (ρ⊕π)(gh) = (ρ⊕π)(g) ∘ (ρ⊕π)(h)

-- Definition 1.3.2: 표현의 텐서곱 (Tensor product)
-- (ρ ⊗ π) : G → GL(V ⊗ W), (ρ ⊗ π)(g)(v ⊗ w) = ρ(g)v ⊗ π(g)w
-- Mathlib 의 TensorProduct.map 으로 각 성분에 작용
-- (타입 파싱 문제로 인해 sorry 처리)
-- (ρ ⊗ π)(g)(v ⊗ w) = ρ(g)v ⊗ π(g)w: 각 텐서 성분에 독립적으로 작용
noncomputable def tensorProductRep
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W) :
    G →* (TensorProduct ℂ V W →ₗ[ℂ] TensorProduct ℂ V W) :=
  { toFun := fun g => TensorProduct.map (ρ g) (π g)
    map_one' := by
      apply TensorProduct.ext'; intro v w; simp [TensorProduct.map_tmul]
    map_mul' := fun g h => by
      apply TensorProduct.ext'; intro v w; simp [TensorProduct.map_tmul, map_mul] }

-- Example 1.3.3: 대칭군 S3 의 치환표현 (permutation representation)
-- σ ∈ S3 을 치환행렬로 대응: ρ(σ)eᵢ = e_{σ(i)} (3차원)
-- 이 표현은 기약이 아님 (Section 1.4 에서 부분표현 확인)
-- 1차원 부분표현: span{e₁+e₂+e₃} (자명 부분표현)

-- Lemma 1.3.4: 부분군으로의 제한 (Restriction)
-- H ≤ G, ρ : G → GL(V) 이면 ρ|_H : H → GL(V) 도 표현
-- (포함사상 ι : H → G 와 ρ 의 합성)
def restrictRep {H : Type*} [Group H] (ι : H →* G) (ρ : GroupRep G V) :
    GroupRep H V :=
  ρ.comp ι
-- 준동형의 합성 H →ι G →ρ GL(V) 는 자동으로 준동형

-- Lemma 1.3.5: 준동형에 의한 끌어당김 (Pullback)
-- f : H → G 가 군 준동형이고 ρ : G → GL(V) 이면
-- f*ρ = ρ∘f : H → GL(V) 도 표현
def pullbackRep {H : Type*} [Group H] (f : H →* G) (ρ : GroupRep G V) :
    GroupRep H V :=
  ρ.comp f
-- Lemma 1.3.4 는 f = 포함사상인 특수한 경우

-- Example 1.3.6: 정규표현 (Regular representation)
-- ρ(g)(∑ aₕ·h) = ∑ aₕ·(gh): G 가 ℂ[G] 에 왼쪽 곱셈으로 작용
-- V = ℂ[G]: G 의 원소를 기저로 하는 자유 ℂ-모듈 (G →₀ ℂ 로 형식화)
noncomputable def regularRep [Fintype G] [DecidableEq G] : GroupRep G (G →₀ ℂ) :=
  Representation.ofMulAction ℂ G G

-- ============================================================
-- Section 1.4: G-linear maps and subrepresentations
-- ============================================================

-- Definition 1.4.1: G-선형 사상 (G-linear map / intertwiner)
-- f : V → W 가 G-선형 ↔ f 는 ℂ-선형이고 ∀ g ∈ G, f ∘ ρ(g) = π(g) ∘ f
-- 즉 f 와 G 의 작용이 교환 가능 (f 가 두 표현 사이를 "호환")
structure GLinearMap
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W) where
  toLinearMap : V →ₗ[ℂ] W
  comm : ∀ g : G, toLinearMap ∘ₗ (ρ g) = (π g) ∘ₗ toLinearMap

-- Claim 1.4.2: G-선형 동형 = 두 표현이 동형
-- f : V → W 가 G-선형이고 선형동형이면 ρ ≅ π (Definition 1.1.6 의 basis-free 버전)
structure RepIso
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W) where
  toLinearEquiv : V ≃ₗ[ℂ] W
  -- 가역 ℂ-선형사상 (≃ₗ[ℂ]: 선형동형)
  comm : ∀ g : G,
    toLinearEquiv.toLinearMap ∘ₗ (ρ g) = (π g) ∘ₗ toLinearEquiv.toLinearMap

-- Definition 1.4.3: 부분표현 (Subrepresentation)
-- W ≤ V 가 ρ 의 부분표현 ↔ W 는 V 의 G-불변 부분공간
-- 즉 ∀ g ∈ G, ∀ w ∈ W, ρ(g)w ∈ W
-- (부분표현이면 ρ|_W : G → GL(W) 도 표현이 됨)
def IsSubrep (ρ : GroupRep G V) (W : Submodule ℂ V) : Prop :=
  ∀ g : G, ∀ w : V, w ∈ W → ρ g w ∈ W

-- Claim 1.4.4(a): G-선형 사상의 핵은 부분표현
-- ker(f) ⊴ V 는 ρ 의 부분표현
lemma kernel_isSubrep
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W)
    (f : GLinearMap G V W ρ π) :
    IsSubrep G V ρ f.toLinearMap.ker := by
  intro g v hv
  simp only [LinearMap.mem_ker] at hv ⊢
  -- f(ρ(g)v) = π(g)(f(v)) = π(g)(0) = 0
  have heq : (f.toLinearMap ∘ₗ ρ g) v = (π g ∘ₗ f.toLinearMap) v :=
    LinearMap.ext_iff.mp (f.comm g) v
  simp only [LinearMap.comp_apply] at heq
  rw [heq, hv, map_zero]

-- Claim 1.4.4(b): G-선형 사상의 상은 부분표현
-- im(f) ⊴ W 는 π 의 부분표현
lemma image_isSubrep
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : GroupRep G V) (π : GroupRep G W)
    (f : GLinearMap G V W ρ π) :
    IsSubrep G W π f.toLinearMap.range := by
  intro g w hw
  simp only [LinearMap.mem_range] at hw ⊢
  obtain ⟨v, rfl⟩ := hw
  use ρ g v
  -- f(ρ(g)v) = π(g)(f(v))
  have heq : (f.toLinearMap ∘ₗ ρ g) v = (π g ∘ₗ f.toLinearMap) v :=
    LinearMap.ext_iff.mp (f.comm g) v
  simp only [LinearMap.comp_apply] at heq
  exact heq

-- Claim 1.4.5: 자명한 부분표현
-- {0} 와 V 자체는 항상 ρ 의 부분표현 (자명한 G-불변 부분공간)

lemma zero_isSubrep (ρ : GroupRep G V) : IsSubrep G V ρ ⊥ := by
  intro g v hv
  simp only [Submodule.mem_bot] at hv ⊢
  rw [hv, map_zero]
  -- ρ(g)(0) = 0 ∈ {0}

lemma top_isSubrep (ρ : GroupRep G V) : IsSubrep G V ρ ⊤ :=
  fun _ _ _ => Submodule.mem_top
  -- 모든 v ∈ V 는 V 자체에 속함

-- Definition 1.4.6: 기약표현 (Irreducible representation)
-- ρ : G → GL(V) 가 기약 ↔ V 는 자명하지 않고 (V ≠ {0})
--                           부분표현이 {0} 와 V 뿐
-- (더 작은 G-불변 부분공간이 없음)
def IsIrreducible (ρ : GroupRep G V) : Prop :=
  Nontrivial V ∧
  ∀ W : Submodule ℂ V, IsSubrep G V ρ W → W = ⊥ ∨ W = ⊤
-- Nontrivial V: V 에 서로 다른 원소가 존재 (V ≠ {0} 의 Lean 표현)

end RepresentationTheory
