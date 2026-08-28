-- Basic.lean

import Mathlib

namespace RepresentationTheory

variable (G : Type*) [Group G]
variable (V : Type*) [AddCommGroup V] [Module ℂ V]

-- Definition 1.2.1: 군 표현
-- ρ : G → GL(V), 즉 G에서 V의 가역 선형사상들의 군으로의 준동형
def GroupRep := G →* (V →ₗ[ℂ] V)

-- Example 1.1.5: trivial representation
-- 모든 g ∈ G 를 항등사상으로 보내는 표현
def trivialRep : GroupRep G V where
  toFun    := fun _ => LinearMap.id
  map_one' := rfl
  map_mul' := fun _ _ => rfl

end RepresentationTheory
