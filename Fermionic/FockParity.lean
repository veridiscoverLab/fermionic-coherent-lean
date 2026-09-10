import Fermionic.PhysicalGaussian

/-! Parity of the actual creation, contraction and Euclidean Spin action.
The target is the original exterior algebra's `evenOdd` submodule. No
converse fixed-point description of the grade involution is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Fermionic.FockParity
open Module Fermionic.Fock Fermionic.SpinorTransport

section Exterior
variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

theorem create_even_to_odd (v : E) {s : Space R E}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 0) :
    create v s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 1 := by
  change CliffordAlgebra.ι (0 : QuadraticForm R E) v * s ∈ _
  exact CliffordAlgebra.evenOdd_mul_le (0 : QuadraticForm R E) 1 0
    (Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one _ v) hs)

theorem create_odd_to_even (v : E) {s : Space R E}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 1) :
    create v s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 0 := by
  change CliffordAlgebra.ι (0 : QuadraticForm R E) v * s ∈ _
  exact CliffordAlgebra.evenOdd_mul_le (0 : QuadraticForm R E) 1 1
    (Submodule.mul_mem_mul (CliffordAlgebra.ι_mem_evenOdd_one _ v) hs)

theorem annihilate_even_to_odd (f : Module.Dual R E) {s : Space R E}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 0) :
    annihilate f s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 1 := by
  change CliffordAlgebra.contractLeft f s ∈ _
  induction s, hs using CliffordAlgebra.even_induction with
  | algebraMap r =>
      rw [CliffordAlgebra.contractLeft_algebraMap]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul v w x hx ih =>
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (create_even_to_odd w hx))
        (create_even_to_odd v (Submodule.sub_mem _
          (Submodule.smul_mem _ _ hx) (create_odd_to_even w ih)))

theorem annihilate_odd_to_even (f : Module.Dual R E) {s : Space R E}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 1) :
    annihilate f s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 0 := by
  change CliffordAlgebra.contractLeft f s ∈ _
  induction s, hs using CliffordAlgebra.odd_induction with
  | ι v =>
      rw [CliffordAlgebra.contractLeft_ι]
      exact (CliffordAlgebra.even _).algebraMap_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul v w x hx ih =>
      rw [mul_assoc, CliffordAlgebra.contractLeft_ι_mul,
        CliffordAlgebra.contractLeft_ι_mul]
      exact Submodule.sub_mem _
        (Submodule.smul_mem _ _ (create_odd_to_even w hx))
        (create_odd_to_even v (Submodule.sub_mem _
          (Submodule.smul_mem _ _ hx) (create_even_to_odd w ih)))

theorem action_even_to_odd (z : Module.Dual R E × E) {s : Space R E}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 0) :
    action z s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 1 :=
  Submodule.add_mem _ (annihilate_even_to_odd z.1 hs) (create_even_to_odd z.2 hs)

theorem action_odd_to_even (z : Module.Dual R E × E) {s : Space R E}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 1) :
    action z s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm R E) 0 :=
  Submodule.add_mem _ (annihilate_odd_to_even z.1 hs) (create_odd_to_even z.2 hs)

end Exterior

section EuclideanSpin
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance realInnerProduct : InnerProductSpace ℝ H :=
  InnerProductSpace.rclikeToReal ℂ H

/-- Every original even real Clifford element preserves the original even
Fock subspace under the constructed Majorana representation. -/
theorem real_even_preserves_even
    (x : CliffordAlgebra (majoranaQuadratic (H := H)))
    (hx : x ∈ CliffordAlgebra.even (majoranaQuadratic (H := H))) :
    ∀ (s : Space ℂ H), s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0 →
      representation (majoranaCliffordMap x) s ∈
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0 := by
  change x ∈ CliffordAlgebra.evenOdd (majoranaQuadratic (H := H)) 0 at hx
  induction x, hx using CliffordAlgebra.even_induction with
  | algebraMap r =>
      intro s hs
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply ℝ ℂ _ r, AlgHom.commutes]
      exact Submodule.smul_mem _ (r : ℂ) hs
  | add x y hx hy ihx ihy =>
      intro s hs
      simp only [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (ihx s hs) (ihy s hs)
  | ι_mul_ι_mul v w x hx ih =>
      intro s hs
      simp only [map_mul, Module.End.mul_apply,
        majoranaCliffordMap_generator, representation_generator]
      exact action_odd_to_even (majoranaEmbedding v)
        (action_even_to_odd (majoranaEmbedding w) (ih s hs))

theorem euclideanSpinAction_preserves_even
    (x : spinGroup (majoranaQuadratic (H := H))) {s : Space ℂ H}
    (hs : s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0) :
    euclideanSpinAction x s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0 :=
  real_even_preserves_even x (spinGroup.mem_even x.property) s hs

/-- The exact vacuum orbit lies in the original even exterior algebra. -/
theorem euclideanSpin_vacuum_even
    (x : spinGroup (majoranaQuadratic (H := H))) :
    euclideanSpinAction x (1 : Space ℂ H) ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0 :=
  euclideanSpinAction_preserves_even x (SetLike.one_mem_graded _)

theorem euclideanSpin_vacuum_smul_even
    (x : spinGroup (majoranaQuadratic (H := H))) (c : ℂ) :
    c • euclideanSpinAction x (1 : Space ℂ H) ∈
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0 :=
  Submodule.smul_mem _ c (euclideanSpin_vacuum_even x)

/-- Membership uses the existing physical Spin-orbit dictionary and gives
even parity as a conclusion, not as an extra dictionary hypothesis. -/
theorem gaussian_even (s : Space ℂ H) (hs : Fermionic.PhysicalGaussian.IsGaussian s) :
    s ∈ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ H) 0 := by
  obtain ⟨x, c, _hc, rfl⟩ := hs
  exact euclideanSpin_vacuum_smul_even x c

end EuclideanSpin
end Fermionic.FockParity
