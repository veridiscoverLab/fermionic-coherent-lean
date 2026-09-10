import Fermionic.OccupationMixture
import Fermionic.OccupancyOrbit
import Fermionic.CommonJensen

/-!
The common probability-distribution comparison for the actual one-particle
occupation of an arbitrary full exterior-sector density matrix. The measure,
unitary action, probabilities, and every component are constructed explicitly.
This is the occupation step of the full Husimi induction, not an assumption
that the full Husimi order already holds.
-/

noncomputable section
namespace Fermionic.OccupationConvexOrder
open Matrix MeasureTheory Set
open scoped ComplexOrder
open Fermionic.ExteriorUnitary Fermionic.ExteriorDifferential
open Fermionic.OccupationMixture Fermionic.OccupancyOrbit
open Fermionic.HaarConditioning Fermionic.CommonJensen

def component {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (hρ : ρ.PosSemidef) (i : Fin n) (S : Index n p)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  projectionReadout S.val i (star (eigenRotation ρ hρ) * U)

theorem component_continuous {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (i : Fin n) (S : Index n p) : Continuous (component ρ hρ i S) :=
  (continuous_projectionReadout S.val i).comp (continuous_const_mul _)

theorem component_range {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (i : Fin n) (S : Index n p) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    component ρ hρ i S U ∈ Icc (0 : ℝ) 1 :=
  projectionReadout_mem_unitInterval S.val i _

theorem component_common_law {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (i : Fin n) (S T : Index n p) :
    Measure.map (component ρ hρ i S) (unitaryHaar (Fin n)) =
      Measure.map (projectionReadout T.val i) (unitaryHaar (Fin n)) := by
  exact (map_readout_mul_left (continuous_projectionReadout S.val i).measurable
    (star (eigenRotation ρ hρ))).trans (occupancy_readout_same_law S T i)

theorem actual_readout_eq_common_mixture {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (i : Fin n) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    oneParticleReadout ρ i U = ∑ S, probability ρ hρ S * component ρ hρ i S U := by
  rw [common_readout_mixture ρ hρ]
  simp only [component, projectionReadout, Submonoid.coe_mul, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, occupancyProjection, coordinateProjection,
    Matrix.mul_assoc]

theorem actual_readout_range {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (i : Fin n) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    oneParticleReadout ρ i U ∈ Icc (0 : ℝ) 1 := by
  rw [actual_readout_eq_common_mixture ρ hρ]
  simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) 1).sum_mem
    (t := Finset.univ) (fun S _ => probability_nonneg ρ hρ S)
    (probability_sum ρ hρ ht) (fun S _ => component_range ρ hρ i S U)

theorem actual_readout_continuous {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (i : Fin n) :
    Continuous (oneParticleReadout ρ i) := by
  change Continuous (fun U => oneParticleReadout ρ i U)
  simp_rw [actual_readout_eq_common_mixture ρ hρ]
  exact continuous_finset_sum Finset.univ (fun S _ =>
    (component_continuous ρ hρ i S).const_mul _)

/-- Full convex order of the original one-particle occupation distribution.
The only density hypotheses are its actual positivity and trace one. -/
theorem occupation_convex_order {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (i : Fin n) (T : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ U, F (oneParticleReadout ρ i U) ∂unitaryHaar (Fin n)) ≤
      ∫ U, F (projectionReadout T.val i U) ∂unitaryHaar (Fin n) := by
  have hJ := common_law_jensen_continuous hFc hF (probability_nonneg ρ hρ)
    (probability_sum ρ hρ ht)
    (Filter.Eventually.of_forall (fun U S => component_range ρ hρ i S U))
    (fun S => (component_continuous ρ hρ i S).measurable.aemeasurable)
    (fun S => component_common_law ρ hρ i S T)
  have hFi := integrable_map_of_continuousOn_unitInterval (μ := unitaryHaar (Fin n)) hFc
    (continuous_projectionReadout T.val i).measurable.aemeasurable
    (Filter.Eventually.of_forall (projectionReadout_mem_unitInterval T.val i))
  have hmap := integral_eq_of_map_eq
    (continuous_projectionReadout T.val i).measurable.aemeasurable rfl hFi
  simp_rw [← actual_readout_eq_common_mixture ρ hρ] at hJ
  exact hJ.trans_eq hmap.symm

/-- Normalized pure Slater densities in the actual exterior representation. -/
def IsSlaterDensity {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ) : Prop :=
  ∃ (S : Index n p) (V : Matrix.unitaryGroup (Fin n) ℂ),
    ρ = exteriorMatrix p V.val * Fermionic.DensityRigidity.basisProjector S *
      (exteriorMatrix p V.val).conjTranspose

theorem component_injective {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (i : Fin n) :
    Function.Injective (component ρ hρ i) := by
  intro S T heq
  apply Subtype.ext
  apply projectionReadout_injective i
  funext U
  have h := congrFun heq (eigenRotation ρ hρ * U)
  simpa only [component, ← mul_assoc, Unitary.star_mul_self, one_mul] using h

theorem eigenDensity_basis_implies_slater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (S : Index n p)
    (heq : eigenDensity ρ hρ = Fermionic.DensityRigidity.basisProjector S) :
    IsSlaterDensity ρ := by
  refine ⟨S, eigenRotation ρ hρ, ?_⟩
  have hU := (representation n p (eigenRotation ρ hρ)).property.2
  change exteriorMatrix p (eigenRotation ρ hρ).val *
    (exteriorMatrix p (eigenRotation ρ hρ).val).conjTranspose = 1 at hU
  rw [← heq, eigenDensity]
  calc
    _ = (exteriorMatrix p (eigenRotation ρ hρ).val *
        (exteriorMatrix p (eigenRotation ρ hρ).val).conjTranspose) * ρ *
        (exteriorMatrix p (eigenRotation ρ hρ).val *
        (exteriorMatrix p (eigenRotation ρ hρ).val).conjTranspose) := by rw [hU]; simp
    _ = _ := by simp only [Matrix.mul_assoc]

/-- Strict equality returns to the full original density matrix and forces
it to be a pure Slater state. No purity or diagonal-density hypothesis is used. -/
theorem occupation_equality_implies_slater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (i : Fin n) (T : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (heq : (∫ U, F (oneParticleReadout ρ i U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (projectionReadout T.val i U) ∂unitaryHaar (Fin n)) :
    IsSlaterDensity ρ := by
  have hFi := integrable_map_of_continuousOn_unitInterval (μ := unitaryHaar (Fin n)) hFc
    (continuous_projectionReadout T.val i).measurable.aemeasurable
    (Filter.Eventually.of_forall (projectionReadout_mem_unitInterval T.val i))
  have hmap := integral_eq_of_map_eq
    (continuous_projectionReadout T.val i).measurable.aemeasurable rfl hFi
  have hJ : (∫ U, F (∑ S, probability ρ hρ S * component ρ hρ i S U)
      ∂unitaryHaar (Fin n)) =
      ∫ t, F t ∂Measure.map (projectionReadout T.val i) (unitaryHaar (Fin n)) := by
    simp_rw [← actual_readout_eq_common_mixture ρ hρ]
    exact heq.trans hmap
  have hae := common_law_eq_implies_ae_eq_continuous hFc hF
    (probability_nonneg ρ hρ) (probability_sum ρ hρ ht)
    (Filter.Eventually.of_forall (fun U S => component_range ρ hρ i S U))
    (fun S => (component_continuous ρ hρ i S).measurable.aemeasurable)
    (fun S => component_common_law ρ hρ i S T) hJ
  have hsum : 0 < ∑ S, probability ρ hρ S := by rw [probability_sum ρ hρ ht]; exact zero_lt_one
  obtain ⟨S, _, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt hsum)
  have hS : 0 < probability ρ hρ S :=
    lt_of_le_of_ne (probability_nonneg ρ hρ S) hSne.symm
  have hz (R : Index n p) (hR : R ≠ S) : probability ρ hρ R = 0 := by
    apply le_antisymm _ (probability_nonneg ρ hρ R)
    apply le_of_not_gt
    intro hpos
    apply hR
    apply component_injective ρ hρ i
    exact readout_eq_of_ae_eq (component_continuous ρ hρ i R)
      (component_continuous ρ hρ i S) (hae R S hpos hS)
  apply eigenDensity_basis_implies_slater ρ hρ S
  apply Fermionic.DensityRigidity.eq_basisProjector_of_trace_eq_one
    (eigenDensity_posSemidef ρ hρ) ((eigenDensity_trace ρ hρ).trans ht) S
  intro R hR
  rw [← probability_cast, hz R hR, Complex.ofReal_zero]

end Fermionic.OccupationConvexOrder
