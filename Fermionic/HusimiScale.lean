import Fermionic.SlaterClosure
import Fermionic.ExteriorHusimi
import Fermionic.CommonJensen

/-!
The fixed coherent Husimi scale law of the original exterior measurement.
Strict convexity uses actual positive Haar mass; coherent conditional equality
uses the proved physical Slater closure of the full conditional density.
-/

noncomputable section

namespace Fermionic.HusimiScale

open Matrix MeasureTheory Set
open Fermionic.ExteriorUnitary Fermionic.ExteriorHusimi Fermionic.ConditionalSector
open Fermionic.HaarConditioning Fermionic.DensityRigidity Fermionic.CommonJensen
open Fermionic.OccupationConvexOrder Fermionic.SlaterClosure
open scoped ComplexOrder

def coherentLaw {n p : ℕ} (S : Index n p) : Measure ℝ :=
  Measure.map (readout (basisProjector S) S) (unitaryHaar (Fin n))

instance coherentLaw_isProbability {n p : ℕ} (S : Index n p) :
    IsProbabilityMeasure (coherentLaw S) :=
  Measure.isProbabilityMeasure_map (readout_continuous _ S).measurable.aemeasurable

theorem coherentLaw_mem_unitInterval {n p : ℕ} (S : Index n p) :
    ∀ᵐ z ∂coherentLaw S, z ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff (readout_continuous _ S).measurable.aemeasurable measurableSet_Icc).mpr
  exact Filter.Eventually.of_forall
    (readout_mem_unitInterval (basisProjector_posSemidef S) (basisProjector_trace S) S)

def scaleAverage {n p : ℕ} (S : Index n p) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z, F (t * z) ∂coherentLaw S

theorem scaleAverage_eq_integral {n p : ℕ} (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    scaleAverage S F t =
      ∫ V, F (t * readout (basisProjector S) S V) ∂unitaryHaar (Fin n) := by
  exact (integral_eq_of_map_eq (readout_continuous _ S).measurable.aemeasurable rfl
    (integrable_scaled_of_continuousOn hFc (coherentLaw_mem_unitInterval S) ht)).symm

theorem continuous_scaleAverage {n p : ℕ} (S : Index n p) {F : ℝ → ℝ}
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    ContinuousOn (scaleAverage S F) (Icc (0 : ℝ) 1) :=
  scale_mixture_continuousOn hFc (coherentLaw_mem_unitInterval S)

theorem convex_scaleAverage {n p : ℕ} (S : Index n p) {F : ℝ → ℝ}
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (scaleAverage S F) :=
  scale_mixture_convex_continuous hFc hF (coherentLaw_mem_unitInterval S)

theorem strictConvex_scaleAverage {n p : ℕ} (S : Index n p) {F : ℝ → ℝ}
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (scaleAverage S F) :=
  scale_mixture_strictConvex_continuous hFc hF (coherentLaw_mem_unitInterval S)
    (coherent_readout_positive_mass S)

@[simp] theorem scaleAverage_zero {n p : ℕ} (S : Index n p) (F : ℝ → ℝ) :
    scaleAverage S F 0 = F 0 := by simp [scaleAverage]

/-- Each conditional branch of the original reference coherent state has the
same lower coherent integral, scaled by its own original success weight. -/
theorem coherent_inner_conditioning {M p : ℕ} (hp : p ≤ M) (S : Index M p)
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) :
    (∫ V, F (readout (conditionalMatrix M p (basisProjector (insertFirst S)) U) S V)
      ∂unitaryHaar (Fin M)) =
      scaleAverage S F (weight (conditionalMatrix M p (basisProjector (insertFirst S)) U)) := by
  let ρ := basisProjector (insertFirst S)
  have hρ : ρ.PosSemidef := basisProjector_posSemidef _
  have ht : ρ.trace = 1 := basisProjector_trace _
  have hs : IsSlaterDensity ρ := by
    refine ⟨insertFirst S, 1, ?_⟩
    simp only [Submonoid.coe_one, exteriorMatrix_one, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_one]
    rfl
  change (∫ V, F (readout (conditionalMatrix M p ρ U) S V) ∂unitaryHaar (Fin M)) =
    scaleAverage S F (weight (conditionalMatrix M p ρ U))
  have hw := conditional_weight_mem_unitInterval M p hρ ht U
  by_cases hz : weight (conditionalMatrix M p ρ U) = 0
  · have hc := compression_zero_of_weight_zero (conditionalMatrix_posSemidef M p hρ U) hz
    rw [hz, scaleAverage_zero, hc]
    simp [readout, rotated]
  · have hpos : 0 < weight (conditionalMatrix M p ρ U) :=
      lt_of_le_of_ne hw.1 (Ne.symm hz)
    obtain ⟨T, W, hW⟩ := conditional_isSlater hp ρ hs U hpos
    have hpoint (V : Matrix.unitaryGroup (Fin M) ℂ) :
        readout (conditionalMatrix M p ρ U) S V =
          weight (conditionalMatrix M p ρ U) *
            readout (normalized (conditionalMatrix M p ρ U)) S V := by
      rw [← readout_conditional M p ρ S U V,
        readout_conditional_normalized M p ρ S U hz V]
    simp_rw [hpoint, hW]
    exact (integral_readout_forward_rotated (basisProjector T) S W
      (fun x => F (weight (conditionalMatrix M p ρ U) * x))).trans
      ((integral_readout_coherent_input S T S
        (fun x => F (weight (conditionalMatrix M p ρ U) * x))).trans
        (scaleAverage_eq_integral S F hFc hw).symm)

/-- Exact equality for the original coherent reference, with its true Haar
conditioning and its full original conditional density. -/
theorem coherent_integral_conditioning {M p : ℕ} (hp : p ≤ M) (S : Index M p)
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    (∫ U, F (readout (basisProjector (insertFirst S)) (insertFirst S) U)
      ∂unitaryHaar (Fin (M + 1))) =
      ∫ U, scaleAverage S F
        (weight (conditionalMatrix M p (basisProjector (insertFirst S)) U))
        ∂unitaryHaar (Fin (M + 1)) := by
  rw [integral_conditional M p (basisProjector_posSemidef _) (basisProjector_trace _) S F hFc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (coherent_inner_conditioning hp S F hFc)

end Fermionic.HusimiScale
