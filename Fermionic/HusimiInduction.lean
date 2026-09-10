import Fermionic.ExteriorHusimi
import Fermionic.SlaterOneParticle
import Fermionic.OccupationConvexOrder
import Fermionic.HusimiScale

/-! Assembly of the actual exterior Husimi induction. -/

noncomputable section
namespace Fermionic.HusimiInduction
open Matrix MeasureTheory Set
open scoped ComplexOrder
open Fermionic.ExteriorUnitary Fermionic.ExteriorHusimi Fermionic.ConditionalSector
open Fermionic.HaarConditioning Fermionic.CommonJensen Fermionic.DensityRigidity
open Fermionic.OccupationMixture Fermionic.OccupancyOrbit Fermionic.OccupationConvexOrder
open Fermionic.SlaterOneParticle
open Fermionic.HusimiScale

theorem scaled_test_continuous {F : ℝ → ℝ}
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun x => F (a * x)) (Icc (0 : ℝ) 1) :=
  hFc.comp (continuous_const.mul continuous_id).continuousOn
    (fun _ hx => mul_mem_unitInterval ha hx)

theorem scaled_test_convex {F : ℝ → ℝ}
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun x => F (a * x)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy c d hc hd hcd
  simpa only [smul_eq_mul, mul_add, mul_left_comm, mul_assoc] using
    hF.2 (mul_mem_unitInterval ha hx) (mul_mem_unitInterval ha hy) hc hd hcd

theorem readout_weight_normalized {n p : ℕ}
    (A : Matrix (Index n p) (Index n p) ℂ) (ha : weight A ≠ 0)
    (S : Index n p) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    readout A S U = weight A * readout (normalized A) S U := by
  rw [readout_eq_quadratic, readout_eq_quadratic]
  exact quadratic_eq_weight_mul_normalized ha _

/-- Integrability of the entire conditional inner average comes from the
original compact double-Haar space, including the zero-weight branches. -/
theorem conditional_inner_integrable (M p : ℕ)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (S : Index M p)
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    Integrable (fun U => ∫ V, F (readout (conditionalMatrix M p ρ U) S V)
      ∂unitaryHaar (Fin M)) (unitaryHaar (Fin (M + 1))) := by
  letI : SecondCountableTopology (Matrix (Fin (M + 1)) (Fin (M + 1)) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin (M + 1) → Fin (M + 1) → ℂ))
  letI : SecondCountableTopology (Matrix.unitaryGroup (Fin (M + 1)) ℂ) :=
    TopologicalSpace.secondCountableTopology_induced _ _
      (fun U : Matrix.unitaryGroup (Fin (M + 1)) ℂ => U.val)
  have hc : Continuous (fun z : Matrix.unitaryGroup (Fin (M + 1)) ℂ ×
      Matrix.unitaryGroup (Fin M) ℂ =>
      F (readout ρ (insertFirst S) (z.1 * fixFirstFinHom M z.2))) :=
    (continuous_test_readout hρ ht (insertFirst S) hFc).comp
      (continuous_fst.mul ((fixFirstFinHom_continuous M).comp continuous_snd))
  have hi := hc.integrable_of_hasCompactSupport
    (μ := (unitaryHaar (Fin (M + 1))).prod (unitaryHaar (Fin M)))
    (HasCompactSupport.of_compactSpace _)
  simpa only [readout_conditional] using hi.integral_prod_left

theorem conditional_coherent_weight (M p : ℕ) (S : Index M p)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) :
    weight (conditionalMatrix M p (basisProjector (insertFirst S)) U) =
      projectionReadout (insertFirst S).val 0 U := by
  rw [conditional_weight_eq_oneParticleReadout, oneParticleReadout,
    oneParticle_basisProjector]
  rfl

theorem zero_sector_isSlater (n : ℕ)
    (ρ : Matrix (Index n 0) (Index n 0) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n 0) : IsSlaterDensity ρ := by
  have hsingle : ∀ R : Index n 0, R = S := by
    intro R
    apply Subtype.ext
    exact (Finset.card_eq_zero.mp R.property).trans (Finset.card_eq_zero.mp S.property).symm
  have heq := eq_basisProjector_of_trace_eq_one hρ ht S
    (fun R hR => (hR (hsingle R)).elim)
  refine ⟨S, 1, ?_⟩
  simpa only [OneMemClass.coe_one, exteriorMatrix_one, Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one] using heq

def reference {n p : ℕ} (hp : p ≤ n) : Index n p :=
  Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb hp)

theorem index_card_le {n p : ℕ} (S : Index n p) : p ≤ n := by
  have h := Finset.card_le_univ S.val
  calc p = S.val.card := S.property.symm
       _ ≤ n := by simpa only [Fintype.card_fin] using h

/-- The lower-dimensional theorem is used only as the induction hypothesis;
the actual conditional density and all its hypotheses are proved here. -/
theorem conditional_inner_bound {M p : ℕ}
    (ih : ∀ (σ : Matrix (Index M p) (Index M p) ℂ), σ.PosSemidef → σ.trace = 1 →
      ∀ (S : Index M p) (F : ℝ → ℝ), ContinuousOn F (Icc (0 : ℝ) 1) →
      ConvexOn ℝ (Icc (0 : ℝ) 1) F →
      (∫ V, F (readout σ S V) ∂unitaryHaar (Fin M)) ≤
        ∫ V, F (readout (basisProjector S) S V) ∂unitaryHaar (Fin M))
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (S : Index M p)
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) :
    (∫ V, F (readout (conditionalMatrix M p ρ U) S V) ∂unitaryHaar (Fin M)) ≤
      scaleAverage S F (weight (conditionalMatrix M p ρ U)) := by
  have hA := conditionalMatrix_posSemidef M p hρ U
  have ha := conditional_weight_mem_unitInterval M p hρ ht U
  by_cases hz : weight (conditionalMatrix M p ρ U) = 0
  · have hzero := compression_zero_of_weight_zero hA hz
    rw [hz, scaleAverage_zero, hzero]
    simp [readout, rotated]
  · have hpos := lt_of_le_of_ne ha.1 (Ne.symm hz)
    have hnorm := normalized_posSemidef hA
    have htrace := normalized_trace_eq_one hA hpos
    have hi := ih (normalized (conditionalMatrix M p ρ U)) hnorm htrace S
      (fun x => F (weight (conditionalMatrix M p ρ U) * x))
      (scaled_test_continuous hFc ha) (scaled_test_convex hF ha)
    rw [scaleAverage_eq_integral S F hFc ha]
    simpa only [readout_weight_normalized _ hz] using hi

theorem conditional_integral_bound {M p : ℕ}
    (ih : ∀ (σ : Matrix (Index M p) (Index M p) ℂ), σ.PosSemidef → σ.trace = 1 →
      ∀ (S : Index M p) (F : ℝ → ℝ), ContinuousOn F (Icc (0 : ℝ) 1) →
      ConvexOn ℝ (Icc (0 : ℝ) 1) F →
      (∫ V, F (readout σ S V) ∂unitaryHaar (Fin M)) ≤
        ∫ V, F (readout (basisProjector S) S V) ∂unitaryHaar (Fin M))
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (S : Index M p)
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ U, F (readout ρ (insertFirst S) U) ∂unitaryHaar (Fin (M + 1))) ≤
      ∫ U, scaleAverage S F (oneParticleReadout ρ 0 U) ∂unitaryHaar (Fin (M + 1)) := by
  rw [integral_conditional M p hρ ht S F hFc]
  have hi := integrable_comp_of_continuousOn_unitInterval
    (μ := unitaryHaar (Fin (M + 1))) (continuous_scaleAverage S hFc)
    (actual_readout_continuous ρ hρ 0).measurable.aemeasurable
    (Filter.Eventually.of_forall (actual_readout_range ρ hρ ht 0))
  apply integral_mono (conditional_inner_integrable M p hρ ht S F hFc) hi
  intro U
  simpa only [conditional_weight_eq_oneParticleReadout] using
    conditional_inner_bound ih hρ ht S F hFc hF U

theorem occupation_integral_bound {M p : ℕ} (hp : p ≤ M)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (S : Index M p)
    (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ U, scaleAverage S F (oneParticleReadout ρ 0 U) ∂unitaryHaar (Fin (M + 1))) ≤
      ∫ U, F (readout (basisProjector (insertFirst S)) (insertFirst S) U)
        ∂unitaryHaar (Fin (M + 1)) := by
  rw [coherent_integral_conditioning hp S F hFc]
  simp_rw [conditional_coherent_weight]
  exact occupation_convex_order ρ hρ ht 0 (insertFirst S) (scaleAverage S F)
    (continuous_scaleAverage S hFc) (convex_scaleAverage S hFc hF)

/-- All dimensions, all full exterior-sector density matrices, and every
continuous convex interval test. No induction or conditional hypothesis is
present in this root theorem. -/
theorem exterior_husimi_convex_order (n p : ℕ)
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n)) ≤
      ∫ U, F (readout (basisProjector S) S U) ∂unitaryHaar (Fin n) := by
  induction n generalizing p F with
  | zero =>
      have hp : p = 0 := Nat.le_zero.mp (index_card_le S)
      subst p
      simp only [readout_zero_particles 0 ρ ht,
        readout_zero_particles 0 (basisProjector S) (basisProjector_trace S), le_refl]
  | succ M ih =>
      cases p with
      | zero =>
          simp only [readout_zero_particles (M + 1) ρ ht,
            readout_zero_particles (M + 1) (basisProjector S) (basisProjector_trace S), le_refl]
      | succ p =>
          have hp : p ≤ M := Nat.succ_le_succ_iff.mp (index_card_le S)
          let T : Index M p := reference hp
          have hb := (conditional_integral_bound (ih p) hρ ht T F hFc hF).trans
            (occupation_integral_bound hp hρ ht T F hFc hF)
          calc
            _ = ∫ U, F (readout ρ (insertFirst T) U) ∂unitaryHaar (Fin (M + 1)) :=
              integral_readout_reference ρ S (insertFirst T) F
            _ ≤ ∫ U, F (readout (basisProjector (insertFirst T)) (insertFirst T) U)
                ∂unitaryHaar (Fin (M + 1)) := hb
            _ = ∫ U, F (readout (basisProjector S) (insertFirst T) U)
                ∂unitaryHaar (Fin (M + 1)) :=
              integral_readout_coherent_input (insertFirst T) (insertFirst T) S F
            _ = _ := integral_readout_reference (basisProjector S) (insertFirst T) S F

theorem slater_integral_eq {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : IsSlaterDensity ρ)
    (S : Index n p) (F : ℝ → ℝ) :
    (∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout (basisProjector S) S U) ∂unitaryHaar (Fin n) := by
  obtain ⟨T, V, rfl⟩ := hρ
  exact (integral_readout_forward_rotated (basisProjector T) S V F).trans
    (integral_readout_coherent_input S T S F)

/-- Strict equality for the full original Husimi integral forces a pure Slater
state; the actual complete density is recovered, not just its covariance. -/
theorem exterior_husimi_equality_implies_slater (n p : ℕ)
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (heq : (∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout (basisProjector S) S U) ∂unitaryHaar (Fin n)) :
    IsSlaterDensity ρ := by
  cases p with
  | zero => exact zero_sector_isSlater n ρ hρ ht S
  | succ p =>
      cases n with
      | zero => exact False.elim (Nat.not_succ_le_zero p (index_card_le S))
      | succ M =>
          have hp : p ≤ M := Nat.succ_le_succ_iff.mp (index_card_le S)
          let T : Index M p := reference hp
          have heq' : (∫ U, F (readout ρ (insertFirst T) U) ∂unitaryHaar (Fin (M + 1))) =
              ∫ U, F (readout (basisProjector (insertFirst T)) (insertFirst T) U)
                ∂unitaryHaar (Fin (M + 1)) := by
            calc
              _ = ∫ U, F (readout ρ S U) ∂unitaryHaar (Fin (M + 1)) :=
                integral_readout_reference ρ (insertFirst T) S F
              _ = _ := heq
              _ = ∫ U, F (readout (basisProjector (insertFirst T)) S U)
                  ∂unitaryHaar (Fin (M + 1)) :=
                integral_readout_coherent_input S S (insertFirst T) F
              _ = _ := integral_readout_reference (basisProjector (insertFirst T)) S (insertFirst T) F
          have hleft := conditional_integral_bound (exterior_husimi_convex_order M p)
            hρ ht T F hFc hF.convexOn
          have hright := occupation_integral_bound hp hρ ht T F hFc hF.convexOn
          have hmiddle := le_antisymm hright (heq' ▸ hleft)
          rw [coherent_integral_conditioning hp T F hFc] at hmiddle
          simp_rw [conditional_coherent_weight] at hmiddle
          exact occupation_equality_implies_slater ρ hρ ht 0 (insertFirst T)
            (scaleAverage T F) (continuous_scaleAverage T hFc)
            (strictConvex_scaleAverage T hFc hF) hmiddle

/-- The full strict-equality characterization, including pure-state sufficiency. -/
theorem exterior_husimi_equality_iff (n p : ℕ)
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    ((∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout (basisProjector S) S U) ∂unitaryHaar (Fin n)) ↔
      IsSlaterDensity ρ :=
  ⟨exterior_husimi_equality_implies_slater n p ρ hρ ht S F hFc hF,
    fun h => slater_integral_eq ρ h S F⟩

/-- The theorem with an arbitrary pure Slater comparison state, as in the
manuscript, rather than a distinguished coordinate projector. -/
theorem exterior_husimi_convex_order_any_slater (n p : ℕ)
    (ρ σ : Matrix (Index n p) (Index n p) ℂ)
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (hσ : IsSlaterDensity σ)
    (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n)) ≤
      ∫ U, F (readout σ S U) ∂unitaryHaar (Fin n) :=
  (exterior_husimi_convex_order n p ρ hρ ht S F hFc hF).trans_eq
    (slater_integral_eq σ hσ S F).symm

end Fermionic.HusimiInduction
