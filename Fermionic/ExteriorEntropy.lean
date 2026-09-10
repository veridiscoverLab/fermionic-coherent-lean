import Fermionic.HusimiInduction
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-! Positive real moments and Wehrl entropy for the actual exterior Husimi
measurement. Haar is a probability measure. The factor `sectorDimension` is
proved to normalize the first moment; no resolution of identity is assumed. -/

noncomputable section
namespace Fermionic.ExteriorEntropy
open Matrix MeasureTheory Set
open scoped ComplexOrder
open Fermionic.ExteriorUnitary Fermionic.ExteriorHusimi Fermionic.ConditionalSector
open Fermionic.HaarConditioning Fermionic.DensityRigidity
open Fermionic.OccupationConvexOrder Fermionic.HusimiInduction

def sectorDimension (n p : ℕ) : ℝ := Fintype.card (Index n p)

/-- The complete original occupancy basis has the manuscript's binomial dimension. -/
theorem sectorDimension_eq_choose (n p : ℕ) :
    sectorDimension n p = (Nat.choose n p : ℝ) := by
  unfold sectorDimension
  have h := Set.powersetCard.card (α := Fin n) (n := p)
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using congrArg Nat.cast h

theorem sectorDimension_pos {n p : ℕ} (S : Index n p) :
    0 < sectorDimension n p := by
  letI : Nonempty (Index n p) := ⟨S⟩
  unfold sectorDimension
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Index n p))

def powerMoment {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (S : Index n p) (q : ℝ) : ℝ :=
  ∫ U, (readout ρ S U) ^ q ∂unitaryHaar (Fin n)

def normalizedMoment {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (S : Index n p) (q : ℝ) : ℝ :=
  sectorDimension n p * powerMoment ρ S q

/-- The original probability-Haar Wehrl convention, with `0 log 0 = 0`. -/
def wehrl {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (S : Index n p) : ℝ :=
  -(sectorDimension n p) *
    ∫ U, readout ρ S U * Real.log (readout ρ S U) ∂unitaryHaar (Fin n)

theorem sum_readout {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    ∑ S : Index n p, readout ρ S U = ρ.trace.re := by
  have h := congrArg Complex.re (rotated_trace n p ρ U)
  simpa only [readout, Matrix.trace, Matrix.diag_apply, Complex.re_sum] using h

/-- The first-moment normalization follows from the complete original
occupancy basis and its common Haar law. -/
theorem normalizedMoment_one {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (ht : ρ.trace = 1)
    (S : Index n p) : normalizedMoment ρ S 1 = 1 := by
  classical
  have hi (T : Index n p) : Integrable (readout ρ T) (unitaryHaar (Fin n)) :=
    (readout_continuous ρ T).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq (T : Index n p) :
      (∫ U, readout ρ T U ∂unitaryHaar (Fin n)) =
        ∫ U, readout ρ S U ∂unitaryHaar (Fin n) :=
    integral_readout_reference ρ T S id
  have hsum : (∑ T : Index n p, ∫ U, readout ρ T U ∂unitaryHaar (Fin n)) = 1 := by
    rw [← integral_finset_sum _ (fun T _ => hi T)]
    simp only [sum_readout, ht, Complex.one_re, integral_const, probReal_univ,
      smul_eq_mul, one_mul]
  simp_rw [heq] at hsum
  simpa only [normalizedMoment, powerMoment, Real.rpow_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, sectorDimension] using hsum

theorem powerMoment_integrable {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    {q : ℝ} (hq : 0 ≤ q) :
    Integrable (fun U => (readout ρ S U) ^ q) (unitaryHaar (Fin n)) :=
  ((Real.continuous_rpow_const hq).comp (readout_continuous ρ S)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem rpow_strictConvex {q : ℝ} (hq : 1 < q) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun x : ℝ => x ^ q) :=
  (strictConvexOn_rpow hq).subset (fun _ hx => hx.1) (convex_Icc 0 1)

theorem neg_rpow_strictConvex {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun x : ℝ => -(x ^ q)) :=
  (Real.strictConcaveOn_rpow hq0 hq1).neg.subset
    (fun _ hx => hx.1) (convex_Icc 0 1)

theorem powerMoment_le_coherent {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq : 1 < q) :
    powerMoment ρ S q ≤ powerMoment (basisProjector S) S q :=
  exterior_husimi_convex_order n p ρ hρ ht S (fun x => x ^ q)
    (Real.continuous_rpow_const (le_of_lt (lt_trans zero_lt_one hq))).continuousOn
    (rpow_strictConvex hq).convexOn

theorem coherent_le_powerMoment {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    powerMoment (basisProjector S) S q ≤ powerMoment ρ S q := by
  have h := exterior_husimi_convex_order n p ρ hρ ht S (fun x => -(x ^ q))
    (Real.continuous_rpow_const hq0.le).neg.continuousOn
    (neg_rpow_strictConvex hq0 hq1).convexOn
  simpa only [integral_neg, neg_le_neg_iff, powerMoment] using h

/-- Every nontrivial positive real power has precisely the actual Slater
density matrices as equality cases. -/
theorem powerMoment_eq_iff_slater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) :
    (powerMoment ρ S q = powerMoment (basisProjector S) S q) ↔ IsSlaterDensity ρ := by
  rcases lt_or_gt_of_ne hq1 with hq | hq
  · have h := exterior_husimi_equality_iff n p ρ hρ ht S (fun x => -(x ^ q))
      (Real.continuous_rpow_const hq0.le).neg.continuousOn
      (neg_rpow_strictConvex hq0 hq)
    simpa only [integral_neg, neg_inj, powerMoment] using h
  · exact exterior_husimi_equality_iff n p ρ hρ ht S (fun x => x ^ q)
      (Real.continuous_rpow_const hq0.le).continuousOn (rpow_strictConvex hq)

theorem normalizedMoment_le_coherent {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq : 1 < q) :
    normalizedMoment ρ S q ≤ normalizedMoment (basisProjector S) S q :=
  mul_le_mul_of_nonneg_left (powerMoment_le_coherent ρ hρ ht S hq)
    (sectorDimension_pos S).le

theorem coherent_le_normalizedMoment {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    normalizedMoment (basisProjector S) S q ≤ normalizedMoment ρ S q :=
  mul_le_mul_of_nonneg_left (coherent_le_powerMoment ρ hρ ht S hq0 hq1)
    (sectorDimension_pos S).le

theorem normalizedMoment_eq_iff_slater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) :
    (normalizedMoment ρ S q = normalizedMoment (basisProjector S) S q) ↔
      IsSlaterDensity ρ := by
  unfold normalizedMoment
  rw [mul_right_inj' (sectorDimension_pos S).ne']
  exact powerMoment_eq_iff_slater ρ hρ ht S hq0 hq1

/-- Strict positivity is paid by the first-moment identity of the same
density matrix, including densities whose Husimi function has zeros. -/
theorem powerMoment_pos {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq : 0 < q) : 0 < powerMoment ρ S q := by
  have hn (U : Matrix.unitaryGroup (Fin n) ℂ) : 0 ≤ (readout ρ S U) ^ q :=
    Real.rpow_nonneg (readout_mem_unitInterval hρ ht S U).1 _
  have hnonneg : 0 ≤ powerMoment ρ S q := integral_nonneg hn
  by_contra hnot
  have hz : powerMoment ρ S q = 0 := le_antisymm (not_lt.mp hnot) hnonneg
  have hae := (integral_eq_zero_iff_of_nonneg hn (powerMoment_integrable ρ S hq.le)).mp hz
  have hfirst : powerMoment ρ S 1 = 0 := by
    unfold powerMoment
    simp only [Real.rpow_one]
    calc
      (∫ U, readout ρ S U ∂unitaryHaar (Fin n)) =
          ∫ _U, (0 : ℝ) ∂unitaryHaar (Fin n) := by
        apply integral_congr_ae
        filter_upwards [hae] with U hU
        exact (Real.rpow_eq_zero (readout_mem_unitInterval hρ ht S U).1 hq.ne').mp hU
      _ = 0 := integral_zero _ _
  have hnorm := normalizedMoment_one ρ ht S
  simp only [normalizedMoment, hfirst, mul_zero] at hnorm
  exact zero_ne_one hnorm

theorem normalizedMoment_pos {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq : 0 < q) : 0 < normalizedMoment ρ S q :=
  mul_pos (sectorDimension_pos S) (powerMoment_pos ρ hρ ht S hq)

/-- Rényi--Wehrl entropy in the original probability-Haar convention. -/
def renyiWehrl {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (S : Index n p) (q : ℝ) : ℝ :=
  (1 / (1 - q)) * Real.log (normalizedMoment ρ S q)

theorem renyiWehrl_minimum {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) :
    renyiWehrl (basisProjector S) S q ≤ renyiWehrl ρ S q := by
  have hp := normalizedMoment_pos ρ hρ ht S hq0
  have hpc := normalizedMoment_pos (basisProjector S)
    (basisProjector_posSemidef S) (basisProjector_trace S) S hq0
  rcases lt_or_gt_of_ne hq1 with hq | hq
  · exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hpc (coherent_le_normalizedMoment ρ hρ ht S hq0 hq))
      (one_div_nonneg.mpr (sub_nonneg.mpr hq.le))
  · exact mul_le_mul_of_nonpos_left
      (Real.log_le_log hp (normalizedMoment_le_coherent ρ hρ ht S hq))
      (one_div_nonpos.mpr (sub_nonpos.mpr hq.le))

theorem renyiWehrl_eq_iff_slater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≠ 1) :
    (renyiWehrl ρ S q = renyiWehrl (basisProjector S) S q) ↔ IsSlaterDensity ρ := by
  unfold renyiWehrl
  rw [mul_right_inj' (one_div_ne_zero (sub_ne_zero.mpr hq1.symm))]
  have hp := normalizedMoment_pos ρ hρ ht S hq0
  have hpc := normalizedMoment_pos (basisProjector S)
    (basisProjector_posSemidef S) (basisProjector_trace S) S hq0
  rw [Real.log_injOn_pos.eq_iff hp hpc]
  exact normalizedMoment_eq_iff_slater ρ hρ ht S hq0 hq1

theorem mul_log_strictConvex :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun x => x * Real.log x) :=
  Real.strictConvexOn_mul_log.subset (fun _ hx => hx.1) (convex_Icc 0 1)

theorem wehrl_minimum {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) : wehrl (basisProjector S) S ≤ wehrl ρ S := by
  have h := exterior_husimi_convex_order n p ρ hρ ht S (fun x => x * Real.log x)
    Real.continuous_mul_log.continuousOn mul_log_strictConvex.convexOn
  exact mul_le_mul_of_nonpos_left h (neg_nonpos.mpr (sectorDimension_pos S).le)

theorem wehrl_eq_iff_slater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) :
    (wehrl ρ S = wehrl (basisProjector S) S) ↔ IsSlaterDensity ρ := by
  unfold wehrl
  rw [mul_right_inj' (neg_ne_zero.mpr (sectorDimension_pos S).ne')]
  exact exterior_husimi_equality_iff n p ρ hρ ht S (fun x => x * Real.log x)
    Real.continuous_mul_log.continuousOn mul_log_strictConvex

end Fermionic.ExteriorEntropy
