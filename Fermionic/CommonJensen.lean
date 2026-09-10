import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Common finite weights on the original measure space

These lemmas formalize the measure-theoretic common-weight Jensen step of
`wehrl:common-convex`.  The functions remain on one and the same measure space;
the finite probabilities do not depend on the sample.  No coherent-state,
covariance, or representation-theoretic assertion is assumed or concluded here.

Validation: Lean 4.29.0, mathlib revision
`8a178386ffc0f5fef0b77738bb5449d50efeea95`, compiled on cab17 only.
The transitive axioms of each of the twenty declarations in this file were
checked with `#print axioms`: exactly `propext`, `Classical.choice`, and
`Quot.sound`.  There are no new axioms or admitted proofs.
-/

open MeasureTheory Set Filter
open scoped BigOperators

namespace Fermionic.CommonJensen

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
  {μ : Measure Ω} {w : ι → ℝ} {a : ι → Ω → ℝ} {F : ℝ → ℝ} {K : Set ℝ}

omit [MeasurableSpace Ω] in
/-- Pointwise finite Jensen, with one fixed family of weights. -/
theorem pointwise_jensen
    (hF : ConvexOn ℝ K F) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ i, a i ω ∈ K) :
    F (∑ i, w i * a i ω) ≤ ∑ i, w i * F (a i ω) := by
  simpa only [smul_eq_mul] using
    hF.map_sum_le (t := Finset.univ) (fun i _ => hw i) hs (fun i _ => ha i)

/-- Integration of the same finite weighted sum, without changing the measure. -/
theorem integral_weighted_sum
    (hfi : ∀ i, Integrable (fun ω => F (a i ω)) μ) :
    (∫ ω, ∑ i, w i * F (a i ω) ∂μ) =
      ∑ i, w i * ∫ ω, F (a i ω) ∂μ := by
  rw [integral_finset_sum Finset.univ (fun i _ => (hfi i).const_mul (w i))]
  simp only [integral_const_mul]

/-- Common-weight Jensen on an actual measure space.

The integrability hypotheses concern the displayed original functions only.
They are automatic for continuous functions on the compact interval in the
probability-space application, but are kept explicit to allow arbitrary measures.
-/
theorem integral_jensen
    (hF : ConvexOn ℝ K F) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ K)
    (hfi : ∀ i, Integrable (fun ω => F (a i ω)) μ)
    (hfm : Integrable (fun ω => F (∑ i, w i * a i ω)) μ) :
    (∫ ω, F (∑ i, w i * a i ω) ∂μ) ≤
      ∑ i, w i * ∫ ω, F (a i ω) ∂μ := by
  rw [← integral_weighted_sum hfi]
  apply integral_mono_ae hfm
    (integrable_finset_sum Finset.univ (fun i _ => (hfi i).const_mul (w i)))
  filter_upwards [ha] with ω hω
  exact pointwise_jensen hF hw hs hω

/-- Equality in common-weight strict Jensen forces every positive-weight
observation to coincide almost everywhere with the original weighted mixture. -/
theorem ae_eq_mixture_of_integral_eq
    (hF : StrictConvexOn ℝ K F) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ K)
    (hfi : ∀ i, Integrable (fun ω => F (a i ω)) μ)
    (hfm : Integrable (fun ω => F (∑ i, w i * a i ω)) μ)
    (heq : (∫ ω, F (∑ i, w i * a i ω) ∂μ) =
      ∑ i, w i * ∫ ω, F (a i ω) ∂μ) :
    ∀ i, 0 < w i → a i =ᵐ[μ] (fun ω => ∑ j, w j * a j ω) := by
  have hint : Integrable (fun ω => ∑ i, w i * F (a i ω)) μ :=
    integrable_finset_sum Finset.univ (fun i _ => (hfi i).const_mul (w i))
  have hle : (fun ω => F (∑ i, w i * a i ω)) ≤ᵐ[μ]
      (fun ω => ∑ i, w i * F (a i ω)) := by
    filter_upwards [ha] with ω hω
    exact pointwise_jensen hF.convexOn hw hs hω
  have hpoint := (integral_eq_iff_of_ae_le hfm hint hle).mp
    (heq.trans (integral_weighted_sum hfi).symm)
  intro i hi
  filter_upwards [ha, hpoint] with ω hω he
  have hJ := (hF.map_sum_eq_iff' (t := Finset.univ)
    (fun j _ => hw j) hs (fun j _ => hω j)).mp
      (by simpa only [smul_eq_mul] using he)
  simpa only [smul_eq_mul] using hJ i (Finset.mem_univ i) (ne_of_gt hi)

/-- In the strict equality case every two positive-weight observations agree
on the original measure space, not merely in distribution. -/
theorem ae_eq_of_integral_eq
    (hF : StrictConvexOn ℝ K F) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ K)
    (hfi : ∀ i, Integrable (fun ω => F (a i ω)) μ)
    (hfm : Integrable (fun ω => F (∑ i, w i * a i ω)) μ)
    (heq : (∫ ω, F (∑ i, w i * a i ω) ∂μ) =
      ∑ i, w i * ∫ ω, F (a i ω) ∂μ) :
    ∀ i j, 0 < w i → 0 < w j → a i =ᵐ[μ] a j := by
  intro i j hi hj
  exact (ae_eq_mixture_of_integral_eq hF hw hs ha hfi hfm heq i hi).trans
    (ae_eq_mixture_of_integral_eq hF hw hs ha hfi hfm heq j hj).symm

/-- Equality of the original pushforward measures gives the common integral. -/
theorem integral_eq_of_map_eq {η : Measure ℝ} {b : Ω → ℝ}
    (hb : AEMeasurable b μ) (hlaw : Measure.map b μ = η)
    (hF : Integrable F η) :
    (∫ ω, F (b ω) ∂μ) = ∫ t, F t ∂η := by
  have hi : Integrable F (Measure.map b μ) := hlaw.symm ▸ hF
  exact (integral_map hb hi.aestronglyMeasurable).symm.trans
    (congrArg (fun ν => ∫ t, F t ∂ν) hlaw)

/-- The common-law Jensen inequality.  The laws refer to the original
observations, and all observations retain their original joint coupling. -/
theorem common_law_jensen {η : Measure ℝ}
    (hF : ConvexOn ℝ K F) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ K)
    (ham : ∀ i, AEMeasurable (a i) μ)
    (hlaw : ∀ i, Measure.map (a i) μ = η)
    (hFi : Integrable F η)
    (hfm : Integrable (fun ω => F (∑ i, w i * a i ω)) μ) :
    (∫ ω, F (∑ i, w i * a i ω) ∂μ) ≤ ∫ t, F t ∂η := by
  have hfi : ∀ i, Integrable (fun ω => F (a i ω)) μ := by
    intro i
    exact ((hlaw i).symm ▸ hFi).comp_aemeasurable (ham i)
  calc
    _ ≤ ∑ i, w i * ∫ ω, F (a i ω) ∂μ := integral_jensen hF hw hs ha hfi hfm
    _ = ∑ i, w i * ∫ t, F t ∂η := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_eq_of_map_eq (ham i) (hlaw i) hFi]
    _ = ∫ t, F t ∂η := by rw [← Finset.sum_mul, hs, one_mul]

/-- Strict common-law Jensen: equality forces pathwise agreement almost
everywhere for every pair of positive-weight components. -/
theorem common_law_eq_implies_ae_eq {η : Measure ℝ}
    (hF : StrictConvexOn ℝ K F) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ K)
    (ham : ∀ i, AEMeasurable (a i) μ)
    (hlaw : ∀ i, Measure.map (a i) μ = η)
    (hFi : Integrable F η)
    (hfm : Integrable (fun ω => F (∑ i, w i * a i ω)) μ)
    (heq : (∫ ω, F (∑ i, w i * a i ω) ∂μ) = ∫ t, F t ∂η) :
    ∀ i j, 0 < w i → 0 < w j → a i =ᵐ[μ] a j := by
  have hfi : ∀ i, Integrable (fun ω => F (a i ω)) μ := by
    intro i
    exact ((hlaw i).symm ▸ hFi).comp_aemeasurable (ham i)
  apply ae_eq_of_integral_eq hF hw hs ha hfi hfm
  rw [heq]
  calc
    _ = ∑ i, w i * ∫ t, F t ∂η := by rw [← Finset.sum_mul, hs, one_mul]
    _ = ∑ i, w i * ∫ ω, F (a i ω) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_eq_of_map_eq (ham i) (hlaw i) hFi]

section ContinuousWrappers

variable [IsFiniteMeasure μ]

/-- Compact-interval continuity supplies integrability on the actual
pushforward measure, even if the function has no regularity outside the interval. -/
theorem integrable_map_of_continuousOn_unitInterval {b : Ω → ℝ}
    (hF : ContinuousOn F (Icc (0 : ℝ) 1)) (hb : AEMeasurable b μ)
    (hrange : ∀ᵐ ω ∂μ, b ω ∈ Icc (0 : ℝ) 1) :
    Integrable F (Measure.map b μ) := by
  have hrange' : ∀ᵐ t ∂Measure.map b μ, t ∈ Icc (0 : ℝ) 1 :=
    (ae_map_iff hb measurableSet_Icc).mpr hrange
  have hi : IntegrableOn F (Icc (0 : ℝ) 1) (Measure.map b μ) := hF.integrableOn_Icc
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hrange'] using hi

/-- Automatic integrability of a continuous interval observation on a finite
measure space; no extension of `F` outside its stated domain is used. -/
theorem integrable_comp_of_continuousOn_unitInterval {b : Ω → ℝ}
    (hF : ContinuousOn F (Icc (0 : ℝ) 1)) (hb : AEMeasurable b μ)
    (hrange : ∀ᵐ ω ∂μ, b ω ∈ Icc (0 : ℝ) 1) :
    Integrable (fun ω => F (b ω)) μ :=
  (integrable_map_of_continuousOn_unitInterval hF hb hrange).comp_aemeasurable hb

omit [IsFiniteMeasure μ] in
/-- The original common mixture is still measurable and interval-valued. -/
theorem mixture_aemeasurable_and_range
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ Icc (0 : ℝ) 1)
    (ham : ∀ i, AEMeasurable (a i) μ) :
    AEMeasurable (fun ω => ∑ i, w i * a i ω) μ ∧
      ∀ᵐ ω ∂μ, (∑ i, w i * a i ω) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.aemeasurable_fun_sum Finset.univ
      (fun i _ => (ham i).const_mul (w i))
  · filter_upwards [ha] with ω hω
    simpa only [smul_eq_mul] using (convex_Icc (0 : ℝ) 1).sum_mem
      (t := Finset.univ) (fun i _ => hw i) hs (fun i _ => hω i)

/-- The exact common-law assertion for continuous convex interval functions.
All integrability obligations are proved from the stated finite measure,
continuity, measurability and interval range assumptions.  In particular this
applies to the probability spaces in the paper. -/
theorem common_law_jensen_continuous {η : Measure ℝ}
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ Icc (0 : ℝ) 1)
    (ham : ∀ i, AEMeasurable (a i) μ)
    (hlaw : ∀ i, Measure.map (a i) μ = η) :
    (∫ ω, F (∑ i, w i * a i ω) ∂μ) ≤ ∫ t, F t ∂η := by
  have hsum : (∑ i, w i) ≠ 0 := by rw [hs]; exact one_ne_zero
  obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hFi : Integrable F η := by
    rw [← hlaw i]
    exact integrable_map_of_continuousOn_unitInterval hFc (ham i)
      (ha.mono (fun _ h => h i))
  obtain ⟨hmm, hmr⟩ := mixture_aemeasurable_and_range hw hs ha ham
  exact common_law_jensen hF hw hs ha ham hlaw hFi
    (integrable_comp_of_continuousOn_unitInterval hFc hmm hmr)

/-- The strict equality case of the continuous common-law theorem requires
no separate integrability inputs. -/
theorem common_law_eq_implies_ae_eq_continuous {η : Measure ℝ}
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (ha : ∀ᵐ ω ∂μ, ∀ i, a i ω ∈ Icc (0 : ℝ) 1)
    (ham : ∀ i, AEMeasurable (a i) μ)
    (hlaw : ∀ i, Measure.map (a i) μ = η)
    (heq : (∫ ω, F (∑ i, w i * a i ω) ∂μ) = ∫ t, F t ∂η) :
    ∀ i j, 0 < w i → 0 < w j → a i =ᵐ[μ] a j := by
  have hsum : (∑ i, w i) ≠ 0 := by rw [hs]; exact one_ne_zero
  obtain ⟨i, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hFi : Integrable F η := by
    rw [← hlaw i]
    exact integrable_map_of_continuousOn_unitInterval hFc (ham i)
      (ha.mono (fun _ h => h i))
  obtain ⟨hmm, hmr⟩ := mixture_aemeasurable_and_range hw hs ha ham
  exact common_law_eq_implies_ae_eq hF hw hs ha ham hlaw hFi
    (integrable_comp_of_continuousOn_unitInterval hFc hmm hmr) heq

end ContinuousWrappers

section Scaling

variable {ν : Measure ℝ}

/-- Multiplication by an interval-valued scale preserves the interval. -/
lemma mul_mem_unitInterval {x z : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hz : z ∈ Icc (0 : ℝ) 1) : x * z ∈ Icc (0 : ℝ) 1 :=
  ⟨mul_nonneg hx.1 hz.1, (mul_le_mul_of_nonneg_right hx.2 hz.1).trans
    (by simpa using hz.2)⟩

/-- A scale mixture of a convex function is convex on the same unit interval.
The entire fixed scale law is used for every value of the external parameter. -/
theorem scale_mixture_convex
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (hν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun z => F (t * z)) ν) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => ∫ z, F (t * z) ∂ν) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy c d hc hd hcd
  have hm := (convex_Icc (0 : ℝ) 1) hx hy hc hd hcd
  have hle : (fun z => F ((c • x + d • y) * z)) ≤ᵐ[ν]
      (fun z => c * F (x * z) + d * F (y * z)) := by
    filter_upwards [hν] with z hz
    simpa only [smul_eq_mul, add_mul, mul_assoc] using
      hF.2 (mul_mem_unitInterval hx hz) (mul_mem_unitInterval hy hz) hc hd hcd
  have h := integral_mono_ae (hi _ hm)
    (((hi x hx).const_mul c).add ((hi y hy).const_mul d)) hle
  simpa only [Pi.add_apply, integral_add ((hi x hx).const_mul c) ((hi y hy).const_mul d),
    integral_const_mul, smul_eq_mul] using h

/-- Strict convexity survives scale averaging when a positive-measure set of
scales is strictly positive.  No pointwise positive lower bound is required. -/
theorem scale_mixture_strictConvex
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (hν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hpos : ν (Ioi (0 : ℝ)) ≠ 0)
    (hi : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun z => F (t * z)) ν) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => ∫ z, F (t * z) ∂ν) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy hxy c d hc hd hcd
  have hm := (convex_Icc (0 : ℝ) 1) hx hy hc.le hd.le hcd
  have hle : (fun z => F ((c • x + d • y) * z)) ≤ᵐ[ν]
      (fun z => c * F (x * z) + d * F (y * z)) := by
    filter_upwards [hν] with z hz
    simpa only [smul_eq_mul, add_mul, mul_assoc] using
      hF.convexOn.2 (mul_mem_unitInterval hx hz) (mul_mem_unitInterval hy hz)
        hc.le hd.le hcd
  have hleft := hi _ hm
  have hright := ((hi x hx).const_mul c).add ((hi y hy).const_mul d)
  have hlt : (∫ z, F ((c • x + d • y) * z) ∂ν) <
      ∫ z, c * F (x * z) + d * F (y * z) ∂ν := by
    refine lt_of_le_of_ne (integral_mono_ae hleft hright hle) ?_
    intro heq
    have he := (integral_eq_iff_of_ae_le hleft hright hle).mp heq
    obtain ⟨z, hzpos, hz, hzeq⟩ :=
      Measure.exists_mem_of_measure_ne_zero_of_ae hpos (ae_restrict_of_ae (hν.and he))
    have hzne : z ≠ 0 := ne_of_gt hzpos
    have hneq : x * z ≠ y * z := fun h => hxy (mul_right_cancel₀ hzne h)
    have hzlt := hF.2 (mul_mem_unitInterval hx hz) (mul_mem_unitInterval hy hz)
      hneq hc hd hcd
    have hzlt' : F ((c • x + d • y) * z) <
        c * F (x * z) + d * F (y * z) := by
      simpa only [smul_eq_mul, add_mul, mul_assoc] using hzlt
    exact (ne_of_lt hzlt') hzeq
  simpa only [Pi.add_apply, integral_add ((hi x hx).const_mul c) ((hi y hy).const_mul d),
    integral_const_mul, smul_eq_mul] using hlt

variable [IsFiniteMeasure ν]

/-- All scaled observations of a continuous interval function are integrable. -/
theorem integrable_scaled_of_continuousOn
    (hF : ContinuousOn F (Icc (0 : ℝ) 1))
    (hν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    Integrable (fun z => F (t * z)) ν := by
  apply integrable_comp_of_continuousOn_unitInterval hF
    (measurable_const.mul measurable_id).aemeasurable
  exact hν.mono (fun _ hz => mul_mem_unitInterval ht hz)

/-- Continuity of the scale mixture, proved on the original fixed scale law
by compact domination.  This supplies the continuity input for reusing the
common-law Jensen theorem at the next conditioning step. -/
theorem scale_mixture_continuousOn
    (hF : ContinuousOn F (Icc (0 : ℝ) 1))
    (hν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun t => ∫ z, F (t * z) ∂ν) (Icc (0 : ℝ) 1) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x ∈ F '' Icc (0 : ℝ) 1, ‖x‖ ≤ C :=
    (isCompact_Icc.image_of_continuousOn hF).isBounded.exists_norm_le
  apply continuousOn_of_dominated (bound := fun _ => C)
  · intro t ht
    exact (integrable_scaled_of_continuousOn hF hν ht).aestronglyMeasurable
  · intro t ht
    filter_upwards [hν] with z hz
    exact hC _ ⟨t * z, mul_mem_unitInterval ht hz, rfl⟩
  · exact integrable_const C
  · filter_upwards [hν] with z hz
    exact hF.comp (continuous_id.mul_const z).continuousOn
      (fun t ht => mul_mem_unitInterval ht hz)

/-- The continuous scale-mixture convexity theorem has no integrability
premises. -/
theorem scale_mixture_convex_continuous
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (hν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1) :
    ConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => ∫ z, F (t * z) ∂ν) :=
  scale_mixture_convex hF hν (fun _ ht => integrable_scaled_of_continuousOn hFc hν ht)

/-- The continuous strict scale-mixture theorem has no integrability premises
and permits an arbitrary atom at zero. -/
theorem scale_mixture_strictConvex_continuous
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F)
    (hν : ∀ᵐ z ∂ν, z ∈ Icc (0 : ℝ) 1)
    (hpos : ν (Ioi (0 : ℝ)) ≠ 0) :
    StrictConvexOn ℝ (Icc (0 : ℝ) 1) (fun t => ∫ z, F (t * z) ∂ν) :=
  scale_mixture_strictConvex hF hν hpos
    (fun _ ht => integrable_scaled_of_continuousOn hFc hν ht)

end Scaling

end Fermionic.CommonJensen
