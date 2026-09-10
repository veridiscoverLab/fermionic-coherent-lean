import Fermionic.HusimiInduction

/-!
The original invariant Slater-orbit probability measure, realized by actual
rank-one exterior projectors. This makes the transport from the group Haar
formulation to an orbit-measure formulation an explicit proved pushforward.
No topology or measure on an unrelated quotient is postulated.
-/

noncomputable section
namespace Fermionic.SlaterMeasure
open Matrix MeasureTheory Set
open scoped ComplexOrder
open Fermionic.ExteriorUnitary Fermionic.ExteriorHusimi Fermionic.HaarConditioning
open Fermionic.DensityRigidity Fermionic.OccupationConvexOrder
open Fermionic.SlaterOrbit Fermionic.OccupancyOrbit Fermionic.CommonJensen
open Fermionic.HusimiInduction

/-- The ordinary Borel structure of the actual finite-dimensional matrix space. -/
instance sectorMatrixMeasurable (n p : ℕ) :
    MeasurableSpace (Matrix (Index n p) (Index n p) ℂ) := borel _

instance sectorMatrixBorel (n p : ℕ) :
    BorelSpace (Matrix (Index n p) (Index n p) ℂ) := ⟨rfl⟩

def projector {n p : ℕ} (S : Index n p) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Matrix (Index n p) (Index n p) ℂ :=
  exteriorMatrix p U.val * basisProjector S * (exteriorMatrix p U.val).conjTranspose

theorem projector_continuous {n p : ℕ} (S : Index n p) : Continuous (projector S) := by
  have hc : Continuous (fun U : Matrix.unitaryGroup (Fin n) ℂ => exteriorMatrix p U.val) :=
    (continuous_exteriorMatrix n p).comp continuous_subtype_val
  unfold projector
  fun_prop

def conjugate {n p : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ)
    (P : Matrix (Index n p) (Index n p) ℂ) : Matrix (Index n p) (Index n p) ℂ :=
  exteriorMatrix p U.val * P * (exteriorMatrix p U.val).conjTranspose

theorem conjugate_continuous {n p : ℕ} (U : Matrix.unitaryGroup (Fin n) ℂ) :
    Continuous (conjugate (p := p) U) := by
  unfold conjugate
  fun_prop

theorem projector_mul {n p : ℕ} (S : Index n p)
    (V U : Matrix.unitaryGroup (Fin n) ℂ) :
    projector S (V * U) = conjugate V (projector S U) := by
  simp only [projector, conjugate, Submonoid.coe_mul, exteriorMatrix_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

def orbitMeasure {n p : ℕ} (S : Index n p) :
    Measure (Matrix (Index n p) (Index n p) ℂ) :=
  Measure.map (projector S) (unitaryHaar (Fin n))

instance orbitMeasure_isProbability {n p : ℕ} (S : Index n p) :
    IsProbabilityMeasure (orbitMeasure S) :=
  Measure.isProbabilityMeasure_map (projector_continuous S).measurable.aemeasurable

/-- The constructed orbit probability is invariant under the actual action. -/
theorem orbitMeasure_invariant {n p : ℕ} (S : Index n p)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    Measure.map (conjugate V) (orbitMeasure S) = orbitMeasure S := by
  rw [orbitMeasure, Measure.map_map (conjugate_continuous V).measurable
    (projector_continuous S).measurable]
  have hf : conjugate V ∘ projector S = projector S ∘ fun U => V * U := by
    funext U
    exact (projector_mul S V U).symm
  rw [hf, ← Measure.map_map (projector_continuous S).measurable
    (measurable_const_mul V), map_mul_left_eq_self]

/-- Changing the occupancy reference leaves the whole matrix-valued law unchanged. -/
theorem orbitMeasure_reference_independent {n p : ℕ} (S T : Index n p) :
    orbitMeasure S = orbitMeasure T := by
  let V := permutationUnitary (orderedPermutation S T)
  have hf : projector T = projector S ∘ fun U => U * V := by
    funext U
    dsimp only [Function.comp_apply]
    rw [projector_mul]
    have hv : projector S V = basisProjector T := basis_projector_same_orbit S T
    rw [hv]
    rfl
  rw [orbitMeasure, orbitMeasure, hf, ← Measure.map_map (projector_continuous S).measurable
    (measurable_mul_const V), map_mul_right_eq_self]

def traceReadout {n p : ℕ} (ρ P : Matrix (Index n p) (Index n p) ℂ) : ℝ :=
  (ρ * P).trace.re

theorem traceReadout_continuous {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) : Continuous (traceReadout ρ) := by
  unfold traceReadout
  fun_prop

theorem basisProjector_eq_single {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) :
    basisProjector i = Matrix.single i i (1 : ℂ) := by
  ext j k
  simp [basisProjector_apply, Matrix.single, eq_comm]

theorem traceReadout_projector {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    traceReadout ρ (projector S U) = readout ρ S U := by
  unfold traceReadout projector readout Fermionic.ConditionalSector.rotated
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [basisProjector_eq_single, Matrix.trace_mul_single]
  simp

/-- The measure's orbit is exactly the full original pure Slater class. -/
theorem slater_iff_mem_range {n p : ℕ}
    (S : Index n p) (ρ : Matrix (Index n p) (Index n p) ℂ) :
    IsSlaterDensity ρ ↔ ρ ∈ Set.range (projector S) := by
  constructor
  · rintro ⟨T, V, hV⟩
    refine ⟨V * permutationUnitary (orderedPermutation S T), ?_⟩
    rw [hV]
    simp only [projector, Submonoid.coe_mul, exteriorMatrix_mul, Matrix.conjTranspose_mul]
    rw [← basis_projector_same_orbit S T]
    simp only [Matrix.mul_assoc]
  · rintro ⟨U, rfl⟩
    exact ⟨S, U, rfl⟩

theorem orbitMeasure_ae_slater {n p : ℕ} (S : Index n p) :
    ∀ᵐ P ∂orbitMeasure S, IsSlaterDensity P := by
  have hr : IsCompact (Set.range (projector S)) :=
    isCompact_range (projector_continuous S)
  have hs : MeasurableSet {P : Matrix (Index n p) (Index n p) ℂ | IsSlaterDensity P} := by
    have he : {P : Matrix (Index n p) (Index n p) ℂ | IsSlaterDensity P} =
        Set.range (projector S) := by
      ext P
      exact slater_iff_mem_range S P
    rw [he]
    exact hr.measurableSet
  apply (ae_map_iff (projector_continuous S).measurable.aemeasurable hs).mpr
  exact Filter.Eventually.of_forall (fun U => ⟨S, U, rfl⟩)

theorem orbit_readout_range {n p : ℕ}
    {ρ : Matrix (Index n p) (Index n p) ℂ} (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) :
    ∀ᵐ P ∂orbitMeasure S, traceReadout ρ P ∈ Icc (0 : ℝ) 1 := by
  apply (ae_map_iff (projector_continuous S).measurable.aemeasurable
    (measurableSet_Icc.preimage (traceReadout_continuous ρ).measurable)).mpr
  filter_upwards with U
  rw [traceReadout_projector]
  exact readout_mem_unitInterval hρ ht S U

/-- Exact orbit-integral/Haar-integral identification for the original test. -/
theorem orbit_integral_eq_haar {n p : ℕ}
    {ρ : Matrix (Index n p) (Index n p) ℂ} (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) (F : ℝ → ℝ) (hFc : ContinuousOn F (Icc (0 : ℝ) 1)) :
    (∫ P, F (traceReadout ρ P) ∂orbitMeasure S) =
      ∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n) := by
  have hi := integrable_comp_of_continuousOn_unitInterval (μ := orbitMeasure S) hFc
    (traceReadout_continuous ρ).measurable.aemeasurable (orbit_readout_range hρ ht S)
  rw [orbitMeasure, integral_map (projector_continuous S).measurable.aemeasurable
    hi.aestronglyMeasurable]
  simp only [traceReadout_projector]

/-- Complete distribution comparison in the invariant Slater-projector orbit model. -/
theorem orbit_husimi_convex_order (n p : ℕ)
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : ConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    (∫ P, F (traceReadout ρ P) ∂orbitMeasure S) ≤
      ∫ P, F (traceReadout (basisProjector S) P) ∂orbitMeasure S := by
  rw [orbit_integral_eq_haar hρ ht S F hFc,
    orbit_integral_eq_haar (basisProjector_posSemidef S) (basisProjector_trace S) S F hFc]
  exact exterior_husimi_convex_order n p ρ hρ ht S F hFc hF

theorem orbit_husimi_equality_iff (n p : ℕ)
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (S : Index n p) (F : ℝ → ℝ)
    (hFc : ContinuousOn F (Icc (0 : ℝ) 1))
    (hF : StrictConvexOn ℝ (Icc (0 : ℝ) 1) F) :
    ((∫ P, F (traceReadout ρ P) ∂orbitMeasure S) =
      ∫ P, F (traceReadout (basisProjector S) P) ∂orbitMeasure S) ↔ IsSlaterDensity ρ := by
  rw [orbit_integral_eq_haar hρ ht S F hFc,
    orbit_integral_eq_haar (basisProjector_posSemidef S) (basisProjector_trace S) S F hFc]
  exact exterior_husimi_equality_iff n p ρ hρ ht S F hFc hF

end Fermionic.SlaterMeasure
