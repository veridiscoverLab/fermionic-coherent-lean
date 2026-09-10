import Fermionic.ConditionalSector
import Fermionic.SlaterOrbit
import Mathlib.Tactic.FunProp

/-!
# Actual exterior-sector Husimi readouts and double-Haar conditioning

Every readout is an entry of the same full density matrix rotated by the
actual exterior-power representation. The measure is the normalized Haar
measure of the original one-particle unitary group.
-/

noncomputable section

namespace Fermionic.ExteriorHusimi

open Matrix MeasureTheory Set
open Fermionic.ExteriorUnitary Fermionic.ConditionalSector Fermionic.HaarConditioning
open Fermionic.DensityRigidity Fermionic.SlaterOrbit Fermionic.OccupancyOrbit
open scoped ComplexOrder

/-- The actual Husimi function, with an arbitrary original occupancy reference. -/
def readout {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (S : Index n p) (U : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  (rotated n p ρ U S S).re

theorem readout_continuous {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p) :
    Continuous (readout ρ S) := by
  have hR : Continuous (fun U : Matrix.unitaryGroup (Fin n) ℂ =>
      exteriorMatrix p U.val) := (continuous_exteriorMatrix n p).comp continuous_subtype_val
  unfold readout rotated
  fun_prop

theorem readout_mem_unitInterval {n p : ℕ}
    {ρ : Matrix (Index n p) (Index n p) ℂ} (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) (S : Index n p) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    readout ρ S U ∈ Icc (0 : ℝ) 1 := by
  have hA := rotated_posSemidef n p hρ U
  have hnonneg (T : Index n p) : 0 ≤ (rotated n p ρ U T T).re :=
    (Complex.nonneg_iff.mp hA.diag_nonneg).1
  constructor
  · exact hnonneg S
  · have hle := Finset.single_le_sum (fun T (_ : T ∈ Finset.univ) => hnonneg T)
      (Finset.mem_univ S)
    have htrace := congrArg Complex.re ((rotated_trace n p ρ U).trans ht)
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Complex.one_re] at htrace
    exact hle.trans_eq htrace

theorem continuous_test_readout {n p : ℕ}
    {ρ : Matrix (Index n p) (Index n p) ℂ} (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) (S : Index n p) {F : ℝ → ℝ}
    (hF : ContinuousOn F (Icc (0 : ℝ) 1)) : Continuous (fun U => F (readout ρ S U)) :=
  hF.comp_continuous (readout_continuous ρ S) (readout_mem_unitInterval hρ ht S)

theorem quadratic_basis {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i : I) :
    quadratic A (Pi.single i 1) = (A i i).re := by
  simp [quadratic, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem readout_eq_quadratic {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    readout ρ S U = quadratic ρ (exteriorMatrix p U.val *ᵥ Pi.single S 1) := by
  rw [quadratic_compression, quadratic_basis]
  rfl

theorem creation_basis (M p : ℕ) (S : Index M p) :
    creation M p *ᵥ Pi.single S 1 = Pi.single (insertFirst S) 1 := by
  ext T
  simp [creation, basisInclusion, Matrix.mulVec, dotProduct, Pi.single_apply, eq_comm]

theorem basisProjector_posSemidef {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    (basisProjector i).PosSemidef := Matrix.posSemidef_vecMulVec_self_star _

@[simp] theorem basisProjector_trace {I : Type*} [Fintype I] [DecidableEq I] (i : I) :
    (basisProjector i).trace = 1 := by
  simp [Matrix.trace, basisProjector_apply]

@[simp] theorem readout_basisProjector_one {n p : ℕ} (S : Index n p) :
    readout (basisProjector S) S 1 = 1 := by
  simp [readout, rotated, exteriorMatrix_one, basisProjector_apply]

/-- The coherent law puts positive mass on positive readouts.  The identity
group element is an actual positive witness, and Haar has full support. -/
theorem coherent_readout_positive_mass {n p : ℕ} (S : Index n p) :
    Measure.map (readout (basisProjector S) S) (unitaryHaar (Fin n)) (Ioi (0 : ℝ)) ≠ 0 :=
  map_readout_positive_mass (readout_continuous _ S)
    (by rw [readout_basisProjector_one]; exact zero_lt_one)

theorem orderedPermutation_mul_basis {n p : ℕ} (S T : Index n p) :
    exteriorMatrix p (permutationUnitary (orderedPermutation S T)).val *ᵥ Pi.single S 1 =
      Pi.single T 1 := by
  ext R
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, ordered_permutation_column, eq_comm]

/-- Changing the occupancy reference is an actual right translation of the
original one-particle unitary, with no phase or matrix-entry convention omitted. -/
theorem readout_reference_translate {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S T : Index n p)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    readout ρ S (U * permutationUnitary (orderedPermutation S T)) = readout ρ T U := by
  rw [readout_eq_quadratic, readout_eq_quadratic]
  simp only [Submonoid.coe_mul, exteriorMatrix_mul, ← Matrix.mulVec_mulVec,
    orderedPermutation_mul_basis]

theorem readout_reference_same_law {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S T : Index n p) :
    Measure.map (readout ρ S) (unitaryHaar (Fin n)) =
      Measure.map (readout ρ T) (unitaryHaar (Fin n)) := by
  have h := map_readout_mul_right (readout_continuous ρ S).measurable
    (permutationUnitary (orderedPermutation S T))
  simp_rw [readout_reference_translate] at h
  exact h.symm

theorem integral_readout_reference {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S T : Index n p) (F : ℝ → ℝ) :
    (∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout ρ T U) ∂unitaryHaar (Fin n) := by
  have h := integral_mul_right_eq_self (μ := unitaryHaar (Fin n))
    (fun U => F (readout ρ S U)) (permutationUnitary (orderedPermutation S T))
  simp_rw [readout_reference_translate] at h
  exact h.symm

theorem readout_rotated {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (V U : Matrix.unitaryGroup (Fin n) ℂ) :
    readout (rotated n p ρ V) S U = readout ρ S (V * U) := by
  simp only [readout, rotated, Submonoid.coe_mul, exteriorMatrix_mul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Rotating the same original density preserves its complete Haar readout law. -/
theorem readout_rotated_same_law {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    Measure.map (readout (rotated n p ρ V) S) (unitaryHaar (Fin n)) =
      Measure.map (readout ρ S) (unitaryHaar (Fin n)) := by
  change Measure.map (fun U => readout (rotated n p ρ V) S U) _ = _
  simp_rw [readout_rotated]
  exact map_readout_mul_left (readout_continuous ρ S).measurable V

theorem integral_readout_rotated {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (V : Matrix.unitaryGroup (Fin n) ℂ) (F : ℝ → ℝ) :
    (∫ U, F (readout (rotated n p ρ V) S U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n) := by
  simp_rw [readout_rotated]
  exact integral_mul_left_eq_self (μ := unitaryHaar (Fin n))
    (fun U => F (readout ρ S U)) V

theorem readout_forward_rotated_same_law {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (V : Matrix.unitaryGroup (Fin n) ℂ) :
    Measure.map (readout
        (exteriorMatrix p V.val * ρ * (exteriorMatrix p V.val).conjTranspose) S)
        (unitaryHaar (Fin n)) =
      Measure.map (readout ρ S) (unitaryHaar (Fin n)) := by
  simpa only [rotated, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    exteriorMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose] using
    readout_rotated_same_law ρ S (star V)

theorem integral_readout_forward_rotated {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (S : Index n p)
    (V : Matrix.unitaryGroup (Fin n) ℂ) (F : ℝ → ℝ) :
    (∫ U, F (readout
        (exteriorMatrix p V.val * ρ * (exteriorMatrix p V.val).conjTranspose) S U)
        ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout ρ S U) ∂unitaryHaar (Fin n) := by
  simpa only [rotated, Unitary.coe_star, Matrix.star_eq_conjTranspose,
    exteriorMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose] using
    integral_readout_rotated ρ S (star V) F

/-- All pure occupancy inputs induce the same full Husimi distribution. -/
theorem readout_coherent_input_same_law {n p : ℕ} (R S T : Index n p) :
    Measure.map (readout (basisProjector S) R) (unitaryHaar (Fin n)) =
      Measure.map (readout (basisProjector T) R) (unitaryHaar (Fin n)) := by
  have h := readout_forward_rotated_same_law (basisProjector S) R
    (permutationUnitary (orderedPermutation S T))
  rw [basis_projector_same_orbit] at h
  exact h.symm

theorem integral_readout_coherent_input {n p : ℕ} (R S T : Index n p) (F : ℝ → ℝ) :
    (∫ U, F (readout (basisProjector S) R U) ∂unitaryHaar (Fin n)) =
      ∫ U, F (readout (basisProjector T) R U) ∂unitaryHaar (Fin n) := by
  have h := integral_readout_forward_rotated (basisProjector S) R
    (permutationUnitary (orderedPermutation S T)) F
  rw [basis_projector_same_orbit] at h
  exact h.symm

/-- Pointwise conditional identity for the original occupancy reference. -/
theorem readout_conditional (M p : ℕ)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (S : Index M p) (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (V : Matrix.unitaryGroup (Fin M) ℂ) :
    readout ρ (insertFirst S) (U * fixFirstFinHom M V) =
      readout (conditionalMatrix M p ρ U) S V := by
  rw [readout_eq_quadratic, readout_eq_quadratic, ← creation_basis,
    conditional_readout]

theorem readout_conditional_normalized (M p : ℕ)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (S : Index M p) (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (ha : weight (conditionalMatrix M p ρ U) ≠ 0)
    (V : Matrix.unitaryGroup (Fin M) ℂ) :
    readout ρ (insertFirst S) (U * fixFirstFinHom M V) =
      weight (conditionalMatrix M p ρ U) *
        readout (normalized (conditionalMatrix M p ρ U)) S V := by
  rw [readout_eq_quadratic, readout_eq_quadratic, ← creation_basis,
    conditional_readout_normalized M p ρ U ha]

theorem readout_conditional_zero (M p : ℕ)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (S : Index M p)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (ha : weight (conditionalMatrix M p ρ U) = 0)
    (V : Matrix.unitaryGroup (Fin M) ℂ) :
    readout ρ (insertFirst S) (U * fixFirstFinHom M V) = 0 := by
  rw [readout_eq_quadratic, ← creation_basis]
  exact conditional_readout_zero M p hρ U ha V (Pi.single S 1)

/-- The true Haar conditioning formula retains outer Haar mass one and all
cross entries of the original conditional density. -/
theorem integral_conditional (M p : ℕ)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (ht : ρ.trace = 1) (S : Index M p)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc (0 : ℝ) 1)) :
    (∫ U, F (readout ρ (insertFirst S) U) ∂unitaryHaar (Fin (M + 1))) =
      ∫ U, ∫ V, F (readout (conditionalMatrix M p ρ U) S V)
        ∂unitaryHaar (Fin M) ∂unitaryHaar (Fin (M + 1)) := by
  rw [unitary_fin_integral_eq_double M _ (continuous_test_readout hρ ht _ hF)]
  simp_rw [readout_conditional]

theorem readout_eq_one_of_subsingleton {n p : ℕ} [Subsingleton (Index n p)]
    (ρ : Matrix (Index n p) (Index n p) ℂ) (ht : ρ.trace = 1)
    (S : Index n p) (U : Matrix.unitaryGroup (Fin n) ℂ) : readout ρ S U = 1 := by
  have htrace : (rotated n p ρ U).trace = rotated n p ρ U S S := by
    change ∑ T, rotated n p ρ U T T = _
    apply Finset.sum_eq_single S
    · intro T _ hTS
      exact False.elim (hTS (Subsingleton.elim T S))
    · simp
  rw [readout, ← htrace, rotated_trace, ht]
  rfl

/-- The zero-particle sector is one dimensional and gives the constant
readout one for every original trace-one state. -/
theorem readout_zero_particles (n : ℕ)
    (ρ : Matrix (Index n 0) (Index n 0) ℂ) (ht : ρ.trace = 1)
    (S : Index n 0) (U : Matrix.unitaryGroup (Fin n) ℂ) : readout ρ S U = 1 := by
  haveI : Subsingleton (Index n 0) := ⟨fun S T => Subtype.ext
    ((Finset.card_eq_zero.mp S.property).trans (Finset.card_eq_zero.mp T.property).symm)⟩
  exact readout_eq_one_of_subsingleton ρ ht S U

/-- The completely filled sector has the same constant readout, including
the zero-mode boundary. -/
theorem readout_filled_sector (n : ℕ)
    (ρ : Matrix (Index n n) (Index n n) ℂ) (ht : ρ.trace = 1)
    (S : Index n n) (U : Matrix.unitaryGroup (Fin n) ℂ) : readout ρ S U = 1 := by
  have heq (T : Index n n) : T.val = Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simp)
  haveI : Subsingleton (Index n n) := ⟨fun S T => Subtype.ext ((heq S).trans (heq T).symm)⟩
  exact readout_eq_one_of_subsingleton ρ ht S U

end Fermionic.ExteriorHusimi
