import Fermionic.ExteriorUnitary
import Fermionic.HaarConditioning
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Analysis.Complex.Order

/-! Original coordinate projections and their common unitary orbit. -/

noncomputable section
namespace Fermionic.OccupancyOrbit
open Matrix Fermionic.ExteriorUnitary
open scoped ComplexOrder

def coordinateProjection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) : Matrix ι ι ℂ :=
  Matrix.diagonal (fun i => if i ∈ s then 1 else 0)

def permutationUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) : Matrix.unitaryGroup ι ℂ := by
  refine ⟨σ⁻¹.permMatrix ℂ, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  change σ⁻¹.permMatrix ℂ * (σ⁻¹.permMatrix ℂ).conjTranspose = 1
  rw [Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul]
  simp

def occupancyPermutation {n p : ℕ} (S T : Index n p) : Equiv.Perm (Fin n) :=
  (Finset.equivOfCardEq (S.property.trans T.property.symm)).extendSubtype

theorem occupancyPermutation_mem {n p : ℕ} (S T : Index n p) (i : Fin n) :
    occupancyPermutation S T i ∈ T.val ↔ i ∈ S.val := by
  by_cases hi : i ∈ S.val
  · exact iff_of_true
      ((Finset.equivOfCardEq (S.property.trans T.property.symm)).extendSubtype_mem i hi) hi
  · exact iff_of_false
      ((Finset.equivOfCardEq (S.property.trans T.property.symm)).extendSubtype_not_mem i hi) hi

theorem permutation_conjugates_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) (σ : Equiv.Perm ι)
    (hσ : ∀ i, σ i ∈ t ↔ i ∈ s) :
    (permutationUnitary σ).val * coordinateProjection s *
      (permutationUnitary σ).val.conjTranspose = coordinateProjection t := by
  ext i j
  simp only [permutationUnitary, Matrix.conjTranspose_permMatrix, inv_inv]
  simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  change coordinateProjection s (σ.symm i) (σ.symm j) = coordinateProjection t i j
  have hi := hσ (σ.symm i)
  simp only [Equiv.apply_symm_apply] at hi
  by_cases hij : i = j
  · subst j
    simp [coordinateProjection, hi]
  · have hne : σ.symm i ≠ σ.symm j := fun h => hij (σ.symm.injective h)
    simp [coordinateProjection, Matrix.diagonal_apply_ne, hij, hne]

theorem occupancy_same_orbit {n p : ℕ} (S T : Index n p) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ,
      U.val * coordinateProjection S.val * U.val.conjTranspose =
        coordinateProjection T.val :=
  ⟨permutationUnitary (occupancyPermutation S T),
    permutation_conjugates_projection _ _ _ (occupancyPermutation_mem S T)⟩

def projectionReadout {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (i : ι) (U : Matrix.unitaryGroup ι ℂ) : ℝ :=
  ((U.val.conjTranspose * coordinateProjection s * U.val) i i).re

theorem projectionReadout_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (i : ι) (U : Matrix.unitaryGroup ι ℂ) :
    projectionReadout s i U = ∑ j ∈ s, Complex.normSq (U.val j i) := by
  simp only [projectionReadout, coordinateProjection, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp [Matrix.diagonal, Complex.normSq_apply, Complex.mul_re]

theorem projectionReadout_mem_unitInterval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (i : ι) (U : Matrix.unitaryGroup ι ℂ) :
    projectionReadout s i U ∈ Set.Icc (0 : ℝ) 1 := by
  rw [projectionReadout_eq_sum]
  constructor
  · exact Finset.sum_nonneg (fun j _ => Complex.normSq_nonneg _)
  · have hU : U.val.conjTranspose * U.val = 1 := U.property.1
    have hcol := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) hU
    have ht : ∑ j : ι, Complex.normSq (U.val j i) = 1 := by
      simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
        Complex.normSq_apply, Complex.mul_re] using hcol
    exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun j _ _ => Complex.normSq_nonneg _)).trans ht.le

theorem continuous_projectionReadout {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (i : ι) : Continuous (projectionReadout s i) := by
  change Continuous (fun U => projectionReadout s i U)
  simp_rw [projectionReadout_eq_sum]
  exact continuous_finset_sum s (fun j _ => Complex.continuous_normSq.comp
    ((continuous_apply i).comp ((continuous_apply j).comp continuous_subtype_val)))

theorem projectionReadout_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s t : Finset ι) (i : ι) (V : Matrix.unitaryGroup ι ℂ)
    (hV : V.val * coordinateProjection s * V.val.conjTranspose = coordinateProjection t)
    (U : Matrix.unitaryGroup ι ℂ) :
    projectionReadout t i U = projectionReadout s i (star V * U) := by
  simp only [projectionReadout, Submonoid.coe_mul, Unitary.coe_star,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [← hV]
  simp only [Matrix.mul_assoc]

/-- Equal-cardinality projections have identical laws on the original Haar space. -/
theorem occupancy_readout_same_law {n p : ℕ} (S T : Index n p) (i : Fin n) :
    MeasureTheory.Measure.map (projectionReadout S.val i)
        (Fermionic.HaarConditioning.unitaryHaar (Fin n)) =
      MeasureTheory.Measure.map (projectionReadout T.val i)
        (Fermionic.HaarConditioning.unitaryHaar (Fin n)) := by
  obtain ⟨V, hV⟩ := occupancy_same_orbit S T
  have hf : projectionReadout T.val i =
      fun U => projectionReadout S.val i (star V * U) := by
    funext U
    exact projectionReadout_conjugate S.val T.val i V hV U
  rw [hf]
  exact (Fermionic.HaarConditioning.map_readout_mul_left
    (continuous_projectionReadout S.val i).measurable (star V)).symm

theorem projectionReadout_permutation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (i : ι) (σ : Equiv.Perm ι) :
    projectionReadout s i (permutationUnitary σ) =
      if σ i ∈ s then (1 : ℝ) else 0 := by
  simp only [projectionReadout, permutationUnitary, Matrix.conjTranspose_permMatrix,
    inv_inv, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul,
    PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  change (coordinateProjection s (σ i) (σ i)).re = _
  by_cases h : σ i ∈ s <;> simp [coordinateProjection, h]

/-- A single fixed occupation port, with its whole unitary family, detects
every difference between the original coordinate projections. -/
theorem projectionReadout_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) : Function.Injective (fun s : Finset ι => projectionReadout s i) := by
  intro s t heq
  ext j
  have h := congrFun heq (permutationUnitary (Equiv.swap i j))
  simp only [projectionReadout_permutation, Equiv.swap_apply_left] at h
  by_cases hs : j ∈ s <;> by_cases ht : j ∈ t <;> simp_all

end Fermionic.OccupancyOrbit
