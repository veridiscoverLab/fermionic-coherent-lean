import Fermionic.OccupancyOrbit
import Fermionic.DensityRigidity

/-! Exact transport of the original occupancy wedges by one-particle unitaries. -/

noncomputable section
namespace Fermionic.SlaterOrbit
open Matrix Fermionic.ExteriorUnitary Fermionic.OccupancyOrbit
open Set.powersetCard

/-- Match the increasing occupied lists, then extend to the full one-particle space. -/
def orderedPermutation {n p : ℕ} (S T : Index n p) : Equiv.Perm (Fin n) :=
  ((orderIsoOfFin S).toEquiv.symm.trans (orderIsoOfFin T).toEquiv).extendSubtype

theorem orderedPermutation_enumerate {n p : ℕ} (S T : Index n p) (i : Fin p) :
    orderedPermutation S T (enumerate S i) = enumerate T i := by
  have hm : enumerate S i ∈ S.val := by
    change Finset.orderEmbOfFin S.val S.property i ∈ S.val
    exact Finset.orderEmbOfFin_mem _ _ _
  rw [orderedPermutation, Equiv.extendSubtype_apply_of_mem _ _ hm]
  change (((orderIsoOfFin S).toEquiv.symm.trans (orderIsoOfFin T).toEquiv)
    ((orderIsoOfFin S).toEquiv i)).val = _
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem permutation_basis_vector {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Matrix.toLin' (permutationUnitary σ).val (Pi.basisFun ℂ (Fin n) i) =
      Pi.basisFun ℂ (Fin n) (σ i) := by
  ext j
  simp only [Matrix.toLin'_apply, permutationUnitary, Matrix.permMatrix_mulVec,
    Pi.basisFun_apply, Function.comp_apply, Pi.single_apply]
  change (if (σ⁻¹) j = i then (1 : ℂ) else 0) = if j = σ i then 1 else 0
  have he : (σ⁻¹) j = i ↔ j = σ i := σ.symm_apply_eq
  simp only [he]

/-- No arbitrary phase remains: occupied lists are matched in increasing order. -/
theorem ordered_permutation_wedge {n p : ℕ} (S T : Index n p) :
    exteriorPower.map p (Matrix.toLin' (permutationUnitary (orderedPermutation S T)).val)
      (basis n p S) = basis n p T := by
  change exteriorPower.map p
    (Matrix.toLin' (permutationUnitary (orderedPermutation S T)).val)
    ((Pi.basisFun ℂ (Fin n)).exteriorPower p S) =
      (Pi.basisFun ℂ (Fin n)).exteriorPower p T
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family,
    exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext i
  change Matrix.toLin' (permutationUnitary (orderedPermutation S T)).val
    (Pi.basisFun ℂ (Fin n) (enumerate S i)) = Pi.basisFun ℂ (Fin n) (enumerate T i)
  rw [permutation_basis_vector, orderedPermutation_enumerate]

theorem ordered_permutation_column {n p : ℕ} (S T : Index n p) (R : Index n p) :
    exteriorMatrix p (permutationUnitary (orderedPermutation S T)).val R S =
      if R = T then 1 else 0 := by
  rw [exteriorMatrix, LinearMap.toMatrix_apply, ordered_permutation_wedge,
    Module.Basis.repr_self]
  simp [Finsupp.single_apply, eq_comm]

/-- All normalized occupancy projectors belong to the same original Slater orbit. -/
theorem basis_projector_same_orbit {n p : ℕ} (S T : Index n p) :
    exteriorMatrix p (permutationUnitary (orderedPermutation S T)).val *
        Fermionic.DensityRigidity.basisProjector S *
        (exteriorMatrix p (permutationUnitary (orderedPermutation S T)).val).conjTranspose =
      Fermionic.DensityRigidity.basisProjector T := by
  ext R Q
  simp only [Matrix.mul_apply, Fermionic.DensityRigidity.basisProjector_apply,
    Matrix.conjTranspose_apply]
  simp only [ite_and, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, ordered_permutation_column]
  by_cases hR : R = T <;> by_cases hQ : Q = T <;>
    simp [hR, hQ, ordered_permutation_column]

end Fermionic.SlaterOrbit
