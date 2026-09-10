import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.FunProp

/-!
The actual exterior-power representation in its standard orthonormal-coordinate
model. Matrix entries are proved to be the minors of the original one-particle
matrix; the representation is not specified through abstract axioms.
-/

noncomputable section
namespace Fermionic.ExteriorUnitary

open Module
open Set.powersetCard

abbrev Index (n p : ℕ) := Set.powersetCard (Fin n) p
abbrev AlgebraicSector (n p : ℕ) := ⋀[ℂ]^p (Fin n → ℂ)
abbrev Sector (n p : ℕ) := EuclideanSpace ℂ (Index n p)

def basis (n p : ℕ) : Basis (Index n p) ℂ (AlgebraicSector n p) :=
  (Pi.basisFun ℂ (Fin n)).exteriorPower p

/-- This fixes the Hilbert structure: the increasing occupancy wedges map
to the standard orthonormal vectors of the Euclidean coordinate space. -/
def coordinates (n p : ℕ) : AlgebraicSector n p ≃ₗ[ℂ] Sector n p :=
  (basis n p).equivFun.trans (WithLp.linearEquiv 2 ℂ (Index n p → ℂ)).symm

theorem coordinates_basis (n p : ℕ) (S : Index n p) :
    coordinates n p (basis n p S) = EuclideanSpace.single S (1 : ℂ) := by
  apply (WithLp.linearEquiv 2 ℂ (Index n p → ℂ)).injective
  funext T
  simp [coordinates, EuclideanSpace.single, Finsupp.single_apply, eq_comm]

def exteriorMatrix {n : ℕ} (p : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Index n p) (Index n p) ℂ :=
  LinearMap.toMatrix (basis n p) (basis n p) (exteriorPower.map p (Matrix.toLin' A))

/-- Exact transport from the original exterior-power linear map to its
Euclidean coordinate matrix. -/
theorem coordinates_intertwine {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (s : AlgebraicSector n p) :
    coordinates n p (exteriorPower.map p (Matrix.toLin' A) s) =
      Matrix.toEuclideanLin (exteriorMatrix p A) (coordinates n p s) := by
  apply (WithLp.linearEquiv 2 ℂ (Index n p → ℂ)).injective
  change (basis n p).equivFun (exteriorPower.map p (Matrix.toLin' A) s) =
    Matrix.mulVec (exteriorMatrix p A) ((basis n p).equivFun s)
  simp only [Basis.equivFun_apply, exteriorMatrix]
  exact (LinearMap.toMatrix_mulVec_repr (basis n p) (basis n p) _ s).symm

theorem exteriorMatrix_mul {n : ℕ} (p : ℕ) (A B : Matrix (Fin n) (Fin n) ℂ) :
    exteriorMatrix p (A * B) = exteriorMatrix p A * exteriorMatrix p B := by
  unfold exteriorMatrix
  rw [Matrix.toLin'_mul, exteriorPower.map_comp]
  exact LinearMap.toMatrix_comp (basis n p) (basis n p) (basis n p) _ _

@[simp] theorem exteriorMatrix_one (n p : ℕ) :
    exteriorMatrix p (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  unfold exteriorMatrix
  rw [Matrix.toLin'_one, exteriorPower.map_id]
  exact LinearMap.toMatrix_one _

/-- Indices in an occupancy set are enumerated increasingly. -/
def enumerate {n p : ℕ} (S : Index n p) : Fin p → Fin n :=
  ofFinEmbEquiv.symm S

theorem diagonal_on_basis {n p : ℕ} (d : Fin n → ℂ) (S : Index n p) :
    exteriorPower.map p (Matrix.toLin' (Matrix.diagonal d)) (basis n p S) =
      (∏ i : Fin p, d (enumerate S i)) • basis n p S := by
  change exteriorPower.map p (Matrix.toLin' (Matrix.diagonal d))
    ((Pi.basisFun ℂ (Fin n)).exteriorPower p S) = _
  rw [exteriorPower.basis_apply, exteriorPower.map_apply_ιMulti_family]
  unfold exteriorPower.ιMulti_family
  have hv : (Matrix.toLin' (Matrix.diagonal d) ∘ Pi.basisFun ℂ (Fin n)) ∘
      (ofFinEmbEquiv.symm S) =
      fun i : Fin p => d (enumerate S i) • Pi.basisFun ℂ (Fin n) (enumerate S i) := by
    funext i
    ext j
    simp [Function.comp_def, enumerate, Matrix.toLin'_apply, Pi.basisFun_apply,
      Pi.single_apply]
  rw [hv]
  simpa only [basis, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
    enumerate, Function.comp_def] using
    (exteriorPower.ιMulti ℂ p (M := Fin n → ℂ)).toMultilinearMap.map_smul_univ
    (fun i : Fin p => d (enumerate S i))
    (fun i : Fin p => Pi.basisFun ℂ (Fin n) (enumerate S i))

theorem exteriorMatrix_diagonal {n : ℕ} (p : ℕ) (d : Fin n → ℂ) :
    exteriorMatrix p (Matrix.diagonal d) =
      Matrix.diagonal (fun S : Index n p => ∏ i : Fin p, d (enumerate S i)) := by
  ext S T
  rw [exteriorMatrix, LinearMap.toMatrix_apply, diagonal_on_basis]
  by_cases h : S = T <;> simp [h, map_smul, Basis.repr_self]

/-- The transpose-minor convention matches the dual exterior basis exactly. -/
theorem exteriorMatrix_entry {n p : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (S T : Index n p) :
    exteriorMatrix p A S T =
      (Matrix.of fun i j : Fin p => A (enumerate S j) (enumerate T i)).det := by
  unfold exteriorMatrix
  rw [LinearMap.toMatrix_apply]
  change ((Pi.basisFun ℂ (Fin n)).exteriorPower p).repr
    (exteriorPower.map p (Matrix.toLin' A)
      ((Pi.basisFun ℂ (Fin n)).exteriorPower p T)) S = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family]
  unfold exteriorPower.ιMulti_family
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  congr 1
  ext i j
  simp [enumerate, Function.comp_def, Matrix.toLin'_apply, Pi.basisFun_apply]

theorem exteriorMatrix_conjTranspose {n : ℕ} (p : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    exteriorMatrix p A.conjTranspose = (exteriorMatrix p A).conjTranspose := by
  ext S T
  rw [exteriorMatrix_entry, Matrix.conjTranspose_apply, exteriorMatrix_entry,
    ← Matrix.det_conjTranspose]
  congr 1

theorem exteriorMatrix_mem_unitary {n : ℕ} (p : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    exteriorMatrix p A ∈ Matrix.unitaryGroup (Index n p) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  change exteriorMatrix p A * (exteriorMatrix p A).conjTranspose = 1
  rw [← exteriorMatrix_conjTranspose, ← exteriorMatrix_mul]
  exact (congrArg (exteriorMatrix p) hA).trans (exteriorMatrix_one n p)

/-- The original one-particle unitary group acts on the full p-particle sector. -/
def representation (n p : ℕ) :
    Matrix.unitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Index n p) ℂ where
  toFun U := ⟨exteriorMatrix p U.val, exteriorMatrix_mem_unitary p U.val U.property⟩
  map_one' := Subtype.ext (exteriorMatrix_one n p)
  map_mul' U V := Subtype.ext (exteriorMatrix_mul p U.val V.val)

theorem continuous_exteriorMatrix (n p : ℕ) :
    Continuous (exteriorMatrix (n := n) p) := by
  apply continuous_pi
  intro S
  apply continuous_pi
  intro T
  simp_rw [exteriorMatrix_entry]
  change Continuous (fun A : Matrix (Fin n) (Fin n) ℂ =>
    Matrix.det (fun i j : Fin p => A (enumerate S j) (enumerate T i)))
  fun_prop

theorem continuous_representation (n p : ℕ) : Continuous (representation n p) := by
  exact (continuous_exteriorMatrix n p).comp continuous_subtype_val |>.subtype_mk _

end Fermionic.ExteriorUnitary
