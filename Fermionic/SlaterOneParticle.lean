import Fermionic.OccupationMixture
import Fermionic.SlaterOrbit

/-! The one-particle matrix of an original Slater occupancy projector. -/

noncomputable section
namespace Fermionic.SlaterOneParticle
open Matrix Fermionic.ExteriorUnitary Fermionic.ExteriorDifferential
open Fermionic.DensityRigidity Fermionic.OccupationMixture
open scoped ComplexOrder

def signUnitary {n : ℕ} (i : Fin n) : Matrix.unitaryGroup (Fin n) ℂ := by
  refine ⟨Matrix.diagonal (fun j => if j = i then (-1 : ℂ) else 1), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff]
  change Matrix.diagonal (fun j => if j = i then (-1 : ℂ) else 1) *
    (Matrix.diagonal (fun j => if j = i then (-1 : ℂ) else 1)).conjTranspose = 1
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  ext j k
  by_cases hk : j = k
  · subst k
    by_cases hj : j = i <;> simp [hj]
  · simp [Matrix.diagonal, hk]

theorem diagonal_unitary_preserves_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (d : ι → ℂ) (hU : U.val = Matrix.diagonal d)
    (S : ι) : U.val.conjTranspose * basisProjector S * U.val = basisProjector S := by
  have hnorm : star (d S) * d S = 1 := by
    have h := congrArg (fun A : Matrix ι ι ℂ => A S S) U.property.1
    simpa [hU] using h
  rw [hU]
  ext j k
  change (starRingEnd ℂ) (d S) * d S = 1 at hnorm
  simp only [basisProjector, Matrix.vecMulVec, Matrix.diagonal_conjTranspose]
  by_cases hj : j = S <;> by_cases hk : k = S <;>
    simp [Pi.single_apply, hj, hk, hnorm]

theorem sign_preserves_basis {n p : ℕ} (S : Index n p) (i : Fin n) :
    (exteriorMatrix p (signUnitary i).val).conjTranspose * basisProjector S *
      exteriorMatrix p (signUnitary i).val = basisProjector S := by
  exact diagonal_unitary_preserves_basis (representation n p (signUnitary i)) _
    (exteriorMatrix_diagonal p _) S

theorem oneParticle_basisProjector {n p : ℕ} (S : Index n p) :
    oneParticle (basisProjector S) = occupancyProjection S := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [oneParticle_diag]
    simp only [basisProjector_apply, occupancyProjection, Matrix.diagonal_apply_eq]
    simp only [and_self, ite_mul, one_mul, zero_mul]
    simp
  · have hc := oneParticle_unitary_conjugation (basisProjector S) (signUnitary i)
    rw [sign_preserves_basis] at hc
    have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A i j) hc
    simp only [signUnitary, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul, Matrix.mul_diagonal] at he
    have hji : j ≠ i := Ne.symm hij
    simp only [Pi.star_apply, ite_true, if_neg hji, star_neg, star_one,
      neg_one_mul, mul_one] at he
    have hz : oneParticle (basisProjector S) i j = 0 := by
      have hsum : oneParticle (basisProjector S) i j + oneParticle (basisProjector S) i j = 0 :=
        eq_neg_iff_add_eq_zero.mp he
      exact (add_self_eq_zero.mp hsum)
    simpa [occupancyProjection, Matrix.diagonal, hij] using hz

end Fermionic.SlaterOneParticle
