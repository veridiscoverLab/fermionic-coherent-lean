import Fermionic.ExteriorDifferential
import Fermionic.DensityRigidity
import Mathlib.Analysis.Matrix.Spectrum

/-!
One shared finite probability decomposition derived from the original density
matrix. Only its one-particle matrix is diagonalized. The density itself is
rotated by the same actual exterior representation; no diagonal-density or
independent branch decomposition is assumed.
-/

noncomputable section
namespace Fermionic.OccupationMixture

open Matrix Fermionic.ExteriorUnitary Fermionic.ExteriorDifferential
open scoped ComplexOrder

def eigenRotation {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (hρ : ρ.PosSemidef) : Matrix.unitaryGroup (Fin n) ℂ :=
  (oneParticle_isHermitian ρ hρ.isHermitian).eigenvectorUnitary

def eigenDensity {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (hρ : ρ.PosSemidef) : Matrix (Index n p) (Index n p) ℂ :=
  (exteriorMatrix p (eigenRotation ρ hρ).val).conjTranspose * ρ *
    exteriorMatrix p (eigenRotation ρ hρ).val

theorem eigenDensity_posSemidef {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) :
    (eigenDensity ρ hρ).PosSemidef := hρ.conjTranspose_mul_mul_same _

theorem eigenDensity_trace {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) :
    (eigenDensity ρ hρ).trace = ρ.trace := by
  have hU := (representation n p (eigenRotation ρ hρ)).property.2
  change exteriorMatrix p (eigenRotation ρ hρ).val *
    (exteriorMatrix p (eigenRotation ρ hρ).val).conjTranspose = 1 at hU
  rw [eigenDensity, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

theorem eigenDensity_oneParticle_diagonal {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) :
    oneParticle (eigenDensity ρ hρ) =
      Matrix.diagonal (fun i =>
        ((oneParticle_isHermitian ρ hρ.isHermitian).eigenvalues i : ℂ)) := by
  rw [eigenDensity, oneParticle_unitary_conjugation]
  simpa only [eigenRotation, Unitary.conjStarAlgAut_star_apply, Matrix.mul_assoc]
    using (oneParticle_isHermitian ρ hρ.isHermitian).conjStarAlgAut_star_eigenvectorUnitary

/-- These are the original rotated state's actual occupation probabilities. -/
def probability {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (hρ : ρ.PosSemidef) (S : Index n p) : ℝ := (eigenDensity ρ hρ S S).re

theorem probability_nonneg {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (S : Index n p) :
    0 ≤ probability ρ hρ S :=
  (Complex.nonneg_iff.mp (eigenDensity_posSemidef ρ hρ).diag_nonneg).1

theorem probability_sum {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (ht : ρ.trace = 1) : ∑ S, probability ρ hρ S = 1 := by
  have h := congrArg Complex.re ((eigenDensity_trace ρ hρ).trans ht)
  simpa only [Matrix.trace, Complex.re_sum, Complex.one_re, probability] using h

theorem probability_cast {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) (S : Index n p) :
    (probability ρ hρ S : ℂ) = eigenDensity ρ hρ S S := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp (eigenDensity_posSemidef ρ hρ).diag_nonneg).2

/-- The one-particle projection of the actual occupancy Slater vector. -/
def occupancyProjection {n p : ℕ} (S : Index n p) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => if i ∈ S.val then 1 else 0)

/-- One finite family of probabilities decomposes the complete derived
one-particle matrix. Off-diagonal entries of the original density remain in it. -/
theorem common_diagonal_mixture {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) :
    oneParticle (eigenDensity ρ hρ) =
      ∑ S : Index n p, (probability ρ hρ S : ℂ) • occupancyProjection S := by
  ext i j
  by_cases hij : i = j
  · subst j
    rw [oneParticle_diag]
    simp only [Matrix.sum_apply, Matrix.smul_apply, occupancyProjection,
      Matrix.diagonal_apply_eq, smul_eq_mul, probability_cast]
  · rw [eigenDensity_oneParticle_diagonal]
    simp only [Matrix.sum_apply, Matrix.smul_apply, occupancyProjection]
    simp [Matrix.diagonal, hij]

/-- Return to the original one-particle coordinates with that same family. -/
theorem common_projection_mixture {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef) :
    oneParticle ρ = ∑ S : Index n p, (probability ρ hρ S : ℂ) •
      ((eigenRotation ρ hρ).val * occupancyProjection S *
        (eigenRotation ρ hρ).val.conjTranspose) := by
  have hd := common_diagonal_mixture ρ hρ
  rw [eigenDensity, oneParticle_unitary_conjugation] at hd
  have hv := congrArg (fun A => (eigenRotation ρ hρ).val * A *
    (eigenRotation ρ hρ).val.conjTranspose) hd
  have hU : (eigenRotation ρ hρ).val *
      (eigenRotation ρ hρ).val.conjTranspose = 1 := (eigenRotation ρ hρ).property.2
  have hr : (eigenRotation ρ hρ).val *
      ((eigenRotation ρ hρ).val.conjTranspose * oneParticle ρ *
        (eigenRotation ρ hρ).val) * (eigenRotation ρ hρ).val.conjTranspose =
      oneParticle ρ := by
    calc
      _ = ((eigenRotation ρ hρ).val * (eigenRotation ρ hρ).val.conjTranspose) *
          oneParticle ρ *
          ((eigenRotation ρ hρ).val * (eigenRotation ρ hρ).val.conjTranspose) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]; simp
  dsimp only at hv
  rw [hr] at hv
  simpa only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul] using hv

def oneParticleReadout {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ)
    (i : Fin n) (U : Matrix.unitaryGroup (Fin n) ℂ) : ℝ :=
  ((U.val.conjTranspose * oneParticle ρ * U.val) i i).re

/-- All directions use the same weights and the same spectral rotation. -/
theorem common_readout_mixture {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.PosSemidef)
    (i : Fin n) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    oneParticleReadout ρ i U = ∑ S : Index n p, probability ρ hρ S *
      ((U.val.conjTranspose * (eigenRotation ρ hρ).val * occupancyProjection S *
        (eigenRotation ρ hρ).val.conjTranspose * U.val) i i).re := by
  rw [oneParticleReadout, common_projection_mixture ρ hρ]
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Matrix.mul_assoc]

end Fermionic.OccupationMixture
