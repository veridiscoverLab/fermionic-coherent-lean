import Fermionic.ExteriorUnitary
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
The differential of the actual exterior-power matrix representation.  Its
existence comes from the proved minor formula, not from a representation axiom.
-/

noncomputable section

open scoped Matrix.Norms.Elementwise

namespace Fermionic.ExteriorDifferential

open Fermionic.ExteriorUnitary

theorem differentiable_exteriorMatrix (n p : ℕ) :
    Differentiable ℂ (exteriorMatrix (n := n) p) := by
  apply differentiable_pi.mpr
  intro S
  apply differentiable_pi.mpr
  intro T
  simp_rw [exteriorMatrix_entry, Matrix.det_apply', Matrix.of_apply]
  apply Differentiable.fun_sum
  intro σ _
  apply Differentiable.const_mul
  intro A
  have hd : ∀ i : Fin p, DifferentiableAt ℂ
      (fun B : Matrix (Fin n) (Fin n) ℂ => B (enumerate S i) (enumerate T (σ i))) A := by
    intro i
    fun_prop
  exact (HasFDerivAt.finset_prod (fun i _ => (hd i).hasFDerivAt)).differentiableAt

/-- The genuine complex differential at the identity matrix. -/
def infinitesimal (n p : ℕ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Index n p) (Index n p) ℂ :=
  fderiv ℂ (exteriorMatrix p) 1

theorem hasFDerivAt_identity (n p : ℕ) :
    HasFDerivAt (exteriorMatrix (n := n) p) (infinitesimal n p) 1 :=
  (differentiable_exteriorMatrix n p 1).hasFDerivAt

/-- Conjugation is represented as an actual continuous complex linear map. -/
def sandwich {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix ι ι ℂ) : Matrix ι ι ℂ →L[ℂ] Matrix ι ι ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => U * A * V
      map_add' := by intros; simp only [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intros; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }

@[simp] theorem sandwich_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V A : Matrix ι ι ℂ) : sandwich U V A = U * A * V := rfl

/-- The complex differential preserves the actual matrix adjoint.  The two
conjugations are handled together, so no complex derivative of conjugation is assumed. -/
theorem infinitesimal_conjTranspose (n p : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    infinitesimal n p A.conjTranspose = (infinitesimal n p A).conjTranspose := by
  have hfun : star ∘ exteriorMatrix (n := n) p ∘ star = exteriorMatrix p := by
    funext B
    change (exteriorMatrix p B.conjTranspose).conjTranspose = exteriorMatrix p B
    rw [exteriorMatrix_conjTranspose, Matrix.conjTranspose_conjTranspose]
  have h := (hasFDerivAt_identity n p).star_star
  rw [hfun, star_one] at h
  have heq := h.unique (hasFDerivAt_identity n p)
  have hv := congrArg (fun L => L A.conjTranspose) heq
  change (infinitesimal n p A.conjTranspose.conjTranspose).conjTranspose =
    infinitesimal n p A.conjTranspose at hv
  simpa only [Matrix.conjTranspose_conjTranspose] using hv.symm

/-- Equivariance is differentiated from the same exterior representation,
simultaneously for every one-particle matrix direction. -/
theorem infinitesimal_unitary_conjugation (n p : ℕ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    infinitesimal n p (U.val * A * U.val.conjTranspose) =
      exteriorMatrix p U.val * infinitesimal n p A *
        (exteriorMatrix p U.val).conjTranspose := by
  have hUU : U.val * U.val.conjTranspose = 1 := U.property.2
  have hb : HasFDerivAt (exteriorMatrix (n := n) p) (infinitesimal n p)
      (sandwich U.val U.val.conjTranspose 1) := by
    simpa only [sandwich_apply, Matrix.mul_one, hUU] using hasFDerivAt_identity n p
  have hl := hb.comp 1 (sandwich U.val U.val.conjTranspose).hasFDerivAt
  have hr := (sandwich (exteriorMatrix p U.val)
    (exteriorMatrix p U.val.conjTranspose)).hasFDerivAt.comp 1 (hasFDerivAt_identity n p)
  have hf : exteriorMatrix p ∘ sandwich U.val U.val.conjTranspose =
      sandwich (exteriorMatrix p U.val)
        (exteriorMatrix p U.val.conjTranspose) ∘ exteriorMatrix p := by
    funext B
    simp only [Function.comp_apply, sandwich_apply, exteriorMatrix_mul]
  rw [hf] at hl
  have heq := hl.unique hr
  have hv := congrArg (fun L => L A) heq
  simpa only [ContinuousLinearMap.comp_apply, sandwich_apply,
    exteriorMatrix_conjTranspose] using hv

/-- On every actual occupancy basis vector, a diagonal infinitesimal acts by
the sum of its occupied one-particle entries. -/
theorem infinitesimal_diagonal (n p : ℕ) (a : Fin n → ℂ) :
    infinitesimal n p (Matrix.diagonal a) =
      Matrix.diagonal (fun S : Index n p => ∑ j : Fin p, a (enumerate S j)) := by
  have hp : HasDerivAt (fun t : ℂ => (1 : Matrix (Fin n) (Fin n) ℂ) +
      t • Matrix.diagonal a) (Matrix.diagonal a) 0 := by
    simpa only [one_smul] using
      ((hasDerivAt_id (0 : ℂ)).smul_const (Matrix.diagonal a)).const_add 1
  have hl := (hasFDerivAt_identity n p).comp_hasDerivAt_of_eq 0 hp
    (by simp : (1 : Matrix (Fin n) (Fin n) ℂ) = 1 + (0 : ℂ) • Matrix.diagonal a)
  have hd (t : ℂ) : (1 : Matrix (Fin n) (Fin n) ℂ) + t • Matrix.diagonal a =
      Matrix.diagonal (fun i => 1 + t * a i) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have hf : (fun t : ℂ => exteriorMatrix p (1 + t • Matrix.diagonal a)) =
      (fun t : ℂ => Matrix.diagonal
        (fun S : Index n p => ∏ j : Fin p, (1 + t * a (enumerate S j)))) := by
    funext t
    rw [hd, exteriorMatrix_diagonal]
  simp only [Function.comp_def] at hl
  rw [hf] at hl
  apply hl.unique
  apply hasDerivAt_pi.mpr
  intro S
  apply hasDerivAt_pi.mpr
  intro T
  by_cases h : S = T
  · subst T
    simp only [Matrix.diagonal_apply_eq]
    have ht : ∀ j : Fin p, HasDerivAt
        (fun t : ℂ => 1 + t * a (enumerate S j)) (a (enumerate S j)) 0 := by
      intro j
      simpa only [one_mul] using
        ((hasDerivAt_id (0 : ℂ)).mul_const (a (enumerate S j))).const_add 1
    simpa using HasDerivAt.fun_finset_prod (u := Finset.univ) (fun j _ => ht j)
  · simpa only [Matrix.diagonal, Matrix.of_apply, h, if_false] using
      hasDerivAt_const (0 : ℂ) (0 : ℂ)

/-- The actual occupation projection for a one-particle coordinate. -/
def occupation (n p : ℕ) (i : Fin n) : Matrix (Index n p) (Index n p) ℂ := by
  classical
  exact Matrix.diagonal (fun S => if i ∈ S then 1 else 0)

/-- The representation differential is exactly the original occupation matrix. -/
theorem infinitesimal_single_diag (n p : ℕ) (i : Fin n) :
    infinitesimal n p (Matrix.single i i 1) = occupation n p i := by
  classical
  rw [← Matrix.diagonal_single, infinitesimal_diagonal]
  unfold occupation
  congr 1
  funext S
  have hinj : Function.Injective (enumerate S) :=
    (Set.powersetCard.ofFinEmbEquiv.symm S).injective
  by_cases h : i ∈ S
  · obtain ⟨j, hj⟩ :=
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S i).mpr h
    change enumerate S j = i at hj
    rw [if_pos h]
    rw [Finset.sum_eq_single j]
    · rw [hj]
      exact Pi.single_eq_same i 1
    · intro k _ hkj
      have hne : enumerate S k ≠ i := fun he => hkj (hinj (he.trans hj.symm))
      simp [hne]
    · intro hjnot
      exact (hjnot (Finset.mem_univ j)).elim
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro j _
    have hne : enumerate S j ≠ i := by
      intro he
      apply h
      exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem S i).mp ⟨j, he⟩
    simp [hne]

/-- The one-particle matrix is defined from the original sector matrix, through
the actual differential.  It is not supplied as independent data. -/
def oneParticle {n p : ℕ} (ρ : Matrix (Index n p) (Index n p) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => Matrix.trace (ρ * infinitesimal n p (Matrix.single j i 1))

theorem oneParticle_isHermitian {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : ρ.IsHermitian) :
    (oneParticle ρ).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, oneParticle]
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
    ← infinitesimal_conjTranspose, Matrix.conjTranspose_single, star_one, hρ.eq]
  exact Matrix.trace_mul_comm _ _

/-- This trace identity fixes every entry and its transpose convention. -/
theorem trace_infinitesimal {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.trace (ρ * infinitesimal n p A) = Matrix.trace (oneParticle ρ * A) := by
  have hs : A = ∑ i : Fin n, ∑ j : Fin n, A i j • Matrix.single i j (1 : ℂ) := by
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using Matrix.matrix_eq_sum_single A
  conv_lhs => rw [hs]
  simp only [map_sum, map_smul, Matrix.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul]
  conv_rhs => rw [Matrix.trace]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply]
  rw [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- The diagonal is computed from the same original density matrix and all
its actual occupancy-basis diagonal entries. -/
theorem oneParticle_diag {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (i : Fin n) :
    oneParticle ρ i i = ∑ S : Index n p, ρ S S * (if i ∈ S.val then 1 else 0) := by
  classical
  simp only [oneParticle, infinitesimal_single_diag, occupation, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_diagonal]
  simp only [← Set.powersetCard.mem_coe_iff]

/-- Conjugating the original density conjugates its derived one-particle matrix
by the same one-particle unitary.  No diagonalization or positivity is assumed. -/
theorem oneParticle_unitary_conjugation {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    oneParticle ((exteriorMatrix p U.val).conjTranspose * ρ * exteriorMatrix p U.val) =
      U.val.conjTranspose * oneParticle ρ * U.val := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro A
  rw [← trace_infinitesimal]
  calc
    Matrix.trace (((exteriorMatrix p U.val).conjTranspose * ρ * exteriorMatrix p U.val) *
        infinitesimal n p A) =
        Matrix.trace (ρ * (exteriorMatrix p U.val * infinitesimal n p A *
          (exteriorMatrix p U.val).conjTranspose)) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (ρ * infinitesimal n p (U.val * A * U.val.conjTranspose)) := by
      rw [infinitesimal_unitary_conjugation]
    _ = Matrix.trace (oneParticle ρ * (U.val * A * U.val.conjTranspose)) :=
      trace_infinitesimal ρ _
    _ = Matrix.trace ((U.val.conjTranspose * oneParticle ρ * U.val) * A) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]

end Fermionic.ExteriorDifferential
