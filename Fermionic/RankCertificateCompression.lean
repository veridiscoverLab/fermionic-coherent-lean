import Fermionic.RankCertificateNormal
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Exact common-projector compression of the sixteen-dimensional central
block. The two projectors are fixed on the same four-dimensional multiplicity
space; no parameter-dependent eigenspaces or separate Gram objects are used. -/
namespace Fermionic.RankCertificate
noncomputable section
open scoped Kronecker

def commonP : Matrix (Fin 4) (Fin 4) ℂ := fun _ _ => 1/4

def commonQ : Matrix (Fin 4) (Fin 4) ℂ := 1 - commonP

lemma commonP_sq : commonP * commonP = commonP := by
  ext i j
  norm_num [commonP, Matrix.mul_apply, Fin.sum_univ_succ]

lemma commonP_add_commonQ : commonP + commonQ = 1 := by
  unfold commonQ
  abel

lemma commonPQ : commonP * commonQ = 0 := by
  simp [commonQ, mul_sub, commonP_sq]

lemma commonQP : commonQ * commonP = 0 := by
  simp [commonQ, sub_mul, commonP_sq]

lemma commonQ_sq : commonQ * commonQ = commonQ := by
  calc
    commonQ * commonQ = commonQ * (1 - commonP) := rfl
    _ = commonQ := by rw [mul_sub, mul_one, commonQP, sub_zero]

lemma trace_commonP : Matrix.trace commonP = 1 := by
  norm_num [Matrix.trace, commonP, Fin.sum_univ_succ]

lemma trace_commonQ : Matrix.trace commonQ = 3 := by
  norm_num [commonQ, Matrix.trace_sub, trace_commonP]

def centralCompression (T R : Matrix (Fin 4) (Fin 4) ℂ) :
    Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ :=
  T ⊗ₖ commonQ + R ⊗ₖ commonP

lemma centralCompression_pow_succ (T R : Matrix (Fin 4) (Fin 4) ℂ) (k : ℕ) :
    centralCompression T R ^ (k+1) =
      (T^(k+1)) ⊗ₖ commonQ + (R^(k+1)) ⊗ₖ commonP := by
  induction k with
  | zero => simp [centralCompression]
  | succ k ih =>
    rw [pow_succ, ih]
    unfold centralCompression
    simp only [add_mul, mul_add, ← Matrix.mul_kronecker_mul,
      commonP_sq, commonQ_sq, commonPQ, commonQP,
      Matrix.kronecker_zero, zero_add, add_zero, ← pow_succ]

theorem centralCompression_trace_power
    (T R : Matrix (Fin 4) (Fin 4) ℂ) (k : ℕ) (hk : 0 < k) :
    Matrix.trace (centralCompression T R ^ k) =
      3 * Matrix.trace (T^k) + Matrix.trace (R^k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hk)
  rw [centralCompression_pow_succ, Matrix.trace_add,
    Matrix.trace_kronecker, Matrix.trace_kronecker,
    trace_commonQ, trace_commonP]
  ring

def normalFullBlock (x y z : ℂ) :
    Matrix (Fin 8 ⊕ ((Fin 4 × Fin 24) ⊕ (Fin 4 × Fin 4)))
      (Fin 8 ⊕ ((Fin 4 × Fin 24) ⊕ (Fin 4 × Fin 4))) ℂ :=
  Matrix.fromBlocks 0 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal (fun _ : Fin 24 => normalT x y z))
      0 0 (centralCompression (normalT x y z) (normalR x y z)))

lemma trace_from_blocks_complex {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℂ) (D : Matrix m m ℂ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.fromBlocks, Fintype.sum_sum_type]

theorem normalFullBlock_trace_power (x y z : ℂ) (k : ℕ) (hk : 0 < k) :
    Matrix.trace (normalFullBlock x y z ^ k) =
      27 * Matrix.trace (normalT x y z ^ k) + Matrix.trace (normalR x y z ^ k) := by
  simp only [normalFullBlock, Matrix.fromBlocks_diagonal_pow,
    trace_from_blocks_complex, ← Matrix.blockDiagonal_pow,
    Matrix.trace_blockDiagonal, Pi.pow_apply]
  rw [centralCompression_trace_power _ _ k hk]
  simp [zero_pow (by omega : k ≠ 0)]
  ring

theorem normalFullBlock_certificate (x y z : ℂ) :
    invariant16 (x+y+z) (Matrix.trace (normalFullBlock x y z ^ 4))
      (Matrix.trace (normalFullBlock x y z ^ 6)) = 0 := by
  rw [normalFullBlock_trace_power x y z 4 (by omega),
    normalFullBlock_trace_power x y z 6 (by omega)]
  exact normal_four_matrix_certificate x y z

end
end Fermionic.RankCertificate
#print axioms Fermionic.RankCertificate.centralCompression_trace_power
#print axioms Fermionic.RankCertificate.normalFullBlock_certificate
