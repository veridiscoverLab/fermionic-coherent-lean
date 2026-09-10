import Fermionic.RankCertificate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases

/-! Exact full-parameter trace certificate for the two concrete 4 by 4
matrices in the complete normal three-spinor Gram reduction.
The full 120 by 120 reduction and the geometric normal form are separate
obligations; no pure-spinor vanishing theorem is assumed here. -/

namespace Fermionic.RankCertificate

noncomputable section

def normalT (x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![x+y+z,z,z,2*z;
     -y,0,0,-z;
     -y,0,0,-z;
     2*y,y,y,x+y+z]

def normalR (x y z : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![x+y+z,-3*z,-3*z,-6*z;
     3*y,2*(x+y+z),2*(x+y+z),3*z;
     3*y,2*(x+y+z),2*(x+y+z),3*z;
     -6*y,-3*y,-3*y,x+y+z]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem normalT_recurrence (x y z : ℂ) :
    normalT x y z ^ 4 =
      (2*(x+y+z)) • normalT x y z ^ 3 +
      (-(x+y+z)^2) • normalT x y z ^ 2 +
      (4*x*y*z) • normalT x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalT, Matrix.mul_apply, pow_succ, Fin.sum_univ_succ] <;> ring

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem normalR_recurrence (x y z : ℂ) :
    normalR x y z ^ 4 =
      (6*(x+y+z)) • normalR x y z ^ 3 +
      (-9*(x+y+z)^2) • normalR x y z ^ 2 +
      (4*(x+y+z)^3-108*x*y*z) • normalR x y z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalR, Matrix.mul_apply, pow_succ, Fin.sum_univ_succ] <;> ring

theorem normalT_trace_one (x y z : ℂ) :
    Matrix.trace (normalT x y z) = 2*(x+y+z) := by
  norm_num [Matrix.trace, normalT, Fin.sum_univ_succ]
  ring

theorem normalT_trace_two (x y z : ℂ) :
    Matrix.trace (normalT x y z ^ 2) = 2*(x+y+z)^2 := by
  norm_num [Matrix.trace, normalT, Matrix.mul_apply, pow_succ, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 0 in
theorem normalT_trace_three (x y z : ℂ) :
    Matrix.trace (normalT x y z ^ 3) = 2*(x+y+z)^3+12*x*y*z := by
  norm_num [Matrix.trace, normalT, Matrix.mul_apply, pow_succ, Fin.sum_univ_succ]
  ring

theorem normalR_trace_one (x y z : ℂ) :
    Matrix.trace (normalR x y z) = 6*(x+y+z) := by
  norm_num [Matrix.trace, normalR, Fin.sum_univ_succ]
  ring

theorem normalR_trace_two (x y z : ℂ) :
    Matrix.trace (normalR x y z ^ 2) = 18*(x+y+z)^2 := by
  norm_num [Matrix.trace, normalR, Matrix.mul_apply, pow_succ, Fin.sum_univ_succ]
  ring

set_option maxHeartbeats 0 in
theorem normalR_trace_three (x y z : ℂ) :
    Matrix.trace (normalR x y z ^ 3) = 66*(x+y+z)^3-324*x*y*z := by
  norm_num [Matrix.trace, normalR, Matrix.mul_apply, pow_succ, Fin.sum_univ_succ]
  ring

lemma trace_recurrence (M : Matrix (Fin 4) (Fin 4) ℂ) (u v w : ℂ)
    (h : M^4 = u • M^3 + v • M^2 + w • M) (k : ℕ) :
    Matrix.trace (M^(k+4)) = u * Matrix.trace (M^(k+3)) +
      v * Matrix.trace (M^(k+2)) + w * Matrix.trace (M^(k+1)) := by
  have hh := congrArg (fun N => Matrix.trace (N * M^k)) h
  simpa only [add_mul, smul_mul_assoc, Matrix.trace_add, Matrix.trace_smul,
    ← pow_add, smul_eq_mul, Nat.add_comm, pow_one, ← pow_succ'] using hh

theorem normal_trace_four (x y z : ℂ) :
    27 * Matrix.trace (normalT x y z ^ 4) + Matrix.trace (normalR x y z ^ 4) =
      normalTrace4 (x+y+z) (x*y*z) := by
  have hT := trace_recurrence _ _ _ _ (normalT_recurrence x y z) 0
  have hR := trace_recurrence _ _ _ _ (normalR_recurrence x y z) 0
  norm_num only [Nat.reduceAdd, pow_one] at hT hR
  rw [normalT_trace_one, normalT_trace_two, normalT_trace_three] at hT
  rw [normalR_trace_one, normalR_trace_two, normalR_trace_three] at hR
  rw [hT, hR]
  unfold normalTrace4
  ring

theorem normal_trace_six (x y z : ℂ) :
    27 * Matrix.trace (normalT x y z ^ 6) + Matrix.trace (normalR x y z ^ 6) =
      normalTrace6 (x+y+z) (x*y*z) := by
  have t4 := trace_recurrence _ _ _ _ (normalT_recurrence x y z) 0
  have t5 := trace_recurrence _ _ _ _ (normalT_recurrence x y z) 1
  have t6 := trace_recurrence _ _ _ _ (normalT_recurrence x y z) 2
  have r4 := trace_recurrence _ _ _ _ (normalR_recurrence x y z) 0
  have r5 := trace_recurrence _ _ _ _ (normalR_recurrence x y z) 1
  have r6 := trace_recurrence _ _ _ _ (normalR_recurrence x y z) 2
  norm_num only [Nat.reduceAdd, pow_one] at t4 t5 t6 r4 r5 r6
  rw [normalT_trace_one, normalT_trace_two, normalT_trace_three] at t4
  rw [t4, normalT_trace_two, normalT_trace_three] at t5
  rw [t5, t4, normalT_trace_three] at t6
  rw [normalR_trace_one, normalR_trace_two, normalR_trace_three] at r4
  rw [r4, normalR_trace_two, normalR_trace_three] at r5
  rw [r5, r4, normalR_trace_three] at r6
  rw [t6, r6]
  unfold normalTrace6
  ring

theorem normal_four_matrix_certificate (x y z : ℂ) :
    invariant16 (x+y+z)
      (27 * Matrix.trace (normalT x y z ^ 4) + Matrix.trace (normalR x y z ^ 4))
      (27 * Matrix.trace (normalT x y z ^ 6) + Matrix.trace (normalR x y z ^ 6)) = 0 := by
  rw [normal_trace_four, normal_trace_six]
  exact normal_moment_elimination _ _

end
end Fermionic.RankCertificate

#print axioms Fermionic.RankCertificate.normalT_recurrence
#print axioms Fermionic.RankCertificate.normalR_recurrence
#print axioms Fermionic.RankCertificate.normal_four_matrix_certificate
