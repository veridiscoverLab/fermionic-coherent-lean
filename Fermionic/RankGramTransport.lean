import Mathlib.LinearAlgebra.Matrix.Trace
import Fermionic.RankCertificateTrace

/-!
Relative covariance of the full bilinear Gram, with one simultaneous source
and direction transformation. Concrete Clifford/Chevalley coordinate bridges
remain separate from this matrix theorem. No Hermitian transpose is used.
-/

namespace Fermionic.RankGramTransport
open Matrix

variable {K ι κ : Type*} [CommRing K]
variable [Fintype ι] [Fintype κ] [DecidableEq κ]

def gram (B : Matrix ι ι K) (Ginv : Matrix κ κ K) (J : Matrix ι κ K) :
    Matrix κ κ K := Ginv * J.transpose * B * J

theorem inverse_metric_transport (Ginv : Matrix κ κ K)
    (V : (Matrix κ κ K)ˣ)
    (hG : (V : Matrix κ κ K) * Ginv * (V : Matrix κ κ K).transpose = Ginv) :
    Ginv * (↑(V⁻¹) : Matrix κ κ K).transpose = (V : Matrix κ κ K) * Ginv := by
  have hV : (↑(V⁻¹) : Matrix κ κ K) * (V : Matrix κ κ K) = 1 := V.inv_mul
  have hT : (V : Matrix κ κ K).transpose *
      (↑(V⁻¹) : Matrix κ κ K).transpose = 1 := by
    rw [← Matrix.transpose_mul, hV, Matrix.transpose_one]
  calc
    _ = ((V : Matrix κ κ K) * Ginv * (V : Matrix κ κ K).transpose) *
        (↑(V⁻¹) : Matrix κ κ K).transpose := by rw [hG]
    _ = _ := by rw [Matrix.mul_assoc, hT, Matrix.mul_one]

/-- The same full direction change transports every cross Gram entry. -/
theorem gram_relative_covariance (B : Matrix ι ι K) (Ginv : Matrix κ κ K)
    (J : Matrix ι κ K) (U : Matrix ι ι K) (V : (Matrix κ κ K)ˣ) (r : K)
    (hB : U.transpose * B * U = r • B)
    (hG : (V : Matrix κ κ K) * Ginv * (V : Matrix κ κ K).transpose = Ginv) :
    gram B Ginv (U * J * (↑(V⁻¹) : Matrix κ κ K)) =
      r • ((V : Matrix κ κ K) * gram B Ginv J * (↑(V⁻¹) : Matrix κ κ K)) := by
  simp only [gram, Matrix.transpose_mul]
  calc
    _ = (Ginv * (↑(V⁻¹) : Matrix κ κ K).transpose) * J.transpose *
        (U.transpose * B * U) * J * (↑(V⁻¹) : Matrix κ κ K) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [inverse_metric_transport Ginv V hG, hB]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

theorem conjugate_pow (V : (Matrix κ κ K)ˣ) (A : Matrix κ κ K) (k : ℕ) :
    ((V : Matrix κ κ K) * A * (↑(V⁻¹) : Matrix κ κ K)) ^ k =
      (V : Matrix κ κ K) * A ^ k * (↑(V⁻¹) : Matrix κ κ K) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      have hV : (↑(V⁻¹) : Matrix κ κ K) * (V : Matrix κ κ K) = 1 := V.inv_mul
      calc
        _ = (V : Matrix κ κ K) * A ^ k *
            ((↑(V⁻¹) : Matrix κ κ K) * (V : Matrix κ κ K)) * A *
            (↑(V⁻¹) : Matrix κ κ K) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem trace_conjugate (V : (Matrix κ κ K)ˣ) (A : Matrix κ κ K) :
    Matrix.trace ((V : Matrix κ κ K) * A * (↑(V⁻¹) : Matrix κ κ K)) =
      Matrix.trace A := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, V.inv_mul, Matrix.one_mul]

/-- All trace powers transform together, including the fourth and sixth
moments consumed by the degree-sixteen rank certificate. -/
theorem trace_pow_relative (V : (Matrix κ κ K)ˣ) (A : Matrix κ κ K)
    (r : K) (k : ℕ) :
    Matrix.trace ((r • ((V : Matrix κ κ K) * A * (↑(V⁻¹) : Matrix κ κ K))) ^ k) =
      r ^ k * Matrix.trace (A ^ k) := by
  rw [smul_pow, conjugate_pow, Matrix.trace_smul, trace_conjugate]
  rfl

theorem invariant16_relative (s t4 t6 r : ℂ) :
    Fermionic.RankCertificate.invariant16 (r*s) (r^4*t4) (r^6*t6) =
      r^8 * Fermionic.RankCertificate.invariant16 s t4 t6 := by
  unfold Fermionic.RankCertificate.invariant16
  ring

theorem invariant16_relative_zero_iff (s t4 t6 r : ℂ) (hr : r ≠ 0) :
    Fermionic.RankCertificate.invariant16 (r*s) (r^4*t4) (r^6*t6) = 0 ↔
      Fermionic.RankCertificate.invariant16 s t4 t6 = 0 := by
  rw [invariant16_relative, mul_eq_zero]
  simp [pow_ne_zero 8 hr]

theorem invariant18_relative (s t4 t6 r : ℂ) :
    Fermionic.RankCertificate.invariant18 (r*s) (r^4*t4) (r^6*t6) =
      r^9 * Fermionic.RankCertificate.invariant18 s t4 t6 := by
  unfold Fermionic.RankCertificate.invariant18
  rw [invariant16_relative]
  ring

theorem invariant18_relative_zero_iff (s t4 t6 r : ℂ) (hr : r ≠ 0) :
    Fermionic.RankCertificate.invariant18 (r*s) (r^4*t4) (r^6*t6) = 0 ↔
      Fermionic.RankCertificate.invariant18 s t4 t6 = 0 := by
  rw [invariant18_relative, mul_eq_zero]
  simp [pow_ne_zero 9 hr]

/-- The invariant certificate transports on the same complete Gram. The
only transformation premises are the explicitly stated two form identities. -/
theorem complete_gram_certificate_zero_iff
    (B : Matrix ι ι ℂ) (Ginv : Matrix κ κ ℂ) (J : Matrix ι κ ℂ)
    (U : Matrix ι ι ℂ) (V : (Matrix κ κ ℂ)ˣ) (s r : ℂ) (hr : r ≠ 0)
    (hB : U.transpose * B * U = r • B)
    (hG : (V : Matrix κ κ ℂ) * Ginv * (V : Matrix κ κ ℂ).transpose = Ginv) :
    Fermionic.RankCertificate.invariant18 (r*s)
      (Matrix.trace (gram B Ginv (U * J * (↑(V⁻¹) : Matrix κ κ ℂ)) ^ 4))
      (Matrix.trace (gram B Ginv (U * J * (↑(V⁻¹) : Matrix κ κ ℂ)) ^ 6)) = 0 ↔
    Fermionic.RankCertificate.invariant18 s
      (Matrix.trace (gram B Ginv J ^ 4))
      (Matrix.trace (gram B Ginv J ^ 6)) = 0 := by
  rw [gram_relative_covariance B Ginv J U V r hB hG,
    trace_pow_relative, trace_pow_relative]
  exact invariant18_relative_zero_iff _ _ _ r hr

end Fermionic.RankGramTransport

#print axioms Fermionic.RankGramTransport.gram_relative_covariance
#print axioms Fermionic.RankGramTransport.trace_pow_relative
#print axioms Fermionic.RankGramTransport.invariant16_relative_zero_iff
#print axioms Fermionic.RankGramTransport.complete_gram_certificate_zero_iff
