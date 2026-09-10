import Fermionic.RankCertificateNormalCoordinates
import Fermionic.RankCertificateCompression

/-! Restoring the complete mixed-coefficient Gram to the fixed common-block
form. All original directions are present through the bijective coordinate
map in RankCertificateNormalCoordinates. The diagonal pure-square terms are
handled independently in RankCertificateNormalSelf. -/
namespace Fermionic.RankCertificate
noncomputable section
open scoped Kronecker

lemma cast_normal_form (x y z : ℤ) (i j : NormalIndex) :
    (normalFormInt x y z i j : ℂ) =
      4 * normalFullBlock (x:ℂ) (y:ℂ) (z:ℂ) i j := by
  rcases i with i | (⟨i,a⟩ | ⟨i,a⟩) <;>
    rcases j with j | (⟨j,b⟩ | ⟨j,b⟩)
  all_goals simp only [normalFormInt, normalFullBlock, Matrix.fromBlocks,
    Matrix.blockDiagonal, centralCompression, Matrix.smul_apply]
  all_goals try norm_num
  all_goals fin_cases i <;> fin_cases j <;>
    simp [normalMiddleInt, normalTInt, normalRInt, normalT, normalR, commonP, commonQ,
      Matrix.sub_apply, Matrix.one_apply] <;> (try split_ifs) <;> norm_num <;> ring

lemma normalFullBlock_linear (x y z : ℂ) (i j : NormalIndex) :
    normalFullBlock x y z i j =
      x * normalFullBlock 1 0 0 i j +
      y * normalFullBlock 0 1 0 i j +
      z * normalFullBlock 0 0 1 i j := by
  rcases i with i | (⟨i,a⟩ | ⟨i,a⟩) <;>
    rcases j with j | (⟨j,b⟩ | ⟨j,b⟩)
  all_goals simp only [normalFullBlock, Matrix.fromBlocks, Matrix.blockDiagonal,
    centralCompression]
  all_goals try norm_num
  all_goals fin_cases i <;> fin_cases j <;>
    simp [normalT, normalR, commonP, commonQ, Matrix.sub_apply,
      Matrix.one_apply] <;> (try split_ifs) <;> norm_num <;> ring

def actualNormalMixedGram (x y z : ℂ) : Matrix NormalIndex NormalIndex ℂ :=
  fun i j => (1/4:ℂ) *
    (x * (normalReindexedCoefficient 0 i j : ℂ) +
     y * (normalReindexedCoefficient 1 i j : ℂ) +
     z * (normalReindexedCoefficient 2 i j : ℂ))

theorem actualNormalMixedGram_eq (x y z : ℂ) :
    actualNormalMixedGram x y z = normalFullBlock x y z := by
  ext i j
  unfold actualNormalMixedGram
  have h0 : normalReindexedCoefficient 0 i j = normalFormInt 1 0 0 i j :=
    all_normal_coefficients 0 i j
  have h1 : normalReindexedCoefficient 1 i j = normalFormInt 0 1 0 i j :=
    all_normal_coefficients 1 i j
  have h2 : normalReindexedCoefficient 2 i j = normalFormInt 0 0 1 i j :=
    all_normal_coefficients 2 i j
  rw [h0, h1, h2, cast_normal_form, cast_normal_form, cast_normal_form]
  norm_num only [Int.cast_one, Int.cast_zero]
  rw [normalFullBlock_linear x y z i j]
  ring

theorem actual_normal_mixed_trace_four (x y z : ℂ) :
    Matrix.trace (actualNormalMixedGram x y z ^ 4) =
      normalTrace4 (x+y+z) (x*y*z) := by
  rw [actualNormalMixedGram_eq,
    normalFullBlock_trace_power x y z 4 (by omega)]
  exact normal_trace_four x y z

theorem actual_normal_mixed_trace_six (x y z : ℂ) :
    Matrix.trace (actualNormalMixedGram x y z ^ 6) =
      normalTrace6 (x+y+z) (x*y*z) := by
  rw [actualNormalMixedGram_eq,
    normalFullBlock_trace_power x y z 6 (by omega)]
  exact normal_trace_six x y z

theorem actual_normal_mixed_certificate (x y z : ℂ) :
    invariant16 (x+y+z) (Matrix.trace (actualNormalMixedGram x y z ^ 4))
      (Matrix.trace (actualNormalMixedGram x y z ^ 6)) = 0 := by
  rw [actualNormalMixedGram_eq]
  exact normalFullBlock_certificate x y z

end
end Fermionic.RankCertificate
#print axioms Fermionic.RankCertificate.actualNormalMixedGram_eq
#print axioms Fermionic.RankCertificate.actual_normal_mixed_certificate
