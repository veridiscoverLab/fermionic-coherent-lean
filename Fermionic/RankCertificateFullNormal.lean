import Fermionic.RankCertificateNormalSelf
import Fermionic.RankCertificateNormalAssembly
import Fermionic.RankCertificateTrace

namespace Fermionic.RankCertificate
noncomputable section

theorem actualNormalFullGram_eq (a b c : ℂ) :
    actualNormalFullGram a b c = actualNormalMixedGram (a*b) (a*c) (b*c) :=
  actualNormalFullGram_eq_of_coefficients a b c
    direct_normal_self_coefficients direct_normal_mixed_coefficients

theorem actual_normal_full_trace_four (a b c : ℂ) :
    Matrix.trace (actualNormalFullGram a b c ^ 4) =
      normalTrace4 (a*b+a*c+b*c) (a^2*b^2*c^2) := by
  rw [actualNormalFullGram_eq]
  have hp : (a*b)*(a*c)*(b*c) = a^2*b^2*c^2 := by ring
  simpa only [hp] using actual_normal_mixed_trace_four (a*b) (a*c) (b*c)

theorem actual_normal_full_trace_six (a b c : ℂ) :
    Matrix.trace (actualNormalFullGram a b c ^ 6) =
      normalTrace6 (a*b+a*c+b*c) (a^2*b^2*c^2) := by
  rw [actualNormalFullGram_eq]
  have hp : (a*b)*(a*c)*(b*c) = a^2*b^2*c^2 := by ring
  simpa only [hp] using actual_normal_mixed_trace_six (a*b) (a*c) (b*c)

theorem full_coordinate_normal_certificate (a b c : ℂ) :
    invariant18 (actualNormalHalfPair a b c)
      (Matrix.trace (actualNormalFullGram a b c ^ 4))
      (Matrix.trace (actualNormalFullGram a b c ^ 6)) = 0 := by
  rw [actualNormalHalfPair_eq, actualNormalFullGram_eq]
  unfold invariant18
  rw [actual_normal_mixed_certificate]
  ring

end
end Fermionic.RankCertificate
#print axioms Fermionic.RankCertificate.actualNormalFullGram_eq
#print axioms Fermionic.RankCertificate.actualNormalHalfPair_eq
#print axioms Fermionic.RankCertificate.full_coordinate_normal_certificate

#print axioms Fermionic.RankCertificate.actual_normal_full_trace_four
#print axioms Fermionic.RankCertificate.actual_normal_full_trace_six
