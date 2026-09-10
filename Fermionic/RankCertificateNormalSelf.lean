import Fermionic.RankCertificateSelfBlock0
import Fermionic.RankCertificateSelfBlock1
import Fermionic.RankCertificateSelfBlock2
import Fermionic.RankCertificateSelfBlock3
import Fermionic.RankCertificateSelfBlock4
import Fermionic.RankCertificateSelfBlock5
import Fermionic.RankCertificateSelfBlock6
import Fermionic.RankCertificateSelfBlock7

namespace Fermionic.RankCertificate

theorem direct_normal_self_coefficients :
    ∀ kind : Fin 3, ∀ i j : NormalIndex,
      normalBilinearCoefficient kind kind (normalCoordinatePair i)
        (normalCoordinatePair j) = 0 := by
  intro kind i j
  rw [← fastNormalBilinear_eq]
  obtain ⟨b,r,hr⟩ := normalBlockRows_cover i
  subst i
  fin_cases b
  · exact normalSelfBlock0 kind r j
  · exact normalSelfBlock1 kind r j
  · exact normalSelfBlock2 kind r j
  · exact normalSelfBlock3 kind r j
  · exact normalSelfBlock4 kind r j
  · exact normalSelfBlock5 kind r j
  · exact normalSelfBlock6 kind r j
  · exact normalSelfBlock7 kind r j

theorem direct_normal_mixed_coefficients :
    ∀ kind : Fin 3, ∀ i j : NormalIndex,
      directNormalMixedCoefficient kind (normalCoordinatePair i)
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair i)
        (normalCoordinatePair j) := by
  intro kind i j
  rw [← fastNormalMixed_eq]
  obtain ⟨b,r,hr⟩ := normalBlockRows_cover i
  subst i
  fin_cases b
  · exact normalMixedBlock0 kind r j
  · exact normalMixedBlock1 kind r j
  · exact normalMixedBlock2 kind r j
  · exact normalMixedBlock3 kind r j
  · exact normalMixedBlock4 kind r j
  · exact normalMixedBlock5 kind r j
  · exact normalMixedBlock6 kind r j
  · exact normalMixedBlock7 kind r j

end Fermionic.RankCertificate
#print axioms Fermionic.RankCertificate.direct_normal_self_coefficients
#print axioms Fermionic.RankCertificate.direct_normal_mixed_coefficients
