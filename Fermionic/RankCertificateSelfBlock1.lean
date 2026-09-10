import Fermionic.RankCertificateSelfPrelude

/-! Original rows 15 through 29; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock1 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 1 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock1

theorem normalMixedBlock1 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 1 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 1 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock1
end Fermionic.RankCertificate
