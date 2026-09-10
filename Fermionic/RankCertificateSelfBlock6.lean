import Fermionic.RankCertificateSelfPrelude

/-! Original rows 90 through 104; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock6 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 6 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock6

theorem normalMixedBlock6 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 6 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 6 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock6
end Fermionic.RankCertificate
