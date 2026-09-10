import Fermionic.RankCertificateSelfPrelude

/-! Original rows 75 through 89; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock5 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 5 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock5

theorem normalMixedBlock5 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 5 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 5 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock5
end Fermionic.RankCertificate
