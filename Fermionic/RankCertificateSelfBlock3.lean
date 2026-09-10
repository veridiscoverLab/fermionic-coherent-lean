import Fermionic.RankCertificateSelfPrelude

/-! Original rows 45 through 59; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock3 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 3 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock3

theorem normalMixedBlock3 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 3 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 3 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock3
end Fermionic.RankCertificate
