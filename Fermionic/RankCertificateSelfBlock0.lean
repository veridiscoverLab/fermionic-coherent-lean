import Fermionic.RankCertificateSelfPrelude

/-! Original rows 0 through 14; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock0 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 0 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock0

theorem normalMixedBlock0 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 0 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 0 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock0
end Fermionic.RankCertificate
