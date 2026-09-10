import Fermionic.RankCertificateSelfPrelude

/-! Original rows 30 through 44; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock2 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 2 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock2

theorem normalMixedBlock2 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 2 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 2 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock2
end Fermionic.RankCertificate
