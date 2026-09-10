import Fermionic.RankCertificateSelfPrelude

/-! Original rows 105 through 119; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock7 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 7 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock7

theorem normalMixedBlock7 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 7 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 7 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock7
end Fermionic.RankCertificate
