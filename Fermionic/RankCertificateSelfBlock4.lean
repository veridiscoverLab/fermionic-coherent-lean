import Fermionic.RankCertificateSelfPrelude

/-! Original rows 60 through 74; all original columns and source coefficients. -/
namespace Fermionic.RankCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem normalSelfBlock4 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalBilinear kind kind (normalCoordinatePair (normalBlockRow 4 r))
        (normalCoordinatePair j) = 0 := by decide

#print axioms normalSelfBlock4

theorem normalMixedBlock4 :
    ∀ kind : Fin 3, ∀ r : Fin 15, ∀ j : NormalIndex,
      fastNormalMixed kind (normalCoordinatePair (normalBlockRow 4 r))
        (normalCoordinatePair j) =
      normalRawCoefficient kind (normalCoordinatePair (normalBlockRow 4 r))
        (normalCoordinatePair j) := by decide

#print axioms normalMixedBlock4
end Fermionic.RankCertificate
