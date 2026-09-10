import Fermionic.RankCertificateNormalSource
import Fermionic.RankCertificateNormalTrace

namespace Fermionic.RankCertificate
noncomputable section

lemma actualNormalFullGram_eq_of_coefficients (a b c : ℂ)
    (hdiag : ∀ r : Fin 3, ∀ i j : NormalIndex,
      normalBilinearCoefficient r r (normalCoordinatePair i) (normalCoordinatePair j) = 0)
    (hmix : ∀ r : Fin 3, ∀ i j : NormalIndex,
      directNormalMixedCoefficient r (normalCoordinatePair i) (normalCoordinatePair j) =
        normalRawCoefficient r (normalCoordinatePair i) (normalCoordinatePair j)) :
    actualNormalFullGram a b c = actualNormalMixedGram (a*b) (a*c) (b*c) := by
  ext i j
  rw [actualNormalFullGram_expansion]
  have hd0 := hdiag 0 i j
  have hd1 := hdiag 1 i j
  have hd2 := hdiag 2 i j
  have hm0 := hmix 0 i j
  have hm1 := hmix 1 i j
  have hm2 := hmix 2 i j
  change normalBilinearCoefficient 0 1 _ _ + normalBilinearCoefficient 1 0 _ _ = _ at hm0
  change normalBilinearCoefficient 0 2 _ _ + normalBilinearCoefficient 2 0 _ _ = _ at hm1
  change normalBilinearCoefficient 1 2 _ _ + normalBilinearCoefficient 2 1 _ _ = _ at hm2
  unfold actualNormalMixedGram normalReindexedCoefficient
  simp [Fin.sum_univ_succ, normalWeights, hd0, hd1, hd2, Int.cast_mul]
  have hc0 := congrArg (fun z : ℤ => (z:ℂ)) hm0
  have hc1 := congrArg (fun z : ℤ => (z:ℂ)) hm1
  have hc2 := congrArg (fun z : ℤ => (z:ℂ)) hm2
  simp only [Int.cast_add] at hc0 hc1 hc2
  rw [← hc0, ← hc1, ← hc2]
  ring

end
end Fermionic.RankCertificate
