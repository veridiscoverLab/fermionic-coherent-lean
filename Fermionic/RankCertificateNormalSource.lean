import Fermionic.RankCertificateNormalCoordinates

namespace Fermionic.RankCertificate

def pairedGaussianMask : Fin 16 → ℕ :=
  ![0,3,12,15,48,51,60,63,192,195,204,207,240,243,252,255]

def vacuumCoefficient (m : ℕ) : ℤ := if m = 0 then 1 else 0

def normalBasisCoefficient (kind : Fin 3) (m : ℕ) : ℤ :=
  if kind = 0 then vacuumCoefficient m
  else if kind = 1 then topCoefficient m
  else pairedGaussianCoefficient m

/-- Direct full bilinear Gram coefficient: both source vectors are read on
the same complete sixteen-mask support, before any symmetry reduction. -/
def normalBilinearCoefficient (r s : Fin 3) (p q : Pair) : ℤ :=
  dualSign p * ∑ u : Fin 16,
    normalBasisCoefficient r (pairedGaussianMask u) *
      fixed_dynamic_pairing (dualPair p) q (pairedGaussianMask u)
        (normalBasisCoefficient s)

def directNormalMixedCoefficient (kind : Fin 3) (p q : Pair) : ℤ :=
  let r : Fin 3 := if kind = 2 then 1 else 0
  let s : Fin 3 := if kind = 0 then 1 else 2
  normalBilinearCoefficient r s p q + normalBilinearCoefficient s r p q

def normalSelfCoefficient (kind : Fin 3) (p q : Pair) : ℤ :=
  dualSign p *
    (if kind = 0 then fixed_dynamic_pairing (dualPair p) q 0 vacuumCoefficient
     else if kind = 1 then fixed_dynamic_pairing (dualPair p) q 255 topCoefficient
     else ∑ r : Fin 16,
       fixed_dynamic_pairing (dualPair p) q (pairedGaussianMask r)
         pairedGaussianCoefficient)


noncomputable section

def normalWeights (a b c : ℂ) : Fin 3 → ℂ := ![a,b,c]

def normalVector (a b c : ℂ) (m : ℕ) : ℂ :=
  ∑ r : Fin 3, normalWeights a b c r * (normalBasisCoefficient r m : ℂ)

def normalKernel (p q : Pair) (u : ℕ) : ℤ :=
  let out := bivectorOutput (dualPair p) u
  let v := bivectorOutput q (Nat.xor 255 out)
  bivectorCoefficient2 (dualPair p) u * chevalleySign out *
    bivectorCoefficient2 q v

def normalPartner (p q : Pair) (u : ℕ) : ℕ :=
  bivectorOutput q (Nat.xor 255 (bivectorOutput (dualPair p) u))

/-- Full source-to-source Gram, with all sixteen occupied masks and both
copies of the same original normal-family vector retained. -/
def actualNormalFullGram (a b c : ℂ) : Matrix NormalIndex NormalIndex ℂ :=
  fun i j =>
    let p := normalCoordinatePair i
    let q := normalCoordinatePair j
    (1/4:ℂ) * (normalCoordinateSign i:ℂ) * (normalCoordinateSign j:ℂ) *
      (dualSign p:ℂ) * ∑ u : Fin 16,
        normalVector a b c (pairedGaussianMask u) *
          (normalKernel p q (pairedGaussianMask u):ℂ) *
          normalVector a b c (normalPartner p q (pairedGaussianMask u))

lemma finite_bilinear_expansion {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℂ) (L R : ι → κ → ℂ) (K : κ → ℂ) :
    (∑ u : κ, (∑ r : ι, w r * L r u) * K u * (∑ s : ι, w s * R s u)) =
      ∑ r : ι, ∑ s : ι, w r * w s * (∑ u : κ, L r u * K u * R s u) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  ring

lemma normalBilinearCoefficient_cast (r s : Fin 3) (p q : Pair) :
    (normalBilinearCoefficient r s p q : ℂ) =
      (dualSign p:ℂ) * ∑ u : Fin 16,
        (normalBasisCoefficient r (pairedGaussianMask u):ℂ) *
          (normalKernel p q (pairedGaussianMask u):ℂ) *
          (normalBasisCoefficient s
            (normalPartner p q (pairedGaussianMask u)):ℂ) := by
  simp only [normalBilinearCoefficient, Int.cast_mul, Int.cast_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  simp only [fixed_dynamic_pairing, normalKernel, normalPartner, Int.cast_mul]
  ring

lemma actualNormalFullGram_expansion (a b c : ℂ) (i j : NormalIndex) :
    actualNormalFullGram a b c i j =
      (1/4:ℂ) * (normalCoordinateSign i:ℂ) * (normalCoordinateSign j:ℂ) *
        ∑ r : Fin 3, ∑ s : Fin 3,
          normalWeights a b c r * normalWeights a b c s *
            (normalBilinearCoefficient r s
              (normalCoordinatePair i) (normalCoordinatePair j):ℂ) := by
  unfold actualNormalFullGram normalVector
  dsimp only
  rw [finite_bilinear_expansion]
  simp_rw [normalBilinearCoefficient_cast]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro u _
  ring

def actualNormalHalfPair (a b c : ℂ) : ℂ :=
  (1/2:ℂ) * ∑ u : Fin 16,
    normalVector a b c (pairedGaussianMask u) *
      (chevalleySign (pairedGaussianMask u):ℂ) *
      normalVector a b c (Nat.xor 255 (pairedGaussianMask u))

def normalChevalleyCoefficient (r s : Fin 3) : ℤ :=
  ∑ u : Fin 16, normalBasisCoefficient r (pairedGaussianMask u) *
    chevalleySign (pairedGaussianMask u) *
    normalBasisCoefficient s (Nat.xor 255 (pairedGaussianMask u))

set_option maxRecDepth 100000 in
theorem normalChevalleyCoefficient_eq : ∀ r s : Fin 3,
    normalChevalleyCoefficient r s =
      ![![0,1,1],![1,0,1],![1,1,0]] r s := by decide

lemma normalChevalleyCoefficient_cast (r s : Fin 3) :
    (∑ u : Fin 16, (normalBasisCoefficient r (pairedGaussianMask u):ℂ) *
      (chevalleySign (pairedGaussianMask u):ℂ) *
      (normalBasisCoefficient s (Nat.xor 255 (pairedGaussianMask u)):ℂ)) =
      (normalChevalleyCoefficient r s:ℂ) := by
  simp [normalChevalleyCoefficient, Int.cast_sum, Int.cast_mul]

theorem actualNormalHalfPair_eq (a b c : ℂ) :
    actualNormalHalfPair a b c = a*b+a*c+b*c := by
  unfold actualNormalHalfPair normalVector
  rw [finite_bilinear_expansion]
  simp_rw [normalChevalleyCoefficient_cast, normalChevalleyCoefficient_eq]
  norm_num [normalWeights, Fin.sum_univ_succ]
  ring

end
end Fermionic.RankCertificate
