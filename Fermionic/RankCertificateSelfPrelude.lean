import Fermionic.RankCertificateNormalSource

/-! Full original coefficient checks, evaluated through an exactly proved
zero-coefficient shortcut. The original source and Gram definitions are
unchanged. The shortcut is ordinary definitional kernel evaluation. -/
namespace Fermionic.RankCertificate

def fastNormalBilinear (r s : Fin 3) (p q : Pair) : ℤ :=
  dualSign p * ∑ u : Fin 16,
    let a := normalBasisCoefficient r (pairedGaussianMask u)
    let b := normalBasisCoefficient s (normalPartner p q (pairedGaussianMask u))
    if a = 0 then 0 else if b = 0 then 0 else
      a * normalKernel p q (pairedGaussianMask u) * b

lemma fastNormalBilinear_eq (r s : Fin 3) (p q : Pair) :
    fastNormalBilinear r s p q = normalBilinearCoefficient r s p q := by
  unfold fastNormalBilinear normalBilinearCoefficient
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  change (if normalBasisCoefficient r (pairedGaussianMask u) = 0 then 0
    else if normalBasisCoefficient s (normalPartner p q (pairedGaussianMask u)) = 0
      then 0 else _) =
    normalBasisCoefficient r (pairedGaussianMask u) *
      (normalKernel p q (pairedGaussianMask u) *
        normalBasisCoefficient s (normalPartner p q (pairedGaussianMask u)))
  split_ifs with ha hb
  · simp [ha]
  · simp [hb]
  · ring

def fastNormalMixed (kind : Fin 3) (p q : Pair) : ℤ :=
  let r : Fin 3 := if kind = 2 then 1 else 0
  let s : Fin 3 := if kind = 0 then 1 else 2
  fastNormalBilinear r s p q + fastNormalBilinear s r p q

lemma fastNormalMixed_eq (kind : Fin 3) (p q : Pair) :
    fastNormalMixed kind p q = directNormalMixedCoefficient kind p q := by
  simp [fastNormalMixed, directNormalMixedCoefficient, fastNormalBilinear_eq]


/-- Fixed enumeration of all original rows; no row depends on the source. -/
def normalFlatRow (r : Fin 120) : NormalIndex :=
  if h : r.val < 8 then .inl ⟨r.val,h⟩
  else if h2 : r.val < 104 then
    .inr (.inl (⟨(r.val-8)%4, Nat.mod_lt _ (by omega)⟩,
      ⟨(r.val-8)/4, by omega⟩))
  else .inr (.inr (⟨(r.val-104)%4, Nat.mod_lt _ (by omega)⟩,
    ⟨(r.val-104)/4, by omega⟩))

def normalBlockRow (b : Fin 8) (r : Fin 15) : NormalIndex :=
  normalFlatRow ⟨15*b.val+r.val, by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem normalBlockRows_cover : ∀ i : NormalIndex,
    ∃ b : Fin 8, ∃ r : Fin 15, normalBlockRow b r = i := by decide

end Fermionic.RankCertificate
#print axioms Fermionic.RankCertificate.fastNormalBilinear_eq
#print axioms Fermionic.RankCertificate.fastNormalMixed_eq
#print axioms Fermionic.RankCertificate.normalBlockRows_cover
