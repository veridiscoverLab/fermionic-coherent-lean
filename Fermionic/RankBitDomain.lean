import Fermionic.RankCertificateNormalSource
import Mathlib.Data.Nat.Bitwise

/-!
Eight-bit domain and parity of the original coordinate generators and source
masks. Parity here means the count of true low-eight testBits modulo two.
No identification with the exterior-algebra grading is claimed in this file.
-/
namespace Fermionic.RankCertificate

/-- Number of occupied positions among the original eight modes. -/
def lowEightWeight (m : ℕ) : ℕ :=
  ((List.range 8).filter (fun j => m.testBit j)).length

/-- Coordinate parity, with no implicit finiteness condition on higher bits. -/
def lowEightParity (m : ℕ) : ℕ := lowEightWeight m % 2

def EvenMask (m : ℕ) : Prop := lowEightParity m = 0

instance decidableEvenMask (m : ℕ) : Decidable (EvenMask m) := inferInstanceAs (Decidable (_ = _))

theorem axis_lt_eight (i : Direction) : axis i < 8 := Nat.mod_lt _ (by decide)

theorem bit_lt_byte (i : Direction) : bit i < 256 := by
  change 2 ^ axis i < 2 ^ 8
  exact Nat.pow_lt_pow_right (by decide) (axis_lt_eight i)

theorem toggle_lt_byte (i : Direction) {m : ℕ} (hm : m < 256) :
    toggle i m < 256 :=
  Nat.xor_lt_two_pow (n := 8) hm (bit_lt_byte i)

theorem complement_lt_byte {m : ℕ} (hm : m < 256) :
    Nat.xor 255 m < 256 :=
  Nat.xor_lt_two_pow (n := 8) (by decide) hm

theorem bivectorOutput_lt_byte (p : Pair) {m : ℕ} (hm : m < 256) :
    bivectorOutput p m < 256 :=
  toggle_lt_byte p.1 (toggle_lt_byte p.2 hm)

theorem normalPartner_lt_byte (p q : Pair) {m : ℕ} (hm : m < 256) :
    normalPartner p q m < 256 :=
  bivectorOutput_lt_byte q (complement_lt_byte (bivectorOutput_lt_byte (dualPair p) hm))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma toggle_even_finite : ∀ (i : Direction) (m : Fin 256),
    EvenMask (toggle i m.val) ↔ ¬ EvenMask m.val := by decide

theorem toggle_even_iff (i : Direction) {m : ℕ} (hm : m < 256) :
    EvenMask (toggle i m) ↔ ¬ EvenMask m :=
  toggle_even_finite i ⟨m, hm⟩

set_option maxRecDepth 100000 in
lemma complement_even_finite : ∀ m : Fin 256,
    EvenMask (Nat.xor 255 m.val) ↔ EvenMask m.val := by decide

theorem complement_even_iff {m : ℕ} (hm : m < 256) :
    EvenMask (Nat.xor 255 m) ↔ EvenMask m :=
  complement_even_finite ⟨m, hm⟩

/-- Both original Clifford toggles are retained, including coincident axes. -/
theorem bivectorOutput_even_iff (p : Pair) {m : ℕ} (hm : m < 256) :
    EvenMask (bivectorOutput p m) ↔ EvenMask m := by
  unfold bivectorOutput
  rw [toggle_even_iff p.1 (toggle_lt_byte p.2 hm), toggle_even_iff p.2 hm]
  exact not_not

/-- Complement and both pairs act on the same mask; there is no support cut. -/
theorem normalPartner_even_iff (p q : Pair) {m : ℕ} (hm : m < 256) :
    EvenMask (normalPartner p q m) ↔ EvenMask m := by
  unfold normalPartner
  rw [bivectorOutput_even_iff q
    (complement_lt_byte (bivectorOutput_lt_byte (dualPair p) hm))]
  rw [complement_even_iff (bivectorOutput_lt_byte (dualPair p) hm)]
  exact bivectorOutput_even_iff (dualPair p) hm

set_option maxRecDepth 100000 in
theorem targetMask_byte_even : ∀ i : Fin 4,
    targetMask i < 256 ∧ EvenMask (targetMask i) := by decide

set_option maxRecDepth 100000 in
theorem pairedGaussianMask_byte_even : ∀ i : Fin 16,
    pairedGaussianMask i < 256 ∧ EvenMask (pairedGaussianMask i) := by decide

set_option maxRecDepth 100000 in
lemma pairedGaussianCoefficient_even_finite : ∀ m : Fin 256,
    pairedGaussianCoefficient m.val ≠ 0 → EvenMask m.val := by decide

theorem pairedGaussianCoefficient_even {m : ℕ} (hm : m < 256)
    (hc : pairedGaussianCoefficient m ≠ 0) : EvenMask m :=
  pairedGaussianCoefficient_even_finite ⟨m, hm⟩ hc

/-- Every output read by the complete original normal Gram stays in the
same eight-bit even domain. -/
theorem normal_source_partner_byte_even (p q : Pair) (i : Fin 16) :
    normalPartner p q (pairedGaussianMask i) < 256 ∧
      EvenMask (normalPartner p q (pairedGaussianMask i)) := by
  have hi := pairedGaussianMask_byte_even i
  exact ⟨normalPartner_lt_byte p q hi.1, (normalPartner_even_iff p q hi.1).mpr hi.2⟩

theorem target_source_bivector_byte_even (p : Pair) (i : Fin 4) :
    bivectorOutput p (targetMask i) < 256 ∧
      EvenMask (bivectorOutput p (targetMask i)) := by
  have hi := targetMask_byte_even i
  exact ⟨bivectorOutput_lt_byte p hi.1, (bivectorOutput_even_iff p hi.1).mpr hi.2⟩

theorem target_source_partner_byte_even (p q : Pair) (i : Fin 4) :
    normalPartner p q (targetMask i) < 256 ∧
      EvenMask (normalPartner p q (targetMask i)) := by
  have hi := targetMask_byte_even i
  exact ⟨normalPartner_lt_byte p q hi.1, (normalPartner_even_iff p q hi.1).mpr hi.2⟩

end Fermionic.RankCertificate

#print axioms Fermionic.RankCertificate.toggle_lt_byte
#print axioms Fermionic.RankCertificate.bivectorOutput_even_iff
#print axioms Fermionic.RankCertificate.normalPartner_even_iff
#print axioms Fermionic.RankCertificate.normal_source_partner_byte_even
#print axioms Fermionic.RankCertificate.target_source_bivector_byte_even

#print axioms Fermionic.RankCertificate.target_source_partner_byte_even
