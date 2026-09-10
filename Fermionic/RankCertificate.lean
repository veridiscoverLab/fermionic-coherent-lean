import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
An explicit degree-sixteen invariant candidate and the complete integer
occupation-coordinate Gram of the eight-mode target.
The Fock/Spin identification and the three-pure-spinor vanishing theorem
are not assumed, and are not claimed in this file.
-/

namespace Fermionic.RankCertificate

def invariant16 (s t4 t6 : ℂ) : ℂ :=
  576 * s^2 * t6 - 7 * t4^2 - 18960 * s^4 * t4 + 4205376 * s^8

def normalTrace4 (s p : ℂ) : ℂ := 312*s^4 - 1728*s*p
def normalTrace6 (s p : ℂ) : ℂ :=
  36288*p^2 - 69984*p*s^3 + 4152*s^6

theorem normal_moment_elimination (s p : ℂ) :
    invariant16 s (normalTrace4 s p) (normalTrace6 s p) = 0 := by
  unfold invariant16 normalTrace4 normalTrace6
  ring

theorem target_moment_evaluation :
    invariant16 2 3648 57408 = 9031680 := by
  norm_num [invariant16]

theorem target_moment_nonzero :
    invariant16 2 3648 57408 ≠ 0 := by
  rw [target_moment_evaluation]
  norm_num

/-! All indices below range over the original sixteen split directions.
Directions 0,...,7 create and directions 8,...,15 annihilate.
The 120 ordered pairs i<j are the full bivector basis. -/

abbrev Direction := Fin 16
abbrev Pair := Direction × Direction

def axis (i : Direction) : ℕ := i.val % 8
def bit (i : Direction) : ℕ := 2 ^ axis i
def toggle (i : Direction) (m : ℕ) : ℕ := Nat.xor m (bit i)

def signBelow (i : Direction) (m : ℕ) : ℤ :=
  if (((List.range (axis i)).filter (fun j => m.testBit j)).length % 2 = 0)
  then 1 else -1

def gammaCoefficient (i : Direction) (m : ℕ) : ℤ :=
  if m.testBit (axis i) == decide (8 ≤ i.val) then signBelow i m else 0

/-- Twice the coefficient of the actual bivector Clifford action on a basis
vector: [c_i,c_j] = 2 c_i c_j - B(i,j). -/
def bivectorCoefficient2 (p : Pair) (m : ℕ) : ℤ :=
  2 * gammaCoefficient p.2 m * gammaCoefficient p.1 (toggle p.2 m) -
    if p.1.val + 8 = p.2.val then 1 else 0

def bivectorOutput (p : Pair) (m : ℕ) : ℕ :=
  toggle p.1 (toggle p.2 m)

def dualDirection (i : Direction) : Direction :=
  ⟨(i.val + 8) % 16, Nat.mod_lt _ (by decide)⟩

def dualPair (p : Pair) : Pair :=
  let i := dualDirection p.1
  let j := dualDirection p.2
  if i < j then (i,j) else (j,i)

def dualSign (p : Pair) : ℤ :=
  if dualDirection p.1 < dualDirection p.2 then 1 else -1

/-- The exact Chevalley reversal/wedge sign in eight creation coordinates. -/
def chevalleySign (m : ℕ) : ℤ :=
  if (((List.range 8).filter (fun j => m.testBit j)).map (fun j => j+1)).sum % 2 = 0
  then 1 else -1

def targetMask : Fin 4 → ℕ := ![0,15,240,255]
def targetCoefficient (m : ℕ) : ℤ :=
  if m = 0 ∨ m = 15 ∨ m = 240 ∨ m = 255 then 1 else 0

/-- Four times the complete bilinear Gram, expanded over the actual four
occupation terms of (1+e1234)(1+e5678). No intermediate output direction
is discarded. -/
def targetGram4 (p q : Pair) : ℤ :=
  dualSign p * ∑ r : Fin 4,
    let u := targetMask r
    let x := bivectorOutput (dualPair p) u
    let v := bivectorOutput q (Nat.xor 255 x)
    bivectorCoefficient2 (dualPair p) u * chevalleySign x *
      bivectorCoefficient2 q v * targetCoefficient v

def isCross (p : Pair) : Bool := decide ((axis p.1 < 4) ≠ (axis p.2 < 4))
def sameSide (p : Pair) : Bool := decide ((p.1.val < 8) = (p.2.val < 8))
def isDiagonal (p : Pair) : Bool := decide (p.1.val + 8 = p.2.val)
def sameBlock (p q : Pair) : Bool := decide ((axis p.1 < 4) = (axis q.1 < 4))
def pairedComplement (p q : Pair) : Bool :=
  sameSide p && sameSide q && sameBlock p q &&
    decide ((p.1.val < 8) ≠ (q.1.val < 8)) &&
    decide (Nat.xor (Nat.xor (bit p.1) (bit p.2))
      (Nat.xor (bit q.1) (bit q.2)) = if axis p.1 < 4 then 15 else 240)

/-- Sparse block formula for the same full matrix. -/
def targetGramSparse (p q : Pair) : ℤ :=
  if isCross p then (if p = q then 4 else 0)
  else if isCross q then 0
  else if sameSide p then
    if p = q then 8
    else if pairedComplement p q then
      if (axis p.1 + axis p.2) % 2 = 0 then 8 else -8
    else 0
  else if isDiagonal p && isDiagonal q && sameBlock p q then 4
  else 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem target_gram_all_entries :
    ∀ i j k l : Direction, i < j → k < l →
      targetGram4 (i,j) (k,l) = targetGramSparse (i,j) (k,l) := by
  decide

end Fermionic.RankCertificate

#print axioms Fermionic.RankCertificate.normal_moment_elimination
#print axioms Fermionic.RankCertificate.target_moment_nonzero
#print axioms Fermionic.RankCertificate.target_gram_all_entries
