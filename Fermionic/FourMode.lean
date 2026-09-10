import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Four-mode even coordinates and the Chevalley quadric

The coordinates are ordered as
(1, e12, e13, e14, e23, e24, e34, e1234).
This file proves an exact minimum-length decomposition theorem for the explicit
quadric in all eight complex coordinates.  It does not identify this quadric
with the physical Gaussian cone; that identification requires the actual
Fock/Spin representation and is a separate theorem.
-/

namespace Fermionic.FourMode

abbrev Space := Fin 8 → ℂ

/-- Half the diagonal Chevalley pairing in the displayed even-coordinate order. -/
def chevalleyQ (x : Space) : ℂ :=
  x 0 * x 7 - x 1 * x 6 + x 2 * x 5 - x 3 * x 4

/-- The bilinear Chevalley expression in the same coordinates. -/
def chevalleyB (x y : Space) : ℂ :=
  x 0 * y 7 + x 7 * y 0 - x 1 * y 6 - x 6 * y 1 +
    x 2 * y 5 + x 5 * y 2 - x 3 * y 4 - x 4 * y 3

@[simp] theorem chevalleyQ_zero : chevalleyQ 0 = 0 := by
  simp [chevalleyQ]

theorem chevalleyB_self (x : Space) :
    chevalleyB x x = 2 * chevalleyQ x := by
  dsimp [chevalleyB, chevalleyQ]
  ring

theorem chevalleyQ_add (x y : Space) :
    chevalleyQ (x + y) = chevalleyQ x + chevalleyQ y + chevalleyB x y := by
  simp only [chevalleyQ, chevalleyB, Pi.add_apply]
  ring

theorem chevalleyQ_smul (t : ℂ) (x : Space) :
    chevalleyQ (t • x) = t ^ 2 * chevalleyQ x := by
  simp only [chevalleyQ, Pi.smul_apply, smul_eq_mul]
  ring

/-- One of the first four isotropic coordinate vectors. -/
def axis (i : Fin 4) : Space :=
  fun j => if j.val = i.val then 1 else 0

/-- Its polar coefficient against the input vector. -/
def axisCoefficient (x : Space) : Fin 4 → ℂ :=
  ![x 7, -x 6, x 5, -x 4]

theorem axis_ne_zero (i : Fin 4) : axis i ≠ 0 := by
  intro h
  have hh := congrFun h (i.castAdd 4)
  simp [axis] at hh

@[simp] theorem chevalleyQ_axis (i : Fin 4) : chevalleyQ (axis i) = 0 := by
  fin_cases i <;> norm_num [chevalleyQ, axis]

theorem chevalleyQ_sub_smul_axis (x : Space) (i : Fin 4) (t : ℂ) :
    chevalleyQ (x - t • axis i) =
      chevalleyQ x - t * axisCoefficient x i := by
  fin_cases i <;>
    simp [chevalleyQ, axis, axisCoefficient, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul] <;> ring

theorem exists_axisCoefficient_ne_zero (x : Space) (hx : chevalleyQ x ≠ 0) :
    ∃ i : Fin 4, axisCoefficient x i ≠ 0 := by
  by_contra! h
  have h7 : x 7 = 0 := by simpa [axisCoefficient] using h 0
  have h6 : x 6 = 0 := by simpa [axisCoefficient] using h 1
  have h5 : x 5 = 0 := by simpa [axisCoefficient] using h 2
  have h4 : x 4 = 0 := by simpa [axisCoefficient] using h 3
  exact hx (by simp [chevalleyQ, h7, h6, h5, h4])

/-- Every vector outside the quadric is the sum of two nonzero quadric vectors.
The construction is valid for arbitrary complex coordinates and uses no square root. -/
theorem nonisotropic_decomposition (x : Space) (hx : chevalleyQ x ≠ 0) :
    ∃ u v : Space, u ≠ 0 ∧ v ≠ 0 ∧
      chevalleyQ u = 0 ∧ chevalleyQ v = 0 ∧ x = u + v := by
  obtain ⟨i, hi⟩ := exists_axisCoefficient_ne_zero x hx
  let t : ℂ := chevalleyQ x / axisCoefficient x i
  let u : Space := t • axis i
  let v : Space := x - u
  have ht : t ≠ 0 := div_ne_zero hx hi
  have hu : u ≠ 0 := by
    intro hu
    apply ht
    have hui := congrFun hu (i.castAdd 4)
    simpa [u, axis, Pi.smul_apply, smul_eq_mul] using hui
  have hqu : chevalleyQ u = 0 := by
    dsimp [u]
    rw [chevalleyQ_smul, chevalleyQ_axis]
    simp
  have hqv : chevalleyQ v = 0 := by
    dsimp [v, u]
    rw [chevalleyQ_sub_smul_axis]
    dsimp [t]
    rw [div_mul_cancel₀ _ hi, sub_self]
  have hv : v ≠ 0 := by
    intro hv
    have heq : x = u := sub_eq_zero.mp hv
    exact hx (heq ▸ hqu)
  refine ⟨u, v, hu, hv, hqu, hqv, ?_⟩
  dsimp [v]
  abel

/-- The nonzero quadric cone, with no physical interpretation built into its definition. -/
def IsQuadric (x : Space) : Prop := x ≠ 0 ∧ chevalleyQ x = 0

/-- A decomposition is an actual finite sum of nonzero quadric vectors. -/
def HasDecomposition (x : Space) (r : ℕ) : Prop :=
  ∃ g : Fin r → Space, (∀ i, IsQuadric (g i)) ∧ x = ∑ i, g i

theorem hasDecomposition_zero_iff (x : Space) :
    HasDecomposition x 0 ↔ x = 0 := by
  constructor
  · rintro ⟨g, hg, hx⟩
    simpa using hx
  · intro hx
    subst x
    refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · simp

theorem hasDecomposition_one_iff (x : Space) :
    HasDecomposition x 1 ↔ IsQuadric x := by
  constructor
  · rintro ⟨g, hg, hx⟩
    have heq : x = g 0 := by simpa using hx
    exact heq ▸ hg 0
  · intro hx
    refine ⟨fun _ => x, fun _ => hx, ?_⟩
    simp

theorem hasDecomposition_two (x : Space) (hx : chevalleyQ x ≠ 0) :
    HasDecomposition x 2 := by
  obtain ⟨u, v, hu, hv, hqu, hqv, hsum⟩ := nonisotropic_decomposition x hx
  refine ⟨![u, v], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨hu, hqu⟩
    · exact ⟨hv, hqv⟩
  · simpa using hsum

theorem decomposition_exists (x : Space) :
    ∃ r : ℕ, HasDecomposition x r := by
  by_cases hx : x = 0
  · exact ⟨0, (hasDecomposition_zero_iff x).2 hx⟩
  · by_cases hq : chevalleyQ x = 0
    · exact ⟨1, (hasDecomposition_one_iff x).2 ⟨hx, hq⟩⟩
    · exact ⟨2, hasDecomposition_two x hq⟩

/-- Minimum number of summands, defined by the decomposition predicate itself. -/
noncomputable def exactRank (x : Space) : ℕ := by
  classical
  exact Nat.find (decomposition_exists x)

theorem exactRank_spec (x : Space) : HasDecomposition x (exactRank x) := by
  classical
  exact Nat.find_spec (decomposition_exists x)

theorem exactRank_le (x : Space) {r : ℕ} (hr : HasDecomposition x r) :
    exactRank x ≤ r := by
  classical
  exact Nat.find_min' (decomposition_exists x) hr

theorem exactRank_zero_iff (x : Space) : exactRank x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hh := exactRank_spec x
    rw [h] at hh
    exact (hasDecomposition_zero_iff x).1 hh
  · intro h
    have hh := exactRank_le x ((hasDecomposition_zero_iff x).2 h)
    omega

theorem exactRank_eq_one (x : Space) (hx : IsQuadric x) : exactRank x = 1 := by
  have hle := exactRank_le x ((hasDecomposition_one_iff x).2 hx)
  have hn : exactRank x ≠ 0 := by
    intro h
    exact hx.1 ((exactRank_zero_iff x).1 h)
  omega

theorem exactRank_one_iff (x : Space) : exactRank x = 1 ↔ IsQuadric x := by
  constructor
  · intro h
    have hh := exactRank_spec x
    rw [h] at hh
    exact (hasDecomposition_one_iff x).1 hh
  · exact exactRank_eq_one x

theorem exactRank_eq_two (x : Space) (hq : chevalleyQ x ≠ 0) :
    exactRank x = 2 := by
  have hle := exactRank_le x (hasDecomposition_two x hq)
  have hn0 : exactRank x ≠ 0 := by
    intro h
    have hx := (exactRank_zero_iff x).1 h
    exact hq (hx ▸ chevalleyQ_zero)
  have hn1 : exactRank x ≠ 1 := by
    intro h
    exact hq ((exactRank_one_iff x).1 h).2
  omega

theorem exactRank_two_iff (x : Space) :
    exactRank x = 2 ↔ chevalleyQ x ≠ 0 := by
  constructor
  · intro h hq
    by_cases hx : x = 0
    · have hr := (exactRank_zero_iff x).2 hx
      omega
    · have hr := exactRank_eq_one x ⟨hx, hq⟩
      omega
  · exact exactRank_eq_two x

theorem exactRank_nonzero (x : Space) (hx : x ≠ 0) :
    exactRank x = if chevalleyQ x = 0 then 1 else 2 := by
  split_ifs with hq
  · exact exactRank_eq_one x ⟨hx, hq⟩
  · exact exactRank_eq_two x hq

/-- The four-mode vacuum-plus-full-occupancy coordinate vector. -/
def magic : Space := fun j => if j.val = 0 ∨ j.val = 7 then 1 else 0

@[simp] theorem chevalleyQ_magic : chevalleyQ magic = 1 := by
  norm_num [chevalleyQ, magic]

theorem exactRank_magic : exactRank magic = 2 :=
  exactRank_eq_two magic (by simp)

end Fermionic.FourMode

#print axioms Fermionic.FourMode.nonisotropic_decomposition
#print axioms Fermionic.FourMode.exactRank_nonzero
#print axioms Fermionic.FourMode.exactRank_magic
