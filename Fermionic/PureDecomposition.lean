import Fermionic.Spinor
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Decompositions in the original full exterior algebra. Purity is the actual
maximal-annihilator condition. The eight-mode target and its four summands
are actual occupancy basis vectors, not numerical Gram data.
-/

noncomputable section
namespace Fermionic.PureDecomposition
open Module Fermionic.Fock Fermionic.Spinor

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]

theorem wedge_isPure {r : ℕ} (v : Fin r → E)
    (h : ExteriorAlgebra.ιMulti K r v ≠ 0) :
    IsPure (ExteriorAlgebra.ιMulti K r v) := by
  induction r with
  | zero => simpa only [ExteriorAlgebra.ιMulti_zero_apply] using (vacuum_isPure (K := K) (E := E))
  | succ r ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply] at h ⊢
      have htail : ExteriorAlgebra.ιMulti K r (Matrix.vecTail v) ≠ 0 := by
        intro hz
        exact h (by rw [hz, mul_zero])
      exact create_preserves_pure _ (ih _ htail) (v 0) h

theorem occupancy_isPure {I : Type*} [LinearOrder I] (b : Basis I K E)
    (S : Finset I) : IsPure (b.ExteriorAlgebra S) := by
  have hn := b.ExteriorAlgebra.ne_zero S
  rw [ExteriorAlgebra.basis_apply] at hn ⊢
  exact wedge_isPure _ hn

omit [FiniteDimensional K E] in
theorem annihilator_smul (a : K) (ha : a ≠ 0) (s : Space K E) :
    annihilator (a • s) = annihilator s := by
  ext z
  simp only [Spinor.mem_annihilator, map_smul]
  exact (smul_eq_zero_iff_right ha)

omit [FiniteDimensional K E] in
theorem smul_isPure (a : K) (ha : a ≠ 0) (s : Space K E) (hs : IsPure s) :
    IsPure (a • s) := by
  refine ⟨smul_ne_zero ha hs.1, ?_⟩
  rw [annihilator_smul a ha s, hs.2]

def HasPureDecomposition (s : Space K E) (r : ℕ) : Prop :=
  ∃ g : Fin r → Space K E, (∀ i, IsPure (g i)) ∧ s = ∑ i, g i

omit [FiniteDimensional K E] in
theorem decomposition_zero_iff (s : Space K E) :
    HasPureDecomposition s 0 ↔ s = 0 := by
  constructor
  · rintro ⟨g, _, hs⟩
    simpa using hs
  · rintro rfl
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩

omit [FiniteDimensional K E] in
theorem decomposition_one_iff (s : Space K E) :
    HasPureDecomposition s 1 ↔ IsPure s := by
  constructor
  · rintro ⟨g, hg, hs⟩
    have he : s = g 0 := by simpa using hs
    exact he ▸ hg 0
  · intro hs
    exact ⟨fun _ => s, fun _ => hs, by simp⟩

abbrev ModeSpace := EuclideanSpace ℂ (Fin 8)
abbrev TargetSpace := ExteriorAlgebra ℂ ModeSpace

def occupancyBasis : Basis (Finset (Fin 8)) ℂ TargetSpace :=
  (EuclideanSpace.basisFun (Fin 8) ℂ).toBasis.ExteriorAlgebra

def targetSupports : Fin 4 → Finset (Fin 8) :=
  ![∅, {0,1,2,3}, {4,5,6,7}, Finset.univ]

/-- The original unnormalized two-copy magic state, in its actual four
occupancy terms. -/
def target : TargetSpace := ∑ i : Fin 4, occupancyBasis (targetSupports i)

theorem target_four_pure : HasPureDecomposition target 4 := by
  refine ⟨fun i => occupancyBasis (targetSupports i), ?_, rfl⟩
  intro i
  exact occupancy_isPure (EuclideanSpace.basisFun (Fin 8) ℂ).toBasis (targetSupports i)

theorem target_vacuum_coefficient : occupancyBasis.repr target ∅ = 1 := by
  simp [target, targetSupports, Basis.repr_self, Fin.sum_univ_succ,
    Finset.univ_nonempty.ne_empty]

theorem target_ne_zero : target ≠ 0 := by
  intro h
  have hc := target_vacuum_coefficient
  rw [h, map_zero, Finsupp.zero_apply] at hc
  exact zero_ne_one hc

/-- The minimum exists because the original target has an actual four-term
pure decomposition. No conjectural lower bound enters this definition. -/
def targetPureRank : ℕ := by
  classical
  exact Nat.find (show ∃ r, HasPureDecomposition target r from ⟨4, target_four_pure⟩)

theorem targetPureRank_spec : HasPureDecomposition target targetPureRank := by
  classical
  exact Nat.find_spec ⟨4, target_four_pure⟩

theorem targetPureRank_le_four : targetPureRank ≤ 4 := by
  classical
  exact Nat.find_min' ⟨4, target_four_pure⟩ target_four_pure

theorem targetPureRank_pos : 0 < targetPureRank := by
  apply Nat.pos_of_ne_zero
  intro h
  have hd := targetPureRank_spec
  rw [h, decomposition_zero_iff] at hd
  exact target_ne_zero hd

end Fermionic.PureDecomposition

#print axioms Fermionic.PureDecomposition.occupancy_isPure
#print axioms Fermionic.PureDecomposition.target_four_pure
#print axioms Fermionic.PureDecomposition.targetPureRank_pos
