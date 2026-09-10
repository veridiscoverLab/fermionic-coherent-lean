import Fermionic.PhysicalOccupancy

/-!
The minimum number of actual Euclidean-Spin vacuum-orbit cone terms for the
unchanged eight-mode target. Existence is proved only for this target, using
its original four occupancy terms; no global finite-decomposition hypothesis
is introduced.

Scope: `PhysicalGaussian.IsGaussian` is the nonzero complex cone over the
vacuum Spin orbit, corresponding to the even branch in `rank:def` of the
paper. This module does not define a dictionary additionally containing the
odd branch, or formalize the paper's parity-projection deletion argument.
It does not claim equality of these two dictionary minima, nor rank four.
-/

noncomputable section
namespace Fermionic.PhysicalGaussianRank

open Fermionic.Fock Fermionic.PhysicalGaussian Fermionic.PhysicalOccupancy
open Fermionic.PureDecomposition (target targetPureRank)

theorem target_decomposable : ∃ r : ℕ, HasDecomposition target r :=
  ⟨4, target_has_gaussian_decomposition⟩

/-- The minimum for the same original target, with the physical orbit
dictionary and unrestricted complex coefficients already inside each term. -/
def targetGaussianRank : ℕ := by
  classical
  exact Nat.find target_decomposable

theorem targetGaussianRank_spec : HasDecomposition target targetGaussianRank := by
  classical
  exact Nat.find_spec target_decomposable

theorem targetGaussianRank_le_of_decomposition (r : ℕ)
    (hr : HasDecomposition target r) : targetGaussianRank ≤ r := by
  classical
  exact Nat.find_min' target_decomposable hr

theorem targetGaussianRank_min (r : ℕ) (hr : r < targetGaussianRank) :
    ¬HasDecomposition target r := by
  intro h
  exact (Nat.not_le_of_gt hr) (targetGaussianRank_le_of_decomposition r h)

theorem targetGaussianRank_le_four : targetGaussianRank ≤ 4 :=
  targetGaussianRank_le_of_decomposition 4 target_has_gaussian_decomposition

theorem decomposition_zero_iff {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (s : Space ℂ H) :
    HasDecomposition s 0 ↔ s = 0 := by
  constructor
  · rintro ⟨g, _, hs⟩
    simpa using hs
  · rintro rfl
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, by simp⟩

theorem targetGaussianRank_pos : 0 < targetGaussianRank := by
  apply Nat.pos_of_ne_zero
  intro h
  have hd := targetGaussianRank_spec
  rw [h, decomposition_zero_iff] at hd
  exact Fermionic.PureDecomposition.target_ne_zero hd

theorem one_le_targetGaussianRank : 1 ≤ targetGaussianRank := targetGaussianRank_pos

/-- Every actual physical decomposition remains a decomposition of the same
original full vectors in the algebraic pure-spinor dictionary. Hence its
minimum cannot be smaller than the algebraic pure minimum. -/
theorem targetPureRank_le_targetGaussianRank : targetPureRank ≤ targetGaussianRank := by
  classical
  exact Nat.find_min'
    (show ∃ r, Fermionic.PureDecomposition.HasPureDecomposition target r from
      ⟨4, Fermionic.PureDecomposition.target_four_pure⟩)
    (decomposition_implies_pure target targetGaussianRank targetGaussianRank_spec)

theorem targetGaussianRank_bounds : 1 ≤ targetGaussianRank ∧ targetGaussianRank ≤ 4 :=
  ⟨one_le_targetGaussianRank, targetGaussianRank_le_four⟩

end Fermionic.PhysicalGaussianRank
