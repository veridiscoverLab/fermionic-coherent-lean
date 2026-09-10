import Fermionic.PhysicalGaussianRank

/-!
Nonzero scalar transport for the same full physical Gaussian dictionary.
Every term and every cancellation are transported together. The normalized
target is the coefficient-rescaled original four-occupancy vector; no norm
or tensor-product identification is added as an assumption.
-/

noncomputable section
namespace Fermionic.GaussianScaling
open Fermionic.Fock Fermionic.PhysicalGaussian
open Fermionic.PureDecomposition (target TargetSpace)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem decomposition_smul (s : Space ℂ H) (r : ℕ)
    (c : ℂ) (hc : c ≠ 0) (hs : HasDecomposition s r) :
    HasDecomposition (c • s) r := by
  obtain ⟨g, hg, heq⟩ := hs
  refine ⟨fun i => c • g i, fun i => gaussian_smul (g i) (hg i) c hc, ?_⟩
  rw [heq, Finset.smul_sum]

/-- The number of terms is unchanged in both directions, including `r = 0`.
No restriction is placed on the Spin element of any summand. -/
theorem decomposition_smul_iff (s : Space ℂ H) (r : ℕ)
    (c : ℂ) (hc : c ≠ 0) :
    HasDecomposition (c • s) r ↔ HasDecomposition s r := by
  constructor
  · intro hs
    have h := decomposition_smul (c • s) r c⁻¹ (inv_ne_zero hc) hs
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using h
  · exact decomposition_smul s r c hc

/-- This is the original target with its four coefficients divided by two. -/
def normalizedTarget : TargetSpace := (1 / 2 : ℂ) • target

theorem normalizedTarget_decomposition_iff (r : ℕ) :
    HasDecomposition normalizedTarget r ↔ HasDecomposition target r :=
  decomposition_smul_iff target r (1 / 2) (by norm_num)

theorem target_eq_two_smul_normalizedTarget :
    target = (2 : ℂ) • normalizedTarget := by
  simp [normalizedTarget, smul_smul]

/-- The already constructed target minimum is also the minimum for the
rescaled target, without a new existence or lower-bound assumption. -/
theorem normalizedTarget_minimum :
    HasDecomposition normalizedTarget
        Fermionic.PhysicalGaussianRank.targetGaussianRank ∧
      ∀ r : ℕ, HasDecomposition normalizedTarget r →
        Fermionic.PhysicalGaussianRank.targetGaussianRank ≤ r := by
  constructor
  · exact (normalizedTarget_decomposition_iff _).mpr
      Fermionic.PhysicalGaussianRank.targetGaussianRank_spec
  · intro r hr
    exact Fermionic.PhysicalGaussianRank.targetGaussianRank_le_of_decomposition r
      ((normalizedTarget_decomposition_iff r).mp hr)

end Fermionic.GaussianScaling
