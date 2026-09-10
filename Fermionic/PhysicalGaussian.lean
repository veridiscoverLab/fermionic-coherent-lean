import Fermionic.SpinorTransport
import Fermionic.PureDecomposition

/-!
The dictionary is the nonzero complex cone over the real Euclidean Spin
vacuum orbit in the actual full Fock representation. The target comparison
to algebraic pure decompositions is proved in the necessary direction.
-/

noncomputable section
namespace Fermionic.PhysicalGaussian
open Module Fermionic.Fock Fermionic.Spinor Fermionic.SpinorTransport

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsGaussian (s : Space ℂ H) : Prop :=
  ∃ (x : spinGroup (majoranaQuadratic (H := H))) (c : ℂ),
    c ≠ 0 ∧ s = c • euclideanSpinAction x (1 : Space ℂ H)

def HasDecomposition (s : Space ℂ H) (r : ℕ) : Prop :=
  ∃ g : Fin r → Space ℂ H, (∀ i, IsGaussian (g i)) ∧ s = ∑ i, g i

theorem gaussian_isPure [FiniteDimensional ℂ H] (s : Space ℂ H)
    (hs : IsGaussian s) : IsPure s := by
  obtain ⟨x, c, hc, rfl⟩ := hs
  exact euclideanSpin_vacuum_ray_isPure x c hc

/-- Every term of the same original physical decomposition becomes a pure
term, preserving its vector, coefficient and all cancellations exactly. -/
theorem decomposition_implies_pure [FiniteDimensional ℂ H]
    (s : Space ℂ H) (r : ℕ) (hs : HasDecomposition s r) :
    Fermionic.PureDecomposition.HasPureDecomposition s r := by
  obtain ⟨g, hg, heq⟩ := hs
  exact ⟨g, fun i => gaussian_isPure (g i) (hg i), heq⟩

theorem vacuum_isGaussian : IsGaussian (1 : Space ℂ H) := by
  refine ⟨1, 1, one_ne_zero, ?_⟩
  simp [euclideanSpinAction]

theorem gaussian_smul (s : Space ℂ H) (hs : IsGaussian s)
    (a : ℂ) (ha : a ≠ 0) : IsGaussian (a • s) := by
  obtain ⟨x, c, hc, rfl⟩ := hs
  exact ⟨x, a*c, mul_ne_zero ha hc, smul_smul a c _⟩

end Fermionic.PhysicalGaussian

#print axioms Fermionic.PhysicalGaussian.gaussian_isPure
#print axioms Fermionic.PhysicalGaussian.decomposition_implies_pure
