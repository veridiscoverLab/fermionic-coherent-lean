import Mathlib.Algebra.MvPolynomial.Funext

/-!
Polynomial extension across a degeneracy set. This supplies the algebraic
boundary step of the rank route; construction of the actual pure-spinor
deformation and its nonzero discriminant remains a separate obligation.
-/

namespace Fermionic.PolynomialBoundary
open MvPolynomial

variable {K σ : Type*} [CommRing K] [IsDomain K] [Infinite K]

/-- A polynomial vanishing wherever a fixed nonzero polynomial does not
vanish is identically zero. No topology, generic-point or density assumption
is needed, and the variables need not form a finite type. -/
theorem eq_zero_of_vanish_off_zero (P D : MvPolynomial σ K) (hD : D ≠ 0)
    (h : ∀ x : σ → K, eval x D ≠ 0 → eval x P = 0) : P = 0 := by
  have hprod : P * D = 0 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_mul, map_zero]
    by_cases hx : eval x D = 0
    · simp [hx]
    · simp [h x hx]
  exact (mul_eq_zero.mp hprod).resolve_right hD

/-- The same identity holds on every boundary specialization, including
the original undeformed vector. -/
theorem eval_eq_zero_at_boundary (P D : MvPolynomial σ K) (hD : D ≠ 0)
    (h : ∀ x : σ → K, eval x D ≠ 0 → eval x P = 0) (x : σ → K) :
    eval x P = 0 := by
  rw [eq_zero_of_vanish_off_zero P D hD h, map_zero]

end Fermionic.PolynomialBoundary

#print axioms Fermionic.PolynomialBoundary.eq_zero_of_vanish_off_zero
#print axioms Fermionic.PolynomialBoundary.eval_eq_zero_at_boundary
