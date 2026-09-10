import Mathlib.Analysis.Matrix.Order

/-!
# Rigidity of an actual positive semidefinite density matrix

These lemmas concern `Matrix.PosSemidef` over `ℂ`; no entrywise
Cauchy--Schwarz bound or rank-one condition is assumed.  They provide the
finite-dimensional positivity step used in `wehrl.tex` lines 190--191 and
406--412.  They do not by themselves formalize the fermionic representations,
their conditional states, or either Husimi theorem.
-/

namespace Fermionic.DensityRigidity

open Matrix
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A zero diagonal entry of a complex positive semidefinite matrix forces
the corresponding entire column to vanish. -/
theorem column_eq_zero_of_diag_eq_zero {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) {i : ι} (hii : A i i = 0) :
    ∀ j, A j i = 0 := by
  have hq : star (Pi.single i (1 : ℂ)) ⬝ᵥ
      (A *ᵥ Pi.single i (1 : ℂ)) = 0 := by
    simpa using hii
  have hz := (hA.dotProduct_mulVec_zero_iff (Pi.single i (1 : ℂ))).mp hq
  intro j
  simpa using congrFun hz j

/-- The corresponding row also vanishes, by the Hermitian property already
contained in `Matrix.PosSemidef`. -/
theorem row_eq_zero_of_diag_eq_zero {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) {i : ι} (hii : A i i = 0) :
    ∀ j, A i j = 0 := by
  intro j
  rw [← hA.isHermitian.apply i j,
    column_eq_zero_of_diag_eq_zero hA hii j, star_zero]

theorem row_and_column_eq_zero_of_diag_eq_zero {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) {i : ι} (hii : A i i = 0) :
    (∀ j, A i j = 0) ∧ (∀ j, A j i = 0) :=
  ⟨row_eq_zero_of_diag_eq_zero hA hii,
    column_eq_zero_of_diag_eq_zero hA hii⟩

/-- The actual outer-product matrix of the i-th standard unit vector. -/
noncomputable def basisProjector (i : ι) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (Pi.single i (1 : ℂ)) (star (Pi.single i (1 : ℂ)))

omit [Fintype ι] in
@[simp] theorem basisProjector_apply (i j k : ι) :
    basisProjector i j k = if j = i ∧ k = i then 1 else 0 := by
  by_cases hj : j = i <;> by_cases hk : k = i <;>
    simp [basisProjector, Matrix.vecMulVec, Pi.single_apply, hj, hk]

/-- With trace one, a positive semidefinite matrix whose other diagonal
entries vanish is exactly the standard basis pure-state projector. -/
theorem eq_basisProjector_of_trace_eq_one {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 1) (i : ι)
    (hdiag : ∀ j, j ≠ i → A j j = 0) :
    A = basisProjector i := by
  have htrace' : A.trace = A i i := by
    unfold Matrix.trace
    exact Finset.sum_eq_single i
      (fun j _ hji => hdiag j hji)
      (fun hi => (hi (Finset.mem_univ i)).elim)
  have hii : A i i = 1 := htrace'.symm.trans htrace
  ext j k
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · subst k
      simpa using hii
    · have hik := column_eq_zero_of_diag_eq_zero hA (hdiag k hk) i
      simpa [hk] using hik
  · have hjk := row_eq_zero_of_diag_eq_zero hA (hdiag j hj) k
    simpa [hj] using hjk

omit [DecidableEq ι] in
/-- Zero conditional trace forces the entire positive compression to vanish. -/
theorem eq_zero_of_trace_eq_zero {A : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (htrace : A.trace = 0) : A = 0 :=
  hA.trace_eq_zero_iff.mp htrace

end Fermionic.DensityRigidity

#check @Fermionic.DensityRigidity.column_eq_zero_of_diag_eq_zero
#check @Fermionic.DensityRigidity.row_eq_zero_of_diag_eq_zero
#check @Fermionic.DensityRigidity.eq_basisProjector_of_trace_eq_one
#check @Fermionic.DensityRigidity.eq_zero_of_trace_eq_zero

#print axioms Fermionic.DensityRigidity.column_eq_zero_of_diag_eq_zero
#print axioms Fermionic.DensityRigidity.row_eq_zero_of_diag_eq_zero
#print axioms Fermionic.DensityRigidity.eq_basisProjector_of_trace_eq_one
#print axioms Fermionic.DensityRigidity.eq_zero_of_trace_eq_zero
