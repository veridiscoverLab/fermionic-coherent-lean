import Fermionic.Fock
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Module

/-!
The joint kernel of all actual annihilation operators on finite-dimensional
exterior Fock space is exactly the scalar vacuum line. The proof derives the
number operator from the same basis and its exact CAR, then reads all original
occupancy coordinates simultaneously.
-/

noncomputable section
namespace Fermionic.FockVacuumKernel

open Module Fermionic.Fock

variable {K E I : Type*} [Field K] [AddCommGroup E] [Module K E]
variable [Fintype I]

def numberOperator (b : Basis I K E) : Module.End K (Space K E) :=
  ∑ i, occupation (b.coord i) (b i)

theorem numberOperator_apply (b : Basis I K E) (s : Space K E) :
    numberOperator b s = ∑ i, create (b i) (annihilate (b.coord i) s) := by
  simp only [numberOperator, LinearMap.sum_apply, occupation, Module.End.mul_apply]

theorem numberOperator_one (b : Basis I K E) : numberOperator b (1 : Space K E) = 0 := by
  simp [numberOperator_apply, annihilate]

theorem create_swap (v w : E) (s : Space K E) :
    create v (create w s) = -create w (create v s) := by
  have h := congrArg (fun a : Space K E => a * s)
    (ExteriorAlgebra.ι_add_mul_swap (R := K) (M := E) v w)
  simp only [add_mul, zero_mul, mul_assoc] at h
  exact eq_neg_of_add_eq_zero_left h

theorem numberOperator_create (b : Basis I K E) (v : E) (s : Space K E) :
    numberOperator b (create v s) = create v s + create v (numberOperator b s) := by
  have hterm (i : I) :
      create (b i) (annihilate (b.coord i) (create v s)) =
        (b.coord i v) • create (b i) s + create v (create (b i) (annihilate (b.coord i) s)) := by
    have hc := mixed_car (b.coord i) v s
    have ha : annihilate (b.coord i) (create v s) =
        b.coord i v • s - create v (annihilate (b.coord i) s) :=
      eq_sub_of_add_eq hc
    rw [ha, map_sub, map_smul, create_swap, sub_neg_eq_add]
  rw [numberOperator_apply, numberOperator_apply]
  simp only [hterm, Finset.sum_add_distrib, ← map_sum]
  congr 1
  simp only [create_apply, ← smul_mul_assoc, ← Finset.sum_mul, ← map_smul, ← map_sum]
  rw [show (∑ i, b.coord i v • b i) = v from b.sum_repr v]

theorem numberOperator_wedge (b : Basis I K E) {r : ℕ} (v : Fin r → E) :
    numberOperator b (ExteriorAlgebra.ιMulti K r v) =
      (r : K) • ExteriorAlgebra.ιMulti K r v := by
  induction r with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, numberOperator_one]
  | succ r ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change numberOperator b (create (v 0) (ExteriorAlgebra.ιMulti K r (Matrix.vecTail v))) = _
    rw [numberOperator_create, ih, map_smul, Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    exact add_comm _ _

variable [LinearOrder I]

theorem numberOperator_basis (b : Basis I K E) (S : Finset I) :
    numberOperator b (b.ExteriorAlgebra S) = (S.card : K) • b.ExteriorAlgebra S := by
  rw [ExteriorAlgebra.basis_apply]
  exact numberOperator_wedge b _

theorem numberOperator_coord (b : Basis I K E) (S : Finset I) :
    (b.ExteriorAlgebra.coord S).comp (numberOperator b) =
      (S.card : K) • b.ExteriorAlgebra.coord S := by
  apply b.ExteriorAlgebra.ext
  intro T
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, numberOperator_basis, map_smul,
    Basis.coord_apply, Basis.repr_self_apply]
  by_cases h : T = S
  · subst T
    rfl
  · simp [h]

omit [LinearOrder I] in
theorem numberOperator_zero_of_annihilated (b : Basis I K E) (s : Space K E)
    (hs : ∀ f : Module.Dual K E, annihilate f s = 0) : numberOperator b s = 0 := by
  simp only [numberOperator_apply, hs, map_zero, Finset.sum_const_zero]

theorem nonempty_coordinate_zero [CharZero K] (b : Basis I K E) (s : Space K E)
    (hs : ∀ f : Module.Dual K E, annihilate f s = 0) (S : Finset I) (hS : S ≠ ∅) :
    b.ExteriorAlgebra.coord S s = 0 := by
  have hn := numberOperator_zero_of_annihilated b s hs
  have h := LinearMap.congr_fun (numberOperator_coord b S) s
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [hn, map_zero] at h
  have hc : (S.card : K) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
  exact (smul_eq_zero.mp h.symm).resolve_left hc

/-- The scalar is the existing augmentation of the actual exterior algebra,
not an independently specified coefficient functional. -/
theorem vacuum_kernel_with_basis [CharZero K] (b : Basis I K E) (s : Space K E)
    (hs : ∀ f : Module.Dual K E, annihilate f s = 0) :
    s = ExteriorAlgebra.algebraMapInv s • (1 : Space K E) := by
  classical
  have he : s = (b.ExteriorAlgebra.coord ∅ s) • b.ExteriorAlgebra ∅ := by
    apply b.ExteriorAlgebra.repr.injective
    ext S
    by_cases hS : S = ∅
    · subst S
      simp [Basis.coord_apply]
    · simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_apply]
      rw [if_neg (Ne.symm hS), smul_zero]
      exact nonempty_coordinate_zero b s hs S hS
  have h0 : b.ExteriorAlgebra ∅ = (1 : Space K E) := by
    rw [ExteriorAlgebra.basis_apply]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  rw [h0] at he
  have hc : ExteriorAlgebra.algebraMapInv s = b.ExteriorAlgebra.coord ∅ s := by
    have hh := congrArg (fun a : Space K E => ExteriorAlgebra.algebraMapInv a) he
    simpa only [map_smul, map_one, smul_eq_mul, mul_one] using hh
  exact he.trans (by rw [hc])

omit [Fintype I] [LinearOrder I] in
theorem joint_annihilation_kernel [FiniteDimensional K E] [CharZero K] (s : Space K E)
    (hs : ∀ f : Module.Dual K E, annihilate f s = 0) :
    s = ExteriorAlgebra.algebraMapInv s • (1 : Space K E) :=
  vacuum_kernel_with_basis (Module.finBasis K E) s hs

omit [Fintype I] [LinearOrder I] in
theorem joint_annihilation_iff_vacuum [FiniteDimensional K E] [CharZero K] (s : Space K E) :
    (∀ f : Module.Dual K E, annihilate f s = 0) ↔
      s = ExteriorAlgebra.algebraMapInv s • (1 : Space K E) := by
  refine ⟨joint_annihilation_kernel s, ?_⟩
  intro hs f
  rw [hs, map_smul]
  simp [annihilate]

end Fermionic.FockVacuumKernel
