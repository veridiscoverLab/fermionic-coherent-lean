import Fermionic.Fock
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
Algebraic pure spinors in the actual exterior-algebra representation.
Purity means a nonzero vector whose Clifford annihilator has half the split
dimension. No equivalence with a compact Gaussian orbit is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Fermionic.Spinor

open Module
open Fermionic.Fock

variable {K : Type*} [Field K]
variable {E : Type*} [AddCommGroup E] [Module K E]

abbrev Split (K : Type*) [Field K] (E : Type*) [AddCommGroup E] [Module K E] :=
  Module.Dual K E × E

def annihilator (s : Space K E) : Submodule K (Split K E) :=
  LinearMap.ker (LinearMap.flip action s)

@[simp] theorem mem_annihilator (u : Split K E) (s : Space K E) :
    u ∈ annihilator s ↔ action u s = 0 := Iff.rfl

variable [FiniteDimensional K E]

omit [FiniteDimensional K E] in
theorem split_nondegenerate : (LinearMap.dualProd K E).Nondegenerate := by
  have hleft := (LinearMap.separatingLeft_dualProd K E).mpr
    (Module.Free.chooseBasis K E).eval_injective
  refine ⟨hleft, ?_⟩
  intro u hu
  apply hleft u
  intro v
  simpa only [LinearMap.dualProd_apply_apply, add_comm] using hu v

theorem split_finrank : finrank K (Split K E) = 2 * finrank K E := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq]
  omega

omit [FiniteDimensional K E] in
theorem annihilator_pairing_zero (s : Space K E) (hs : s ≠ 0)
    {u v : Split K E} (hu : u ∈ annihilator s) (hv : v ∈ annihilator s) :
    LinearMap.dualProd K E u v = 0 := by
  have h := action_car u v s
  rw [mem_annihilator] at hu hv
  rw [hu, hv, map_zero, map_zero, zero_add] at h
  exact (smul_eq_zero.mp h.symm).resolve_right hs

omit [FiniteDimensional K E] in
theorem annihilator_isotropic (s : Space K E) (hs : s ≠ 0) :
    annihilator s ≤ (LinearMap.dualProd K E).orthogonal (annihilator s) := by
  intro u hu v hv
  exact annihilator_pairing_zero s hs hv hu

theorem annihilator_finrank_le (s : Space K E) (hs : s ≠ 0) :
    finrank K (annihilator s) ≤ finrank K E := by
  have hle : finrank K (annihilator s) ≤
      finrank K ((LinearMap.dualProd K E).orthogonal (annihilator s)) :=
    Submodule.finrank_mono (annihilator_isotropic s hs)
  have hdim := LinearMap.BilinForm.finrank_add_finrank_orthogonal'
    (B := LinearMap.dualProd K E) (annihilator s)
  rw [split_nondegenerate.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero,
    split_finrank] at hdim
  change finrank K (annihilator s) +
    finrank K ((LinearMap.dualProd K E).orthogonal (annihilator s)) =
    2 * finrank K E at hdim
  omega

def IsPure (s : Space K E) : Prop :=
  s ≠ 0 ∧ finrank K (annihilator s) = finrank K E

theorem pure_self_orthogonal (s : Space K E) (hs : IsPure s) :
    annihilator s = (LinearMap.dualProd K E).orthogonal (annihilator s) := by
  apply Submodule.eq_of_le_of_finrank_le (annihilator_isotropic s hs.1)
  rw [LinearMap.BilinForm.finrank_orthogonal split_nondegenerate,
    split_finrank, hs.2]
  omega

omit [FiniteDimensional K E] in
/-- The unchanged annihilator directions orthogonal to the applied vector
still annihilate the new state. This is an equality in the full Fock space. -/
theorem intersection_annihilates (s : Space K E) (z : Split K E) :
    annihilator s ⊓ LinearMap.ker (LinearMap.dualProd K E z) ≤
      annihilator (action z s) := by
  intro w hw
  change action w (action z s) = 0
  have h := action_car z w s
  have hw0 : action w s = 0 := hw.1
  have hzw : LinearMap.dualProd K E z w = 0 := hw.2
  rw [hw0, map_zero, zero_add, hzw, zero_smul] at h
  exact h

omit [FiniteDimensional K E] in
theorem null_self_annihilates (s : Space K E) (z : Split K E) (hz : z.1 z.2 = 0) :
    z ∈ annihilator (action z s) := by
  change action z (action z s) = 0
  rw [action_square, hz, zero_smul]

/-- Intersecting any finite-dimensional subspace with the kernel of one
functional loses at most one dimension. -/
theorem hyperplane_dimension (L : Submodule K (Split K E))
    (f : Module.Dual K (Split K E)) :
    finrank K L ≤ finrank K ((L ⊓ LinearMap.ker f) : Submodule K (Split K E)) + 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := K) (V := L) (V₂ := K)
    (f.domRestrict L)
  have hr : finrank K (LinearMap.range (f.domRestrict L)) ≤ 1 := by
    simpa using (Submodule.finrank_le (LinearMap.range (f.domRestrict L)))
  have hk : finrank K (LinearMap.ker (f.domRestrict L)) =
      finrank K ((L ⊓ LinearMap.ker f) : Submodule K (Split K E)) := by
    rw [LinearMap.ker_domRestrict, ← Submodule.finrank_map_subtype_eq L,
      Submodule.map_comap_subtype]
  rw [hk] at h
  omega

/-- Every nonzero isotropic Clifford multiplication preserves purity.
All dimension bounds and CAR relations are proved for the actual Fock action. -/
theorem null_action_preserves_pure (s : Space K E) (hs : IsPure s)
    (z : Split K E) (hz : z.1 z.2 = 0) (hnew : action z s ≠ 0) :
    IsPure (action z s) := by
  refine ⟨hnew, ?_⟩
  let L := annihilator s ⊓ LinearMap.ker (LinearMap.dualProd K E z)
  have hznot : z ∉ L := by
    intro h
    exact hnew h.1
  have hz0 : z ≠ 0 := by
    intro h
    apply hznot
    rw [h]
    exact L.zero_mem
  have hdis : Disjoint L (K ∙ z) :=
    Submodule.disjoint_span_singleton_of_notMem hznot
  have hd := Submodule.finrank_sup_add_finrank_inf_eq L (K ∙ z)
  rw [hdis.eq_bot, finrank_bot, add_zero, finrank_span_singleton hz0] at hd
  have hlow := hyperplane_dimension (annihilator s) (LinearMap.dualProd K E z)
  rw [hs.2] at hlow
  have hsub : L ⊔ (K ∙ z) ≤ annihilator (action z s) := by
    apply sup_le
    · exact intersection_annihilates s z
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr
        (null_self_annihilates s z hz)
  have hmono := Submodule.finrank_mono hsub
  have hup := annihilator_finrank_le (action z s) hnew
  change finrank K E ≤ finrank K L + 1 at hlow
  omega

theorem create_preserves_pure (s : Space K E) (hs : IsPure s)
    (v : E) (hnew : create v s ≠ 0) : IsPure (create v s) := by
  have heq : action ((0 : Module.Dual K E), v) s = create v s := by
    simp [action_apply, annihilate]
  rw [← heq] at hnew ⊢
  exact null_action_preserves_pure s hs _ (by simp) hnew

theorem annihilate_preserves_pure (s : Space K E) (hs : IsPure s)
    (f : Module.Dual K E) (hnew : annihilate f s ≠ 0) : IsPure (annihilate f s) := by
  have heq : action (f, (0 : E)) s = annihilate f s := by
    simp [action_apply, create]
  rw [← heq] at hnew ⊢
  exact null_action_preserves_pure s hs _ (by simp) hnew

theorem occupation_preserves_pure (s : Space K E) (hs : IsPure s)
    (f : Module.Dual K E) (v : E) (hnew : occupation f v s ≠ 0) :
    IsPure (occupation f v s) := by
  have ha : annihilate f s ≠ 0 := by
    intro h
    apply hnew
    change create v (annihilate f s) = 0
    rw [h, map_zero]
  exact create_preserves_pure _ (annihilate_preserves_pure s hs f ha) v hnew

theorem vacancy_preserves_pure (s : Space K E) (hs : IsPure s)
    (f : Module.Dual K E) (v : E) (hnew : vacancy f v s ≠ 0) :
    IsPure (vacancy f v s) := by
  have hc : create v s ≠ 0 := by
    intro h
    apply hnew
    change annihilate f (create v s) = 0
    rw [h, map_zero]
  exact annihilate_preserves_pure _ (create_preserves_pure s hs v hc) f hnew

/-- Apply the entire ordered history in the original exterior algebra.
The head of the list acts first. -/
def historyOperator : List (Split K E) → Module.End K (Space K E)
  | [] => 1
  | z :: zs => historyOperator zs * action z

/-- A finite history of isotropic Clifford operations preserves purity
whenever its final output is nonzero. Intermediate nonvanishing is derived,
not added to the input assumptions. -/
theorem null_history_preserves_pure (zs : List (Split K E))
    (hnull : ∀ z ∈ zs, z.1 z.2 = 0) (s : Space K E) (hs : IsPure s)
    (hfinal : historyOperator zs s ≠ 0) : IsPure (historyOperator zs s) := by
  induction zs generalizing s with
  | nil => simpa [historyOperator] using hs
  | cons z zs ih =>
    have hfirst : action z s ≠ 0 := by
      intro hz
      apply hfinal
      change historyOperator zs (action z s) = 0
      rw [hz, map_zero]
    have hp := null_action_preserves_pure s hs z
      (hnull z (List.mem_cons_self)) hfirst
    exact ih (fun w hw => hnull w (List.mem_cons_of_mem z hw)) (action z s) hp hfinal

omit [FiniteDimensional K E] in
theorem mem_vacuum_annihilator (u : Split K E) :
    u ∈ annihilator (1 : Space K E) ↔ u.2 = 0 := by
  simp [mem_annihilator, action_apply, annihilate, create,
    ExteriorAlgebra.ι_eq_zero_iff]

/-- The vacuum annihilator is explicitly the entire dual of E. -/
def vacuumAnnihilatorEquiv : annihilator (1 : Space K E) ≃ₗ[K] Module.Dual K E where
  toFun u := u.1.1
  invFun f := ⟨(f, 0), (mem_vacuum_annihilator _).mpr rfl⟩
  left_inv u := by
    apply Subtype.ext
    exact Prod.ext rfl ((mem_vacuum_annihilator _).mp u.2).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional K E] in
theorem vacuum_isPure : IsPure (1 : Space K E) := by
  refine ⟨one_ne_zero, ?_⟩
  rw [vacuumAnnihilatorEquiv.finrank_eq, Subspace.dual_finrank_eq]

end Fermionic.Spinor
