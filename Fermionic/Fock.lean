import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
import Mathlib.LinearAlgebra.QuadraticForm.Dual
import Mathlib.Tactic.Abel

/-!
The actual algebraic Fock space is mathlib's exterior algebra, not an
unspecified representation satisfying CAR by assumption. The split vector
space is ordered as E* × E, to agree with `QuadraticForm.dualProd`.
No Hilbert adjoint or compact Spin identification is asserted here.
-/

noncomputable section

namespace Fermionic.Fock

variable {R : Type*} [CommRing R]
variable {E : Type*} [AddCommGroup E] [Module R E]

abbrev Space (R : Type*) [CommRing R] (E : Type*) [AddCommGroup E] [Module R E] :=
  ExteriorAlgebra R E

def create (v : E) : Module.End R (Space R E) :=
  (Algebra.lmul R (Space R E)).toLinearMap (ExteriorAlgebra.ι R v)

def annihilate (f : Module.Dual R E) : Module.End R (Space R E) :=
  CliffordAlgebra.contractLeft f

@[simp] theorem create_apply (v : E) (s : Space R E) :
    create v s = ExteriorAlgebra.ι R v * s := rfl

@[simp] theorem annihilate_apply (f : Module.Dual R E) (s : Space R E) :
    annihilate f s = CliffordAlgebra.contractLeft f s := rfl

theorem create_square (v : E) (s : Space R E) : create v (create v s) = 0 := by
  rw [create_apply, create_apply, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul]

theorem annihilate_square (f : Module.Dual R E) (s : Space R E) :
    annihilate f (annihilate f s) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft f s

theorem mixed_car (f : Module.Dual R E) (v : E) (s : Space R E) :
    annihilate f (create v s) + create v (annihilate f s) = f v • s := by
  simp only [annihilate_apply, create_apply, CliffordAlgebra.contractLeft_ι_mul]
  exact sub_add_cancel _ _

def action : (Module.Dual R E × E) →ₗ[R] Module.End R (Space R E) :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R E))).comp
      (LinearMap.fst R (Module.Dual R E) E) +
    ((Algebra.lmul R (Space R E)).toLinearMap.comp (ExteriorAlgebra.ι R)).comp
      (LinearMap.snd R (Module.Dual R E) E)

@[simp] theorem action_apply (u : Module.Dual R E × E) (s : Space R E) :
    action u s = annihilate u.1 s + create u.2 s := rfl

theorem action_square (u : Module.Dual R E × E) (s : Space R E) :
    action u (action u s) = u.1 u.2 • s := by
  simp only [action_apply, map_add, annihilate_square, create_square, zero_add, add_zero]
  exact (add_comm _ _).trans (mixed_car u.1 u.2 s)

theorem action_square_end (u : Module.Dual R E × E) :
    action u * action u = algebraMap R (Module.End R (Space R E))
      (QuadraticForm.dualProd R E u) := by
  ext s
  exact action_square u s

theorem action_car (u v : Module.Dual R E × E) (s : Space R E) :
    action u (action v s) + action v (action u s) =
      (LinearMap.dualProd R E u v) • s := by
  have hp := action_square (u + v) s
  have hu := action_square u s
  have hv := action_square v s
  simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add,
    add_smul] at hp
  simp only [LinearMap.dualProd_apply_apply]
  calc
    action u (action v s) + action v (action u s) =
        (action u (action u s) + action v (action u s) +
          (action u (action v s) + action v (action v s))) -
          action u (action u s) - action v (action v s) := by abel
    _ = ((u.1 u.2 • s + v.1 u.2 • s) +
          (u.1 v.2 • s + v.1 v.2 • s)) - u.1 u.2 • s - v.1 v.2 • s := by
      rw [hp, hu, hv]
    _ = (v.1 u.2 + u.1 v.2) • s := by rw [add_smul]; abel

/-- The genuine algebra homomorphism from the split Clifford algebra into
the endomorphisms of the full exterior algebra. -/
def representation :
    CliffordAlgebra (QuadraticForm.dualProd R E) →ₐ[R] Module.End R (Space R E) :=
  CliffordAlgebra.lift _ ⟨action, action_square_end⟩

@[simp] theorem representation_generator (u : Module.Dual R E × E) :
    representation (CliffordAlgebra.ι (QuadraticForm.dualProd R E) u) = action u :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- Occupation and vacancy are algebraic complementary idempotents whenever
the chosen covector and vector pair to one. No orthogonality is assumed. -/
def occupation (f : Module.Dual R E) (v : E) : Module.End R (Space R E) :=
  create v * annihilate f

def vacancy (f : Module.Dual R E) (v : E) : Module.End R (Space R E) :=
  annihilate f * create v

theorem occupation_vacancy (f : Module.Dual R E) (v : E) (h : f v = 1)
    (s : Space R E) : occupation f v s + vacancy f v s = s := by
  have hc := mixed_car f v s
  rw [h, one_smul] at hc
  exact (add_comm _ _).trans hc

theorem occupation_idempotent (f : Module.Dual R E) (v : E) (h : f v = 1)
    (s : Space R E) : occupation f v (occupation f v s) = occupation f v s := by
  change create v (annihilate f (create v (annihilate f s))) = _
  have hc := mixed_car f v (annihilate f s)
  rw [annihilate_square, map_zero, add_zero, h, one_smul] at hc
  rw [hc]
  rfl

theorem vacancy_idempotent (f : Module.Dual R E) (v : E) (h : f v = 1)
    (s : Space R E) : vacancy f v (vacancy f v s) = vacancy f v s := by
  change annihilate f (create v (annihilate f (create v s))) = _
  have hc := mixed_car f v (create v s)
  rw [create_square, map_zero, zero_add, h, one_smul] at hc
  rw [hc]
  rfl

theorem vacancy_occupation_zero (f : Module.Dual R E) (v : E) (s : Space R E) :
    vacancy f v (occupation f v s) = 0 := by
  change annihilate f (create v (create v (annihilate f s))) = 0
  rw [create_square, map_zero]

theorem occupation_vacancy_zero (f : Module.Dual R E) (v : E) (s : Space R E) :
    occupation f v (vacancy f v s) = 0 := by
  change create v (annihilate f (annihilate f (create v s))) = 0
  rw [annihilate_square, map_zero]

end Fermionic.Fock
