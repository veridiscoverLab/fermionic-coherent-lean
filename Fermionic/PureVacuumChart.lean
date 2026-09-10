import Fermionic.Spinor

/-!
The actual annihilator chart over a nonzero vacuum coefficient. All graph
directions are constructed from the same original pure Fock vector. This
does not yet assert its reconstruction as an exterior exponential.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Fermionic.PureVacuumChart
open Module Fermionic.Fock Fermionic.Spinor

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

def vacuumCoefficient : Space K E →ₐ[K] K := ExteriorAlgebra.algebraMapInv

@[simp] theorem vacuumCoefficient_create (v : E) (s : Space K E) :
    vacuumCoefficient (create v s) = 0 := by
  simp [vacuumCoefficient, create_apply, ExteriorAlgebra.algebraMapInv]

theorem vacuumCoefficient_annihilate_create (f : Module.Dual K E)
    (v : E) (s : Space K E) :
    vacuumCoefficient (annihilate f (create v s)) = f v * vacuumCoefficient s := by
  have h := congrArg (vacuumCoefficient (K := K) (E := E)) (mixed_car f v s)
  simpa only [map_add, vacuumCoefficient_create, add_zero, map_smul,
    smul_eq_mul] using h

/-- A nonzero original vacuum coefficient makes multiplication by creation
vectors injective on the one-particle input. -/
theorem creator_eq_zero_of_vacuum_ne_zero (s : Space K E)
    (h0 : vacuumCoefficient s ≠ 0) (v : E) (hv : create v s = 0) : v = 0 := by
  apply (Module.Free.chooseBasis K E).eval_injective
  ext f
  have h := vacuumCoefficient_annihilate_create f v s
  rw [hv, map_zero, map_zero] at h
  have hf := (mul_eq_zero.mp h.symm).resolve_right h0
  simpa using hf

def annihilatorProjection (s : Space K E) :
    annihilator s →ₗ[K] Module.Dual K E :=
  (LinearMap.fst K (Module.Dual K E) E).comp (annihilator s).subtype

theorem annihilatorProjection_injective (s : Space K E)
    (h0 : vacuumCoefficient s ≠ 0) : Function.Injective (annihilatorProjection s) := by
  intro u v huv
  have hfst : (u : Split K E).1 - (v : Split K E).1 = 0 := sub_eq_zero.mpr huv
  have hw := (annihilator s).sub_mem u.property v.property
  have hcreate : create ((u : Split K E).2 - (v : Split K E).2) s = 0 := by
    change action ((u : Split K E) - (v : Split K E)) s = 0 at hw
    simpa only [action_apply, Prod.fst_sub, Prod.snd_sub, hfst,
      annihilate, map_zero, LinearMap.zero_apply, zero_add] using hw
  apply Subtype.ext
  apply Prod.ext huv
  exact sub_eq_zero.mp (creator_eq_zero_of_vacuum_ne_zero s h0 _ hcreate)

variable [FiniteDimensional K E]

theorem annihilatorProjection_surjective (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) : Function.Surjective (annihilatorProjection s) := by
  have hi := annihilatorProjection_injective s h0
  have hd := LinearMap.finrank_range_add_finrank_ker
    (K := K) (V := annihilator s) (V₂ := Module.Dual K E) (annihilatorProjection s)
  have hk : LinearMap.ker (annihilatorProjection s) = ⊥ := by
    apply bot_unique
    intro z hz
    change z = 0
    apply hi
    exact hz.trans (map_zero (annihilatorProjection s)).symm
  rw [hk, finrank_bot, add_zero, hs.2] at hd
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_of_le_of_finrank_le (show LinearMap.range (annihilatorProjection s) ≤ ⊤ from le_top)
  simpa only [finrank_top, Subspace.dual_finrank_eq] using hd.ge

/-- A genuine equivalence of the full original annihilator with the whole
dual one-particle space, constructed from purity and the original scalar. -/
def annihilatorProjectionEquiv (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) : annihilator s ≃ₗ[K] Module.Dual K E :=
  LinearEquiv.ofBijective (annihilatorProjection s)
    ⟨annihilatorProjection_injective s h0, annihilatorProjection_surjective s hs h0⟩

def graphDirection (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) : Module.Dual K E →ₗ[K] E :=
  (LinearMap.snd K (Module.Dual K E) E).comp
    ((annihilator s).subtype.comp (annihilatorProjectionEquiv s hs h0).symm.toLinearMap)

theorem graphDirection_mem_annihilator (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) (f : Module.Dual K E) :
    (f, graphDirection s hs h0 f) ∈ annihilator s := by
  let z := (annihilatorProjectionEquiv s hs h0).symm f
  have hf : (z : Split K E).1 = f :=
    (annihilatorProjectionEquiv s hs h0).apply_symm_apply f
  have he : (f, graphDirection s hs h0 f) = (z : Split K E) := Prod.ext hf.symm rfl
  rw [he]
  exact z.property

theorem graphDirection_annihilates (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) (f : Module.Dual K E) :
    annihilate f s + create (graphDirection s hs h0 f) s = 0 :=
  graphDirection_mem_annihilator s hs h0 f

/-- The common graph is alternating by the actual CAR pairing. -/
theorem graphDirection_skew (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) (f g : Module.Dual K E) :
    f (graphDirection s hs h0 g) + g (graphDirection s hs h0 f) = 0 := by
  simpa only [LinearMap.dualProd_apply_apply, add_comm] using annihilator_pairing_zero s hs.1
    (graphDirection_mem_annihilator s hs h0 f)
    (graphDirection_mem_annihilator s hs h0 g)

/-- Every direction is fixed by the original degree-zero and degree-two
contraction data, before any coordinate or normal-form replacement. -/
theorem graphDirection_two_contractions (s : Space K E) (hs : IsPure s)
    (h0 : vacuumCoefficient s ≠ 0) (f g : Module.Dual K E) :
    g (graphDirection s hs h0 f) =
      -vacuumCoefficient (annihilate g (annihilate f s)) / vacuumCoefficient s := by
  have h := congrArg (fun t : Space K E => vacuumCoefficient (annihilate g t))
    (graphDirection_annihilates s hs h0 f)
  simp only [map_add, map_zero, vacuumCoefficient_annihilate_create] at h
  apply (eq_div_iff h0).mpr
  exact eq_neg_of_add_eq_zero_right h

end Fermionic.PureVacuumChart

#print axioms Fermionic.PureVacuumChart.annihilatorProjectionEquiv
#print axioms Fermionic.PureVacuumChart.graphDirection_two_contractions
