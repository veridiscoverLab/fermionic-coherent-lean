import Fermionic.Spinor
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.CliffordAlgebra.SpinGroup
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
Transport in the original full exterior-algebra Fock representation.
The annihilator is transported by a proved reflection, never by an assumed
covariance field. The final section constructs the positive Euclidean real
form through the original conjugate-paired Majorana generators, and proves
purity of its whole vacuum-orbit cone. It does not assert the converse orbit
classification, Hilbert unitarity, a Haar law, or the eight-mode rank theorem.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Fermionic.SpinorTransport

open Module Fermionic.Fock Fermionic.Spinor

variable {K : Type*} [Field K]
variable {E : Type*} [AddCommGroup E] [Module K E]

theorem reflection_pairing (z : Split K E) (hz : z.1 z.2 ≠ 0) :
    ((z.1 z.2)⁻¹ • LinearMap.dualProd K E z) z = 2 := by
  simp only [LinearMap.smul_apply, LinearMap.dualProd_apply_apply, smul_eq_mul]
  rw [← two_mul, mul_comm (z.1 z.2)⁻¹, mul_assoc, mul_inv_cancel₀ hz, mul_one]

/-- The actual orthogonal reflection in the nonisotropic split vector. -/
def reflection (z : Split K E) (hz : z.1 z.2 ≠ 0) : Split K E ≃ₗ[K] Split K E :=
  Module.reflection (reflection_pairing z hz)

theorem reflection_apply (z : Split K E) (hz : z.1 z.2 ≠ 0) (w : Split K E) :
    reflection z hz w = w - ((z.1 z.2)⁻¹ * LinearMap.dualProd K E z w) • z := by
  rfl

theorem reflection_involutive (z : Split K E) (hz : z.1 z.2 ≠ 0) :
    Function.Involutive (reflection z hz) :=
  Module.involutive_reflection (reflection_pairing z hz)

theorem action_injective (z : Split K E) (hz : z.1 z.2 ≠ 0) :
    Function.Injective (action z : Space K E → Space K E) := by
  intro s t h
  have hh := congrArg (action z) h
  rw [action_square, action_square] at hh
  exact (smul_right_injective _ hz) hh

/-- The sign is the one for the ordinary reflection, rather than its negative.
This identity holds on every full Fock vector. -/
theorem action_reflection (z : Split K E) (hz : z.1 z.2 ≠ 0)
    (w : Split K E) (s : Space K E) :
    action (reflection z hz w) (action z s) = -action z (action w s) := by
  have hc := action_car z w s
  have hcoeff : ((z.1 z.2)⁻¹ * LinearMap.dualProd K E z w) * z.1 z.2 =
      LinearMap.dualProd K E z w := by
    rw [mul_right_comm, inv_mul_cancel₀ hz, one_mul]
  rw [reflection_apply, map_sub, map_smul]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, action_square, smul_smul,
    hcoeff]
  rw [← hc]
  abel

theorem reflection_mem_annihilator_iff (z : Split K E) (hz : z.1 z.2 ≠ 0)
    (w : Split K E) (s : Space K E) :
    reflection z hz w ∈ annihilator (action z s) ↔ w ∈ annihilator s := by
  rw [Spinor.mem_annihilator, action_reflection, neg_eq_zero, Spinor.mem_annihilator]
  exact (action_injective z hz).eq_iff' (map_zero (action z))

/-- Exact transport of the entire annihilator, including every cross direction. -/
def annihilatorEquiv (z : Split K E) (hz : z.1 z.2 ≠ 0) (s : Space K E) :
    annihilator s ≃ₗ[K] annihilator (action z s) where
  toFun w := ⟨reflection z hz w, (reflection_mem_annihilator_iff z hz w s).mpr w.2⟩
  invFun w := ⟨reflection z hz w, by
    apply (reflection_mem_annihilator_iff z hz (reflection z hz w) s).mp
    simpa only [reflection_involutive z hz w] using w.2⟩
  left_inv w := Subtype.ext (reflection_involutive z hz w)
  right_inv w := Subtype.ext (reflection_involutive z hz w)
  map_add' w v := Subtype.ext (map_add (reflection z hz) (w : Split K E) (v : Split K E))
  map_smul' a w := Subtype.ext (map_smul (reflection z hz) a (w : Split K E))

theorem nonnull_action_preserves_pure [FiniteDimensional K E]
    (s : Space K E) (hs : IsPure s) (z : Split K E) (hz : z.1 z.2 ≠ 0) :
    IsPure (action z s) := by
  refine ⟨fun h => hs.1 ((action_injective z hz) (h.trans (map_zero (action z)).symm)), ?_⟩
  rw [← (annihilatorEquiv z hz s).finrank_eq, hs.2]

theorem nonnull_action_isPure_iff [FiniteDimensional K E]
    (z : Split K E) (hz : z.1 z.2 ≠ 0) (s : Space K E) :
    IsPure (action z s) ↔ IsPure s := by
  refine ⟨fun hs => ⟨?_, ?_⟩, fun hs => nonnull_action_preserves_pure s hs z hz⟩
  · intro h
    exact hs.1 (by rw [h, map_zero])
  · rw [(annihilatorEquiv z hz s).finrank_eq, hs.2]

/-- An arbitrary Clifford vector, isotropic or not, preserves purity when the
actual result is nonzero. No normalization or resampling is involved. -/
theorem action_preserves_pure [FiniteDimensional K E]
    (s : Space K E) (hs : IsPure s) (z : Split K E) (hnew : action z s ≠ 0) :
    IsPure (action z s) := by
  by_cases hz : z.1 z.2 = 0
  · exact null_action_preserves_pure s hs z hz hnew
  · exact nonnull_action_preserves_pure s hs z hz

theorem history_preserves_pure [FiniteDimensional K E]
    (zs : List (Split K E)) (s : Space K E) (hs : IsPure s)
    (hfinal : historyOperator zs s ≠ 0) : IsPure (historyOperator zs s) := by
  induction zs generalizing s with
  | nil => simpa [historyOperator] using hs
  | cons z zs ih =>
    have hfirst : action z s ≠ 0 := by
      intro hz
      apply hfinal
      change historyOperator zs (action z s) = 0
      rw [hz, map_zero]
    exact ih (action z s) (action_preserves_pure s hs z hfirst) hfinal

theorem invertible_history_preserves_pure [FiniteDimensional K E]
    (zs : List (Split K E)) (hzs : ∀ z ∈ zs, z.1 z.2 ≠ 0)
    (s : Space K E) (hs : IsPure s) : IsPure (historyOperator zs s) := by
  induction zs generalizing s with
  | nil => simpa [historyOperator] using hs
  | cons z zs ih =>
    exact ih (fun w hw => hzs w (List.mem_cons_of_mem z hw)) (action z s)
      (nonnull_action_preserves_pure s hs z (hzs z List.mem_cons_self))

theorem invertible_history_vacuum_isPure [FiniteDimensional K E]
    (zs : List (Split K E)) (hzs : ∀ z ∈ zs, z.1 z.2 ≠ 0) :
    IsPure (historyOperator zs (1 : Space K E)) :=
  invertible_history_preserves_pure zs hzs 1 vacuum_isPure

/-- The genuine algebra representation evaluated on a Clifford unit. -/
def unitAction (x : (CliffordAlgebra (QuadraticForm.dualProd K E))ˣ) :
    Module.End K (Space K E) := representation (x : CliffordAlgebra _)

@[simp] theorem unitAction_one :
    unitAction (1 : (CliffordAlgebra (QuadraticForm.dualProd K E))ˣ) = 1 := by
  simp [unitAction]

@[simp] theorem unitAction_mul (x y : (CliffordAlgebra (QuadraticForm.dualProd K E))ˣ) :
    unitAction (x * y) = unitAction x * unitAction y := by
  simp [unitAction]

theorem unitAction_inv_apply (x : (CliffordAlgebra (QuadraticForm.dualProd K E))ˣ)
    (s : Space K E) : unitAction x (unitAction x⁻¹ s) = s := by
  change (unitAction x * unitAction x⁻¹) s = s
  rw [← unitAction_mul, mul_inv_cancel, unitAction_one]
  rfl

/-- All elements of mathlib's actual Lipschitz group preserve purity in the
original Fock representation. The group is not postulated to preserve purity. -/
theorem lipschitz_action_isPure_iff [FiniteDimensional K E] [Invertible (2 : K)]
    (x : (CliffordAlgebra (QuadraticForm.dualProd K E))ˣ)
    (hx : x ∈ lipschitzGroup (QuadraticForm.dualProd K E)) (s : Space K E) :
    IsPure (unitAction x s) ↔ IsPure s := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction generalizing s with
  | mem x hx =>
    obtain ⟨z, hz⟩ := hx
    have hq : z.1 z.2 ≠ 0 := by
      apply IsUnit.ne_zero
      change IsUnit (QuadraticForm.dualProd K E z)
      apply CliffordAlgebra.isUnit_of_isUnit_ι
      rw [hz]
      exact x.isUnit
    simpa only [unitAction, ← hz, representation_generator] using
      nonnull_action_isPure_iff z hq s
  | one => simp
  | mul x y _ _ ihx ihy =>
    rw [unitAction_mul]
    change IsPure (unitAction x (unitAction y s)) ↔ IsPure s
    exact (ihx _).trans (ihy s)
  | inv x _ ih =>
    have hh := ih (unitAction x⁻¹ s)
    rw [unitAction_inv_apply] at hh
    exact hh.symm

/-- In particular, the actual algebraic Spin group acts by purity-preserving
operators; no compact-real-form or Hilbert-unitarity identification is used. -/
theorem spin_action_preserves_pure [FiniteDimensional K E] [Invertible (2 : K)]
    (x : spinGroup (QuadraticForm.dualProd K E)) (s : Space K E) (hs : IsPure s) :
    IsPure (representation (x : CliffordAlgebra _) s) := by
  have hx : spinGroup.toUnits x ∈ lipschitzGroup (QuadraticForm.dualProd K E) :=
    spinGroup.units_mem_lipschitzGroup x.property
  exact (lipschitz_action_isPure_iff (spinGroup.toUnits x) hx s).mpr hs

theorem spin_vacuum_isPure [FiniteDimensional K E] [Invertible (2 : K)]
    (x : spinGroup (QuadraticForm.dualProd K E)) :
    IsPure (representation (x : CliffordAlgebra _) (1 : Space K E)) :=
  spin_action_preserves_pure x 1 vacuum_isPure

theorem annihilator_smul (c : K) (hc : c ≠ 0) (s : Space K E) :
    annihilator (c • s) = annihilator s := by
  ext w
  simp only [Spinor.mem_annihilator, map_smul, smul_eq_zero, hc, false_or]

theorem smul_isPure_iff [FiniteDimensional K E] (c : K) (hc : c ≠ 0)
    (s : Space K E) : IsPure (c • s) ↔ IsPure s := by
  unfold IsPure
  rw [annihilator_smul c hc s]
  simp only [ne_eq, smul_eq_zero, hc, false_or]

section RealMajorana

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

local instance realInnerProduct : InnerProductSpace ℝ H :=
  InnerProductSpace.rclikeToReal ℂ H

/-- The positive Euclidean form on the underlying real one-particle space. -/
def majoranaQuadratic : QuadraticForm ℝ H :=
  LinearMap.BilinMap.toQuadraticMap (innerₗ H)

@[simp] theorem majoranaQuadratic_apply (v : H) : majoranaQuadratic v = ‖v‖ ^ 2 :=
  real_inner_self_eq_norm_sq v

theorem majoranaQuadratic_pos {v : H} (hv : v ≠ 0) : 0 < majoranaQuadratic v := by
  rw [majoranaQuadratic_apply]
  exact sq_pos_of_pos (norm_pos_iff.mpr hv)

/-- The actual real Majorana vector has conjugate annihilation and creation
coefficients in the original complex split space. -/
def majoranaEmbedding : H →ₗ[ℝ] Split ℂ H where
  toFun v := (innerₛₗ ℂ v, v)
  map_add' v w := by
    apply Prod.ext
    · ext x
      change inner ℂ (v + w) x = inner ℂ v x + inner ℂ w x
      exact inner_add_left v w x
    · rfl
  map_smul' r v := by
    apply Prod.ext
    · ext x
      change inner ℂ (r • v) x = r • inner ℂ v x
      exact inner_smul_left_eq_smul v x r
    · rfl

theorem majoranaEmbedding_quadratic (v : H) :
    QuadraticForm.dualProd ℂ H (majoranaEmbedding v) = (majoranaQuadratic v : ℂ) := by
  change inner ℂ v v = (majoranaQuadratic v : ℂ)
  rw [majoranaQuadratic_apply, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

/-- Scalar extension of the real Euclidean Clifford algebra into the actual
complex split Clifford algebra, on its original generators. -/
def majoranaCliffordMap :
    CliffordAlgebra (majoranaQuadratic (H := H)) →ₐ[ℝ]
      CliffordAlgebra (QuadraticForm.dualProd ℂ H) :=
  CliffordAlgebra.lift _ ⟨
    ((CliffordAlgebra.ι (QuadraticForm.dualProd ℂ H)).restrictScalars ℝ).comp
      majoranaEmbedding, by
      intro v
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      rw [CliffordAlgebra.ι_sq_scalar, majoranaEmbedding_quadratic]
      exact (IsScalarTower.algebraMap_apply ℝ ℂ _ (majoranaQuadratic v)).symm⟩

@[simp] theorem majoranaCliffordMap_generator (v : H) :
    majoranaCliffordMap (CliffordAlgebra.ι majoranaQuadratic v) =
      CliffordAlgebra.ι (QuadraticForm.dualProd ℂ H) (majoranaEmbedding v) :=
  CliffordAlgebra.lift_ι_apply _ _ _

/-- Scalar extension maps the actual real Lipschitz group into the complex
split Lipschitz group, by transporting its original generating vectors. -/
theorem majorana_units_mem_lipschitz
    (x : (CliffordAlgebra (majoranaQuadratic (H := H)))ˣ)
    (hx : x ∈ lipschitzGroup majoranaQuadratic) :
    Units.map majoranaCliffordMap.toMonoidHom x ∈
      lipschitzGroup (QuadraticForm.dualProd ℂ H) := by
  unfold lipschitzGroup at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨majoranaEmbedding v, ?_⟩
    change CliffordAlgebra.ι (QuadraticForm.dualProd ℂ H) (majoranaEmbedding v) =
      majoranaCliffordMap (H := H) (↑x : CliffordAlgebra (majoranaQuadratic (H := H)))
    rw [← hv, majoranaCliffordMap_generator]
  | one => simp
  | mul x y _ _ ihx ihy =>
    simpa only [map_mul] using (lipschitzGroup (QuadraticForm.dualProd ℂ H)).mul_mem ihx ihy
  | inv x _ ih =>
    simpa only [map_inv] using (lipschitzGroup (QuadraticForm.dualProd ℂ H)).inv_mem ih

/-- The real Euclidean Spin action on the full complex exterior Fock space. -/
def euclideanSpinAction (x : spinGroup (majoranaQuadratic (H := H))) :
    Module.End ℂ (Space ℂ H) := representation (majoranaCliffordMap (x : CliffordAlgebra _))

/-- The Euclidean Spin operators form a genuine representation on full Fock
space, not a collection of independently chosen purity-preserving maps. -/
def euclideanSpinRepresentation :
    spinGroup (majoranaQuadratic (H := H)) →* Module.End ℂ (Space ℂ H) where
  toFun := euclideanSpinAction
  map_one' := by simp [euclideanSpinAction]
  map_mul' x y := by simp [euclideanSpinAction]

theorem majorana_fock_generator (v : H) (s : Space ℂ H) :
    representation (majoranaCliffordMap (CliffordAlgebra.ι majoranaQuadratic v)) s =
      annihilate (innerₛₗ ℂ v) s + create v s := by
  rw [majoranaCliffordMap_generator, representation_generator]
  rfl

theorem euclideanSpinAction_preserves_pure [FiniteDimensional ℂ H]
    (x : spinGroup (majoranaQuadratic (H := H))) (s : Space ℂ H) (hs : IsPure s) :
    IsPure (euclideanSpinAction x s) := by
  letI : Invertible (2 : ℂ) := invertibleOfNonzero (by norm_num)
  have hx : spinGroup.toUnits x ∈ lipschitzGroup (majoranaQuadratic (H := H)) :=
    spinGroup.units_mem_lipschitzGroup x.property
  exact (lipschitz_action_isPure_iff
    (Units.map majoranaCliffordMap.toMonoidHom (spinGroup.toUnits x))
    (majorana_units_mem_lipschitz _ hx) s).mpr hs

/-- A vector on the actual Euclidean Spin orbit of the vacuum is pure in the
original complex annihilator definition. This is the physical-to-algebraic
direction; the converse orbit classification is not assumed or proved here. -/
theorem euclideanSpin_vacuum_isPure [FiniteDimensional ℂ H]
    (x : spinGroup (majoranaQuadratic (H := H))) :
    IsPure (euclideanSpinAction x (1 : Space ℂ H)) :=
  euclideanSpinAction_preserves_pure x 1 vacuum_isPure

/-- The entire nonzero complex cone over the real Euclidean Spin vacuum orbit
is contained in the original complex pure-spinor cone. -/
theorem euclideanSpin_vacuum_ray_isPure [FiniteDimensional ℂ H]
    (x : spinGroup (majoranaQuadratic (H := H))) (c : ℂ) (hc : c ≠ 0) :
    IsPure (c • euclideanSpinAction x (1 : Space ℂ H)) :=
  (smul_isPure_iff c hc _).mpr (euclideanSpin_vacuum_isPure x)

end RealMajorana

end Fermionic.SpinorTransport
