import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Exact double-Haar conditioning of the original group measurement

The measure below is the normalized Haar measure constructed by mathlib,
not an abstract law satisfying the desired comparison.  Right averaging by
a compact subgroup preserves the original group integral.  This is the
measure-theoretic step used before compressing a density matrix at the first
occupation mode.  No representation or Husimi comparison is assumed.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set TopologicalSpace

namespace Fermionic.HaarConditioning

section CompactGroup

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

/-- The actual Haar measure with total mass one. -/
def probabilityHaar : Measure G := haarMeasure (⊤ : PositiveCompacts G)

instance probabilityHaar_isHaar : IsHaarMeasure (probabilityHaar G) := by
  unfold probabilityHaar
  infer_instance

instance probabilityHaar_isProbability : IsProbabilityMeasure (probabilityHaar G) :=
  ⟨by simpa only [probabilityHaar, PositiveCompacts.coe_top] using
    (haarMeasure_self (K₀ := (⊤ : PositiveCompacts G)))⟩

/-- On a compact group, the normalized left Haar measure is also right invariant.
The proof uses uniqueness of normalized Haar, not commutativity of the group. -/
instance probabilityHaar_isRightInvariant : IsMulRightInvariant (probabilityHaar G) := by
  constructor
  intro g
  haveI : IsProbabilityMeasure (Measure.map (fun x : G => x * g) (probabilityHaar G)) :=
    Measure.isProbabilityMeasure_map (continuous_mul_const g).measurable.aemeasurable
  exact isHaarMeasure_eq_of_isProbabilityMeasure _ _

variable {G}

/-- A fixed left translation preserves the complete scalar readout law. -/
theorem map_readout_mul_left {q : G → ℝ} (hq : Measurable q) (g : G) :
    Measure.map (fun x => q (g * x)) (probabilityHaar G) =
      Measure.map q (probabilityHaar G) := by
  change Measure.map (q ∘ fun x => g * x) (probabilityHaar G) = _
  rw [← Measure.map_map hq (measurable_const_mul g), map_mul_left_eq_self]

/-- A fixed right translation preserves the complete scalar readout law. -/
theorem map_readout_mul_right {q : G → ℝ} (hq : Measurable q) (g : G) :
    Measure.map (fun x => q (x * g)) (probabilityHaar G) =
      Measure.map q (probabilityHaar G) := by
  change Measure.map (q ∘ fun x => x * g) (probabilityHaar G) = _
  rw [← Measure.map_map hq (measurable_mul_const g), map_mul_right_eq_self]

/-- A continuous readout positive at even one group element has positive mass
on positive values under the original Haar pushforward.  Thus the strict
scale-mixture step does not need a separate Schur-averaging computation. -/
theorem map_readout_positive_mass {q : G → ℝ} (hq : Continuous q) {g : G}
    (hg : 0 < q g) :
    Measure.map q (probabilityHaar G) (Ioi (0 : ℝ)) ≠ 0 := by
  rw [Measure.map_apply hq.measurable measurableSet_Ioi]
  exact (isOpen_lt continuous_const hq).measure_ne_zero (probabilityHaar G) ⟨g, hg⟩

/-- Haar almost-everywhere equality of continuous readouts is equality
everywhere, so a single actual group-element witness detects a strict gap. -/
theorem readout_eq_of_ae_eq {q r : G → ℝ} (hq : Continuous q) (hr : Continuous r)
    (h : q =ᵐ[probabilityHaar G] r) : q = r :=
  (hq.ae_eq_iff_eq (probabilityHaar G) hr).mp h

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- Exact double-Haar identity on compact groups.  The outer Haar variable is
unchanged; no success-probability factor is introduced.  The compact-support
version of Fubini avoids any countability requirement on the compact groups. -/
theorem integral_double_haar (j : K →* G) (hj : Continuous j)
    {f : G → ℝ} (hf : Continuous f) :
    (∫ g, ∫ k, f (g * j k) ∂probabilityHaar K ∂probabilityHaar G) =
      ∫ g, f g ∂probabilityHaar G := by
  have hc : Continuous (fun p : G × K => f (p.1 * j p.2)) :=
    hf.comp (continuous_fst.mul (hj.comp continuous_snd))
  rw [integral_integral_swap_of_hasCompactSupport hc
    (HasCompactSupport.of_compactSpace _)]
  simp only [integral_mul_right_eq_self, integral_const, probReal_univ, one_smul]

/-- The preceding identity in the orientation used by conditioning proofs. -/
theorem integral_eq_double_haar (j : K →* G) (hj : Continuous j)
    {f : G → ℝ} (hf : Continuous f) :
    (∫ g, f g ∂probabilityHaar G) =
      ∫ g, ∫ k, f (g * j k) ∂probabilityHaar K ∂probabilityHaar G :=
  (integral_double_haar j hj hf).symm

end CompactGroup

section UnitaryGroup

open scoped Matrix.Norms.Elementwise

variable (n : Type*) [Fintype n] [DecidableEq n]

/-- The actual finite-dimensional complex unitary matrix group is compact.
Its entries are bounded by one and the unitary equations define a closed set. -/
theorem isCompact_unitaryGroup :
    IsCompact (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  letI : ProperSpace (Matrix n n ℂ) := FiniteDimensional.proper ℂ (Matrix n n ℂ)
  apply (isCompact_closedBall (0 : Matrix n n ℂ) 1).of_isClosed_subset isClosed_unitary
  intro U hU
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    entrywise_sup_norm_bound_of_unitary hU

instance unitaryGroup_compactSpace : CompactSpace (Matrix.unitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n)

instance unitaryGroup_measurableSpace : MeasurableSpace (Matrix.unitaryGroup n ℂ) :=
  borel (Matrix.unitaryGroup n ℂ)

instance unitaryGroup_borelSpace : BorelSpace (Matrix.unitaryGroup n ℂ) := ⟨rfl⟩

/-- Normalized Haar on the original unitary matrix group. -/
def unitaryHaar : Measure (Matrix.unitaryGroup n ℂ) :=
  probabilityHaar (Matrix.unitaryGroup n ℂ)

instance unitaryHaar_isProbability : IsProbabilityMeasure (unitaryHaar n) := by
  unfold unitaryHaar
  infer_instance

instance unitaryHaar_isHaar : IsHaarMeasure (unitaryHaar n) := by
  unfold unitaryHaar
  infer_instance

instance unitaryHaar_isRightInvariant : IsMulRightInvariant (unitaryHaar n) := by
  unfold unitaryHaar
  infer_instance

/-- The actual block-diagonal homomorphism fixing one distinguished mode and
acting by the entire lower-dimensional unitary group on its complement. -/
def fixFirstHom : Matrix.unitaryGroup n ℂ →* Matrix.unitaryGroup (Fin 1 ⊕ n) ℂ where
  toFun U := ⟨Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 U.val, by
    have hU : U.val * U.val.conjTranspose = 1 := U.property.2
    apply Matrix.mem_unitaryGroup_iff.mpr
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      hU, Matrix.fromBlocks_one]⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.fromBlocks_one
  map_mul' U V := by
    apply Subtype.ext
    simp only [Matrix.UnitaryGroup.mul_val, Matrix.fromBlocks_multiply,
      Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem fixFirstHom_continuous : Continuous (fixFirstHom n) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : Matrix.unitaryGroup n ℂ =>
    Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 U.val)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  rcases i with i | i <;> rcases j with j | j
  · exact continuous_const
  · exact continuous_const
  · exact continuous_const
  · exact continuous_subtype_val.matrix_elem i j

@[simp] theorem fixFirstHom_lower_apply (U : Matrix.unitaryGroup n ℂ) (i j : n) :
    fixFirstHom n U (Sum.inr i) (Sum.inr j) = U i j := rfl

@[simp] theorem fixFirstHom_first_apply (U : Matrix.unitaryGroup n ℂ) :
    fixFirstHom n U (Sum.inl 0) (Sum.inl 0) = 1 := by
  simp [fixFirstHom]

@[simp] theorem fixFirstHom_first_row (U : Matrix.unitaryGroup n ℂ) (j : n) :
    fixFirstHom n U (Sum.inl 0) (Sum.inr j) = 0 := rfl

@[simp] theorem fixFirstHom_first_column (U : Matrix.unitaryGroup n ℂ) (i : n) :
    fixFirstHom n U (Sum.inr i) (Sum.inl 0) = 0 := rfl

theorem fixFirstHom_injective : Function.Injective (fixFirstHom n) := by
  intro U V h
  apply Matrix.UnitaryGroup.ext
  intro i j
  exact congrArg (fun W : Matrix.unitaryGroup (Fin 1 ⊕ n) ℂ =>
    W (Sum.inr i) (Sum.inr j)) h

/-- The first-mode double integral for the original finite-dimensional unitary
group and the complete lower-dimensional unitary group. -/
theorem unitary_integral_eq_double (f : Matrix.unitaryGroup (Fin 1 ⊕ n) ℂ → ℝ)
    (hf : Continuous f) :
    (∫ U, f U ∂unitaryHaar (Fin 1 ⊕ n)) =
      ∫ U, ∫ V, f (U * fixFirstHom n V) ∂unitaryHaar n ∂unitaryHaar (Fin 1 ⊕ n) :=
  integral_eq_double_haar (fixFirstHom n) (fixFirstHom_continuous n) hf

variable {n} {m : Type*} [Fintype m] [DecidableEq m]

/-- Relabelling a finite orthonormal coordinate set is an actual unitary-group
isomorphism, obtained from the matrix star-algebra isomorphism. -/
def unitaryReindex (e : n ≃ m) : Matrix.unitaryGroup n ℂ ≃* Matrix.unitaryGroup m ℂ :=
  (Unitary.mapEquiv
    { (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv with map_star' := fun _ => rfl }).toMulEquiv

@[simp] theorem unitaryReindex_apply (e : n ≃ m) (U : Matrix.unitaryGroup n ℂ)
    (i j : m) : unitaryReindex e U i j = U (e.symm i) (e.symm j) := rfl

theorem unitaryReindex_continuous (e : n ≃ m) : Continuous (unitaryReindex e) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun U : Matrix.unitaryGroup n ℂ => Matrix.reindex e e U.val)
  apply continuous_matrix
  intro i j
  exact continuous_subtype_val.matrix_elem (e.symm i) (e.symm j)

/-- Coordinate relabelling transports normalized Haar exactly. -/
theorem unitaryReindex_measurePreserving (e : n ≃ m) :
    MeasurePreserving (unitaryReindex e) (unitaryHaar n) (unitaryHaar m) :=
  (unitaryReindex e).toMonoidHom.measurePreserving (unitaryReindex_continuous e)
    (unitaryReindex e).surjective (by simp only [measure_univ])

def firstFinEquiv (M : ℕ) : Fin 1 ⊕ Fin M ≃ Fin (M + 1) :=
  (finSumFinEquiv : Fin 1 ⊕ Fin M ≃ Fin (1 + M)).trans (finCongr (Nat.add_comm 1 M))

@[simp] theorem firstFinEquiv_zero (M : ℕ) : firstFinEquiv M (Sum.inl 0) = 0 := rfl

@[simp] theorem firstFinEquiv_succ (M : ℕ) (i : Fin M) :
    firstFinEquiv M (Sum.inr i) = i.succ := by
  apply Fin.ext
  exact Nat.add_comm 1 i.val

@[simp] theorem firstFinEquiv_symm_zero (M : ℕ) :
    (firstFinEquiv M).symm 0 = Sum.inl 0 := by
  have h := (firstFinEquiv M).symm_apply_apply (Sum.inl 0)
  rwa [firstFinEquiv_zero] at h

@[simp] theorem firstFinEquiv_symm_succ (M : ℕ) (i : Fin M) :
    (firstFinEquiv M).symm i.succ = Sum.inr i := by
  have h := (firstFinEquiv M).symm_apply_apply (Sum.inr i)
  rwa [firstFinEquiv_succ] at h

/-- The finite-index version of the fixed-first-mode embedding. -/
def fixFirstFinHom (M : ℕ) :
    Matrix.unitaryGroup (Fin M) ℂ →* Matrix.unitaryGroup (Fin (M + 1)) ℂ :=
  (unitaryReindex (firstFinEquiv M)).toMonoidHom.comp (fixFirstHom (Fin M))

@[simp] theorem fixFirstFinHom_zero_zero (M : ℕ) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    fixFirstFinHom M U 0 0 = 1 := by
  change unitaryReindex (firstFinEquiv M) (fixFirstHom (Fin M) U) 0 0 = 1
  simp

@[simp] theorem fixFirstFinHom_zero_succ (M : ℕ) (U : Matrix.unitaryGroup (Fin M) ℂ)
    (j : Fin M) : fixFirstFinHom M U 0 j.succ = 0 := by
  change unitaryReindex (firstFinEquiv M) (fixFirstHom (Fin M) U) 0 j.succ = 0
  simp

@[simp] theorem fixFirstFinHom_succ_zero (M : ℕ) (U : Matrix.unitaryGroup (Fin M) ℂ)
    (i : Fin M) : fixFirstFinHom M U i.succ 0 = 0 := by
  change unitaryReindex (firstFinEquiv M) (fixFirstHom (Fin M) U) i.succ 0 = 0
  simp

@[simp] theorem fixFirstFinHom_succ_succ (M : ℕ) (U : Matrix.unitaryGroup (Fin M) ℂ)
    (i j : Fin M) : fixFirstFinHom M U i.succ j.succ = U i j := by
  change unitaryReindex (firstFinEquiv M) (fixFirstHom (Fin M) U) i.succ j.succ = U i j
  simp

theorem fixFirstFinHom_continuous (M : ℕ) : Continuous (fixFirstFinHom M) :=
  (unitaryReindex_continuous _).comp (fixFirstHom_continuous (Fin M))

/-- Direct `Fin M`/`Fin (M+1)` form of the original unitary double-Haar identity. -/
theorem unitary_fin_integral_eq_double (M : ℕ)
    (f : Matrix.unitaryGroup (Fin (M + 1)) ℂ → ℝ) (hf : Continuous f) :
    (∫ U, f U ∂unitaryHaar (Fin (M + 1))) =
      ∫ U, ∫ V, f (U * fixFirstFinHom M V)
        ∂unitaryHaar (Fin M) ∂unitaryHaar (Fin (M + 1)) :=
  integral_eq_double_haar (fixFirstFinHom M) (fixFirstFinHom_continuous M) hf

end UnitaryGroup

end Fermionic.HaarConditioning
