import Fermionic.ExteriorUnitary
import Fermionic.ConditionalSector
import Fermionic.OccupationConvexOrder
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
Actual orthonormal frame completion used in first-mode Slater conditioning.
No Gaussian or conditional-closure axiom is introduced.
-/

noncomputable section

namespace Fermionic.SlaterClosure

open Matrix Fermionic.ExteriorUnitary Fermionic.ConditionalSector
open Fermionic.OccupationConvexOrder

/-- The matrix whose columns are the given actual orthonormal basis. -/
def basisUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) : Matrix.unitaryGroup ι ℂ :=
  ⟨(EuclideanSpace.basisFun ι ℂ).toBasis.toMatrix b,
    (EuclideanSpace.basisFun ι ℂ).toMatrix_orthonormalBasis_mem_unitary b⟩

@[simp] theorem basisUnitary_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι)) (i j : ι) :
    basisUnitary b i j = b j i := by
  simp [basisUnitary, Module.Basis.toMatrix_apply]

/-- Every actual partial orthonormal coordinate frame can be completed by a
unitary matrix while retaining each specified column. -/
theorem exists_unitary_extension (n : ℕ) (v : Fin n → EuclideanSpace ℂ (Fin n))
    (s : Set (Fin n)) (hv : Orthonormal ℂ (s.restrict v)) :
    ∃ U : Matrix.unitaryGroup (Fin n) ℂ, ∀ i ∈ s, ∀ j, U j i = v i j := by
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank ℂ (EuclideanSpace ℂ (Fin n)) = Fintype.card (Fin n)) hv
  refine ⟨basisUnitary b, ?_⟩
  intro i hi j
  rw [basisUnitary_apply, hb i hi]

/-- A prescribed unit vector can be the actual first column of a unitary. -/
theorem exists_unitary_first_column (n : ℕ) (x : EuclideanSpace ℂ (Fin (n + 1)))
    (hx : ‖x‖ = 1) :
    ∃ U : Matrix.unitaryGroup (Fin (n + 1)) ℂ, ∀ j, U j 0 = x j := by
  have hv : Orthonormal ℂ (({0} : Set (Fin (n + 1))).restrict (fun _ => x)) := by
    constructor
    · intro i
      exact hx
    · intro i j hij
      exact (hij (Subsingleton.elim i j)).elim
  obtain ⟨U, hU⟩ := exists_unitary_extension (n + 1) (fun _ => x) {0} hv
  exact ⟨U, hU 0 (Set.mem_singleton 0)⟩

/-- Every nonzero actual row can be aligned in its own complete column space.
The entire row is retained, and the scalar is its original Euclidean norm. -/
theorem exists_unitary_row_alignment (n : ℕ) (r : Fin (n + 1) → ℂ) (hr : r ≠ 0) :
    ∃ U : Matrix.unitaryGroup (Fin (n + 1)) ℂ, ∃ a : ℂ, a ≠ 0 ∧
      ∀ j, (∑ i, r i * U i j) = if j = 0 then a else 0 := by
  let z : EuclideanSpace ℂ (Fin (n + 1)) := WithLp.toLp 2 (star r)
  have hz : z ≠ 0 := by
    intro h
    apply hr
    have hh := congrArg (fun y : EuclideanSpace ℂ (Fin (n + 1)) => WithLp.ofLp y) h
    simpa only [z, WithLp.ofLp_toLp, WithLp.ofLp_zero, star_eq_zero] using hh
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let x : EuclideanSpace ℂ (Fin (n + 1)) := (↑(‖z‖⁻¹) : ℂ) • z
  have hx : ‖x‖ = 1 := by
    simp [x, norm_smul, hn]
  obtain ⟨U, hU⟩ := exists_unitary_first_column n x hx
  have ha : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  refine ⟨U, (‖z‖ : ℂ), ha, ?_⟩
  have hrow (i : Fin (n + 1)) : r i = (‖z‖ : ℂ) * star (U i 0) := by
    rw [hU]
    change r i = (‖z‖ : ℂ) * star ((↑(‖z‖⁻¹) : ℂ) * star (r i))
    have hc : star (↑(‖z‖⁻¹) : ℂ) = (‖z‖ : ℂ)⁻¹ := by simp
    rw [StarMul.star_mul, star_star, hc]
    simp only [mul_comm (r i), ← mul_assoc, mul_inv_cancel₀ ha, one_mul]
  intro j
  have hc := congrArg (fun A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ => A 0 j) U.property.1
  change (U.val.conjTranspose * U.val) 0 j = (1 : Matrix _ _ ℂ) 0 j at hc
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at hc
  simp_rw [hrow, mul_assoc]
  rw [← Finset.mul_sum, hc]
  by_cases h : j = 0
  · simp [h]
  · simp [h, Ne.symm h]

/-- Completion of the entire original rectangular isometry, with every
specified column retained at a fixed coordinate. -/
theorem exists_unitary_frame_extension {M p : ℕ} (hp : p ≤ M)
    (A : Matrix (Fin M) (Fin p) ℂ) (hA : A.conjTranspose * A = 1) :
    ∃ U : Matrix.unitaryGroup (Fin M) ℂ,
      ∀ i j, U i (Fin.castLE hp j) = A i j := by
  classical
  let e : Fin p ↪ Fin M := Fin.castLEEmb hp
  let f : Fin p → EuclideanSpace ℂ (Fin M) := fun j => WithLp.toLp 2 (fun i => A i j)
  have hf : Orthonormal ℂ f := by
    rw [orthonormal_iff_ite]
    intro i j
    have h := congrArg (fun B : Matrix (Fin p) (Fin p) ℂ => B i j) hA
    simpa only [f, EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp,
      dotProduct, Pi.star_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.one_apply, mul_comm] using h
  let v : Fin M → EuclideanSpace ℂ (Fin M) := Function.extend e f (fun _ => 0)
  have he (j : Fin p) : v (e j) = f j := e.injective.extend_apply _ _ j
  have hv : Orthonormal ℂ ((Set.range e).restrict v) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    obtain ⟨a, rfl⟩ := hi
    obtain ⟨b, rfl⟩ := hj
    simp only [Set.restrict_apply, he]
    have hij : (⟨e a, ⟨a, rfl⟩⟩ : Set.range e) = ⟨e b, ⟨b, rfl⟩⟩ ↔ a = b := by
      rw [Subtype.ext_iff]
      exact e.injective.eq_iff
    simpa only [hij] using (orthonormal_iff_ite.mp hf a b)
  obtain ⟨U, hU⟩ := exists_unitary_extension M v (Set.range e) hv
  refine ⟨U, ?_⟩
  intro i j
  have h := hU (e j) ⟨j, rfl⟩ i
  rw [he] at h
  exact h

/-- The entire exterior vector of a rectangular frame, in actual occupancy coordinates. -/
def frameVector {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) : Index n p → ℂ :=
  fun S => Matrix.det (fun i j : Fin p => A (enumerate S i) j)

theorem frameVector_unitary_columns {n p : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (T : Index n p) :
    frameVector (fun i j => U i (enumerate T j)) =
      fun S => exteriorMatrix p U.val S T := by
  funext S
  rw [exteriorMatrix_entry]
  change Matrix.det (fun i j : Fin p => U (enumerate S i) (enumerate T j)) =
    Matrix.det (fun i j : Fin p => U (enumerate S j) (enumerate T i))
  exact (Matrix.det_transpose (fun i j : Fin p => U (enumerate S i) (enumerate T j))).symm

theorem unitary_columns_isometry {n p : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (T : Index n p) :
    let A : Matrix (Fin n) (Fin p) ℂ := fun i j => U i (enumerate T j)
    A.conjTranspose * A = 1 := by
  dsimp
  ext i j
  have h := congrArg (fun B : Matrix (Fin n) (Fin n) ℂ =>
    B (enumerate T i) (enumerate T j)) U.property.1
  have he : enumerate T i = enumerate T j ↔ i = j :=
    (Set.powersetCard.ofFinEmbEquiv.symm T).injective.eq_iff
  simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, he] using h

/-- A column change of basis contributes its single determinant to every
occupancy coefficient at once. -/
theorem frameVector_mul {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ)
    (V : Matrix (Fin p) (Fin p) ℂ) :
    frameVector (A * V) = V.det • frameVector A := by
  funext S
  change ((A.submatrix (enumerate S) id) * V).det = V.det * (frameVector A S)
  rw [Matrix.det_mul]
  exact mul_comm _ _

/-- A full rectangular orthonormal frame is an actual column of the original
unitary exterior representation, with no abstract Slater predicate. -/
theorem frameVector_is_unitary_column {n p : ℕ} (hp : p ≤ n)
    (A : Matrix (Fin n) (Fin p) ℂ) (hA : A.conjTranspose * A = 1) :
    ∃ (U : Matrix.unitaryGroup (Fin n) ℂ) (T : Index n p),
      frameVector A = fun S => exteriorMatrix p U.val S T := by
  obtain ⟨U, hU⟩ := exists_unitary_frame_extension hp A hA
  let T : Index n p := Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb hp)
  have he (j : Fin p) : enumerate T j = Fin.castLE hp j := by
    simp only [enumerate, T, Equiv.symm_apply_apply]
    rfl
  refine ⟨U, T, ?_⟩
  rw [← frameVector_unitary_columns]
  congr 1
  ext i j
  rw [he, hU]

/-- Exact first-row expansion in the original occupied-sector coordinates. -/
theorem creation_contract_frame {M p : ℕ}
    (A : Matrix (Fin (M + 1)) (Fin (p + 1)) ℂ) (a : ℂ)
    (hrow : ∀ j, A 0 j = if j = 0 then a else 0) :
    (creation M p).conjTranspose *ᵥ frameVector A =
      a • frameVector (fun i j => A i.succ j.succ) := by
  funext S
  rw [creation_conjTranspose_mulVec]
  unfold frameVector
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [enumerate_insertFirst_zero, hrow, Fin.succ_ne_zero, ite_false,
    mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero,
    pow_zero, one_mul, ite_true, Fin.succAbove_zero, Pi.smul_apply, smul_eq_mul]
  congr 1
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, enumerate_insertFirst_succ]

/-- A nonzero actual first-occupation contraction of a unitary exterior column
is a nonzero scalar times an actual lower-sector unitary exterior column. -/
theorem contraction_unitary_column {M p : ℕ} (hp : p ≤ M)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) (T : Index (M + 1) (p + 1))
    (hne : (creation M p).conjTranspose *ᵥ
      (fun S => exteriorMatrix (p + 1) U.val S T) ≠ 0) :
    ∃ (W : Matrix.unitaryGroup (Fin M) ℂ) (S : Index M p) (c : ℂ), c ≠ 0 ∧
      (creation M p).conjTranspose *ᵥ
        (fun S' => exteriorMatrix (p + 1) U.val S' T) =
        c • (fun S' => exteriorMatrix p W.val S' S) := by
  let A : Matrix (Fin (M + 1)) (Fin (p + 1)) ℂ := fun i j => U i (enumerate T j)
  have hA : A.conjTranspose * A = 1 := unitary_columns_isometry U T
  have hv : frameVector A = fun S => exteriorMatrix (p + 1) U.val S T :=
    frameVector_unitary_columns U T
  have hr : (fun j => A 0 j) ≠ 0 := by
    intro h
    apply hne
    rw [← hv]
    have hh : ∀ j, A 0 j = if j = 0 then (0 : ℂ) else 0 := by
      intro j
      simpa only [Pi.zero_apply, ite_self] using congrFun h j
    simpa only [zero_smul] using creation_contract_frame A 0 hh
  obtain ⟨V, a, ha, hrow⟩ := exists_unitary_row_alignment p (fun j => A 0 j) hr
  let B : Matrix (Fin (M + 1)) (Fin (p + 1)) ℂ := A * V.val
  have hbrow : ∀ j, B 0 j = if j = 0 then a else 0 := hrow
  have hB : B.conjTranspose * B = 1 := by
    calc
      _ = V.val.conjTranspose * (A.conjTranspose * A) * V.val := by
        simp only [B, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hA, Matrix.mul_one]; exact V.property.1
  let D : Matrix (Fin M) (Fin p) ℂ := fun i j => B i.succ j.succ
  have hD : D.conjTranspose * D = 1 := by
    ext i j
    have h := congrArg (fun X : Matrix (Fin (p + 1)) (Fin (p + 1)) ℂ =>
      X i.succ j.succ) hB
    simpa only [D, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      hbrow, Fin.succ_ne_zero, ite_false, star_zero, zero_mul, zero_add,
      Matrix.one_apply, Fin.succ_inj] using h
  obtain ⟨W, S, hW⟩ := frameVector_is_unitary_column hp D hD
  have hdet : V.val.det ≠ 0 := by
    intro h
    have he := congrArg Matrix.det V.property.1
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at he
    exact zero_ne_one he
  refine ⟨W, S, V.val.det⁻¹ * a, mul_ne_zero (inv_ne_zero hdet) ha, ?_⟩
  have hc := creation_contract_frame B a hbrow
  change (creation M p).conjTranspose *ᵥ frameVector (A * V.val) =
    a • frameVector D at hc
  rw [frameVector_mul, Matrix.mulVec_smul, hW] at hc
  have he := congrArg (fun v => V.val.det⁻¹ • v) hc
  simpa only [smul_smul, inv_mul_cancel₀ hdet, one_smul, hv] using he

def pureMatrix {ι : Type*} (v : ι → ℂ) : Matrix ι ι ℂ := Matrix.vecMulVec v (star v)

theorem pureMatrix_compression {ι κ : Type*} [Fintype ι]
    (C : Matrix ι κ ℂ) (v : ι → ℂ) :
    C.conjTranspose * pureMatrix v * C = pureMatrix (C.conjTranspose *ᵥ v) := by
  simp only [pureMatrix, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

theorem pureMatrix_smul {ι : Type*} (v : ι → ℂ) (c : ℂ) :
    pureMatrix (c • v) = (Complex.normSq c : ℂ) • pureMatrix v := by
  ext i j
  simp only [pureMatrix, Matrix.vecMulVec_apply, Pi.smul_apply, Pi.star_apply,
    smul_eq_mul, StarMul.star_mul]
  rw [← Complex.mul_conj]
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
    smul_eq_mul, Complex.star_def]
  ac_rfl

theorem pureMatrix_unitary_column {n p : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (S : Index n p) :
    pureMatrix (fun T => exteriorMatrix p U.val T S) =
      exteriorMatrix p U.val * Fermionic.DensityRigidity.basisProjector S *
        (exteriorMatrix p U.val).conjTranspose := by
  rw [Fermionic.DensityRigidity.basisProjector, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    ← Matrix.star_mulVec, Matrix.mulVec_single_one]
  rfl

theorem unitary_column_trace_one {n p : ℕ}
    (U : Matrix.unitaryGroup (Fin n) ℂ) (S : Index n p) :
    (pureMatrix (fun T => exteriorMatrix p U.val T S)).trace = 1 := by
  have hU : (exteriorMatrix p U.val).conjTranspose * exteriorMatrix p U.val = 1 :=
    (exteriorMatrix_mem_unitary p U.val U.property).1
  rw [pureMatrix_unitary_column, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  simp [Fermionic.DensityRigidity.basisProjector, Matrix.trace_vecMulVec,
    dotProduct, Pi.single_apply]

theorem normalized_pos_smul {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (hA : A.trace = 1) (r : ℝ) (hr : 0 < r) :
    normalized ((r : ℂ) • A) = A := by
  have hw : weight ((r : ℂ) • A) = r := by
    simp only [weight, Matrix.trace_smul, hA, smul_eq_mul, mul_one, Complex.ofReal_re]
  rw [normalized, hw, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ (ne_of_gt hr), Complex.ofReal_one, one_smul]

/-- Positive-weight occupation conditioning preserves the original normalized
Slater density orbit.  The conclusion concerns the whole conditional matrix. -/
theorem normalized_compression_isSlater {M p : ℕ} (hp : p ≤ M)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (hρ : IsSlaterDensity ρ)
    (ha : 0 < weight ((creation M p).conjTranspose * ρ * creation M p)) :
    IsSlaterDensity (normalized ((creation M p).conjTranspose * ρ * creation M p)) := by
  obtain ⟨T, U, rfl⟩ := hρ
  rw [← pureMatrix_unitary_column, pureMatrix_compression] at ha ⊢
  have hne : (creation M p).conjTranspose *ᵥ
      (fun S => exteriorMatrix (p + 1) U.val S T) ≠ 0 := by
    intro h
    simp only [h, pureMatrix, star_zero, Matrix.vecMulVec_zero, weight,
      Matrix.trace_zero, Complex.zero_re, lt_self_iff_false] at ha
  obtain ⟨W, S, c, hc, he⟩ := contraction_unitary_column hp U T hne
  rw [he, pureMatrix_smul,
    normalized_pos_smul _ (unitary_column_trace_one W S) _ (Complex.normSq_pos.mpr hc)]
  exact ⟨S, W, pureMatrix_unitary_column W S⟩

theorem rotated_isSlater {n p : ℕ}
    (ρ : Matrix (Index n p) (Index n p) ℂ) (hρ : IsSlaterDensity ρ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) : IsSlaterDensity (rotated n p ρ U) := by
  obtain ⟨S, V, rfl⟩ := hρ
  refine ⟨S, U⁻¹ * V, ?_⟩
  simp only [rotated, Matrix.UnitaryGroup.mul_val, Matrix.UnitaryGroup.inv_val,
    Matrix.star_eq_conjTranspose, exteriorMatrix_mul, exteriorMatrix_conjTranspose,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- The exact original Haar-conditioning matrix has a lower-sector Slater
normalization whenever its original success weight is positive. -/
theorem conditional_isSlater {M p : ℕ} (hp : p ≤ M)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (hρ : IsSlaterDensity ρ) (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (ha : 0 < weight (conditionalMatrix M p ρ U)) :
    IsSlaterDensity (normalized (conditionalMatrix M p ρ U)) :=
  normalized_compression_isSlater hp _ (rotated_isSlater ρ hρ U) ha

end Fermionic.SlaterClosure
