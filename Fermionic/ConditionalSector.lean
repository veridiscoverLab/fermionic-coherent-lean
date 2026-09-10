import Fermionic.ExteriorUnitary
import Fermionic.HaarConditioning
import Fermionic.DensityRigidity
import Fermionic.OccupationMixture
import Mathlib.Analysis.Complex.Order

/-!
# The actual first-occupation sector and its full density compression

The rectangular inclusion below maps each original occupancy basis vector to
the basis vector obtained by adjoining the first mode.  Compression retains
all matrix entries between the retained states, including their cross terms.
-/

noncomputable section

namespace Fermionic.ConditionalSector

open Matrix Fermionic.ExteriorUnitary
open scoped ComplexOrder

def insertFirst {M p : ℕ} (S : Index M p) : Index (M + 1) (p + 1) :=
  ⟨insert 0 (S.val.map (Fin.succEmb M)), by
    have hzero : (0 : Fin (M + 1)) ∉ S.val.map (Fin.succEmb M) := by simp
    simp [hzero]⟩

@[simp] theorem mem_insertFirst_zero {M p : ℕ} (S : Index M p) :
    (0 : Fin (M + 1)) ∈ (insertFirst S).val := by simp [insertFirst]

@[simp] theorem mem_insertFirst_succ {M p : ℕ} (S : Index M p) (i : Fin M) :
    i.succ ∈ (insertFirst S).val ↔ i ∈ S.val := by simp [insertFirst]

theorem insertFirst_injective (M p : ℕ) :
    Function.Injective (insertFirst (M := M) (p := p)) := by
  intro S T h
  apply Subtype.ext
  ext i
  rw [← mem_insertFirst_succ S i, h, mem_insertFirst_succ T i]

/-- Every original occupancy containing the first mode is retained; no
additional occupied coordinate is excluded from the conditional sector. -/
theorem insertFirst_surjective_occupied {M p : ℕ} (T : Index (M + 1) (p + 1))
    (h0 : (0 : Fin (M + 1)) ∈ T.val) : ∃ S : Index M p, insertFirst S = T := by
  let s : Finset (Fin M) := Finset.univ.filter (fun i => i.succ ∈ T.val)
  have hs : s.map (Fin.succEmb M) = T.val.erase 0 := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [s]
  have hcard : s.card = p := by
    have h := congrArg Finset.card hs
    simpa [Finset.card_erase_of_mem h0, T.property] using h
  refine ⟨⟨s, hcard⟩, ?_⟩
  apply Subtype.ext
  change insert 0 (s.map (Fin.succEmb M)) = T.val
  rw [hs, Finset.insert_erase h0]

theorem insertFirst_range (M p : ℕ) :
    Set.range (insertFirst (M := M) (p := p)) =
      {T : Index (M + 1) (p + 1) | (0 : Fin (M + 1)) ∈ T.val} := by
  ext T
  constructor
  · rintro ⟨S, rfl⟩
    exact mem_insertFirst_zero S
  · exact insertFirst_surjective_occupied T

theorem sum_insertFirst (M p : ℕ) (f : Index (M + 1) (p + 1) → ℂ) :
    ∑ S : Index M p, f (insertFirst S) =
      ∑ T : Index (M + 1) (p + 1), if (0 : Fin (M + 1)) ∈ T.val then f T else 0 := by
  have him : Finset.univ.image (insertFirst (M := M) (p := p)) =
      Finset.univ.filter (fun T => (0 : Fin (M + 1)) ∈ T.val) := by
    ext T
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    change T ∈ Set.range (insertFirst (M := M) (p := p)) ↔ _
    rw [insertFirst_range]
    rfl
  calc
    _ = ∑ T ∈ Finset.univ.image (insertFirst (M := M) (p := p)), f T := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => insertFirst_injective M p hij
    _ = _ := by rw [him, Finset.sum_filter]

theorem enumerate_insertFirst {M p : ℕ} (S : Index M p) :
    enumerate (insertFirst S) = Fin.cons 0 (fun i => (enumerate S i).succ) := by
  have hmem (i : Fin (p + 1)) :
      (Fin.cons (0 : Fin (M + 1)) (fun i => (enumerate S i).succ) :
        Fin (p + 1) → Fin (M + 1)) i ∈
        (insertFirst S).val := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp only [Fin.cons_succ, mem_insertFirst_succ]
      exact Finset.orderEmbOfFin_mem S.val S.property j
  have hmono : StrictMono (Fin.cons (0 : Fin (M + 1))
      (fun i => (enumerate S i).succ)) := by
    intro i j hij
    revert hij
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · intro _
      exact Fin.succ_pos _
    · simp
    · intro h
      exact Fin.succ_lt_succ_iff.mpr
        ((Set.powersetCard.ofFinEmbEquiv.symm S).strictMono
          (Fin.succ_lt_succ_iff.mp h))
  exact (Finset.orderEmbOfFin_unique (insertFirst S).property hmem hmono).symm

@[simp] theorem enumerate_insertFirst_zero {M p : ℕ} (S : Index M p) :
    enumerate (insertFirst S) 0 = 0 := by simp [enumerate_insertFirst]

@[simp] theorem enumerate_insertFirst_succ {M p : ℕ} (S : Index M p) (i : Fin p) :
    enumerate (insertFirst S) i.succ = (enumerate S i).succ := by
  simp [enumerate_insertFirst]

section BasisInclusion

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Inclusion of the specified actual coordinate vectors. -/
def basisInclusion (f : I → J) : Matrix J I ℂ := fun j i => if j = f i then 1 else 0

omit [Fintype I] [DecidableEq I] in
theorem basisInclusion_compress_apply (f : I → J) (A : Matrix J J ℂ) (i j : I) :
    ((basisInclusion f).conjTranspose * A * basisInclusion f) i j = A (f i) (f j) := by
  simp [Matrix.mul_apply, basisInclusion, Matrix.conjTranspose_apply]

omit [Fintype I] [DecidableEq I] in
/-- Every retained cross entry agrees with the corresponding original entry. -/
theorem basisInclusion_compress (f : I → J) (A : Matrix J J ℂ) :
    (basisInclusion f).conjTranspose * A * basisInclusion f = A.submatrix f f := by
  ext i j
  exact basisInclusion_compress_apply f A i j

omit [Fintype I] in
theorem basisInclusion_isometry (f : I → J) (hf : Function.Injective f) :
    (basisInclusion f).conjTranspose * basisInclusion f = 1 := by
  have h := basisInclusion_compress f (1 : Matrix J J ℂ)
  have h1 : (1 : Matrix J J ℂ).submatrix f f = (1 : Matrix I I ℂ) := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, hf.eq_iff]
  simpa only [Matrix.mul_one, h1] using h

omit [DecidableEq I] in
theorem basisInclusion_compress_posSemidef (f : I → J) {A : Matrix J J ℂ}
    (hA : A.PosSemidef) :
    ((basisInclusion f).conjTranspose * A * basisInclusion f).PosSemidef :=
  hA.conjTranspose_mul_mul_same (basisInclusion f)

omit [DecidableEq I] in
/-- The success weight is at most the original total trace.  This uses the
actual retained diagonal entries and does not add bounds on the cross entries. -/
theorem basisInclusion_compress_trace_le_one (f : I → J) (hf : Function.Injective f)
    {A : Matrix J J ℂ} (hA : A.PosSemidef) (htrace : A.trace = 1) :
    (((basisInclusion f).conjTranspose * A * basisInclusion f).trace).re ≤ 1 := by
  have hnonneg (j : J) : 0 ≤ (A j j).re :=
    (Complex.nonneg_iff.mp hA.diag_nonneg).1
  have ht : (∑ j, A j j).re = 1 := by simpa [Matrix.trace] using congrArg Complex.re htrace
  change (∑ i, ((basisInclusion f).conjTranspose * A * basisInclusion f) i i).re ≤ 1
  simp_rw [basisInclusion_compress_apply, Complex.re_sum]
  calc
    _ = ∑ j ∈ Finset.univ.image f, (A j j).re := by
      rw [Finset.sum_image]
      exact fun i _ j _ hij => hf hij
    _ ≤ ∑ j : J, (A j j).re := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun j _ _ => hnonneg j)
    _ = 1 := by simpa only [Complex.re_sum] using ht

end BasisInclusion

/-- An isometric subspace with unitary compressed action is actually invariant.
This proves the full intertwiner, including all entries outside the retained
coordinates, rather than assuming that compression discards no leakage. -/
theorem intertwine_of_unitary_compression {I J : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (C : Matrix J I ℂ) (R : Matrix J J ℂ) (L : Matrix I I ℂ)
    (hC : C.conjTranspose * C = 1)
    (hR : R.conjTranspose * R = 1) (hL : L.conjTranspose * L = 1)
    (hc : C.conjTranspose * R * C = L) : R * C = C * L := by
  have hcs : C.conjTranspose * R.conjTranspose * C = L.conjTranspose := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using congrArg Matrix.conjTranspose hc
  apply sub_eq_zero.mp
  apply Matrix.conjTranspose_mul_self_eq_zero.mp
  calc
    (R * C - C * L).conjTranspose * (R * C - C * L) =
        C.conjTranspose * (R.conjTranspose * R) * C -
          L.conjTranspose * (C.conjTranspose * R * C) -
          ((C.conjTranspose * R.conjTranspose * C) * L -
            L.conjTranspose * (C.conjTranspose * C) * L) := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = 0 := by simp [hR, hcs, hc, hC, hL]

section DensityCompression

variable {I J : Type*} [Fintype I] [Fintype J]

def quadratic (A : Matrix I I ℂ) (v : I → ℂ) : ℝ :=
  (star v ⬝ᵥ (A *ᵥ v)).re

/-- The exact quadratic readout of a rectangular compression. -/
theorem quadratic_compression (A : Matrix J J ℂ) (C : Matrix J I ℂ) (v : I → ℂ) :
    quadratic A (C *ᵥ v) = quadratic (C.conjTranspose * A * C) v := by
  simp only [quadratic, star_mulVec, dotProduct_mulVec, vecMul_vecMul]

theorem quadratic_smul (r : ℝ) (A : Matrix I I ℂ) (v : I → ℂ) :
    quadratic ((r : ℂ) • A) v = r * quadratic A v := by
  simp only [quadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  exact Complex.re_ofReal_mul r _

def weight (A : Matrix I I ℂ) : ℝ := A.trace.re

theorem weight_nonneg {A : Matrix I I ℂ} (hA : A.PosSemidef) : 0 ≤ weight A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

theorem trace_eq_weight {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    A.trace = (weight A : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (Complex.nonneg_iff.mp hA.trace_nonneg).2.symm

/-- A zero success weight annihilates the whole positive conditional matrix. -/
theorem compression_zero_of_weight_zero {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (ha : weight A = 0) : A = 0 := by
  apply Fermionic.DensityRigidity.eq_zero_of_trace_eq_zero hA
  rw [trace_eq_weight hA, ha, Complex.ofReal_zero]

/-- Normalization is performed on the full original compression. -/
def normalized (A : Matrix I I ℂ) : Matrix I I ℂ := (↑((weight A)⁻¹) : ℂ) • A

theorem normalized_posSemidef {A : Matrix I I ℂ} (hA : A.PosSemidef) :
    (normalized A).PosSemidef :=
  hA.smul (Complex.nonneg_iff.mpr
    ⟨by simpa using inv_nonneg.mpr (weight_nonneg hA), by simp⟩)

theorem normalized_trace_eq_one {A : Matrix I I ℂ} (hA : A.PosSemidef)
    (ha : 0 < weight A) : (normalized A).trace = 1 := by
  simp only [normalized, Matrix.trace_smul, trace_eq_weight hA, smul_eq_mul,
    ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt ha), Complex.ofReal_one]

theorem weight_smul_normalized {A : Matrix I I ℂ} (ha : weight A ≠ 0) :
    (weight A : ℂ) • normalized A = A := by
  simp only [normalized, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ha,
    Complex.ofReal_one, one_smul]

/-- The positive branch readout identity, with the original success weight. -/
theorem quadratic_eq_weight_mul_normalized {A : Matrix I I ℂ}
    (ha : weight A ≠ 0) (v : I → ℂ) :
    quadratic A v = weight A * quadratic (normalized A) v := by
  rw [← quadratic_smul, weight_smul_normalized ha]

end DensityCompression

/-- The actual first-mode creation matrix between the two particle sectors. -/
def creation (M p : ℕ) : Matrix (Index (M + 1) (p + 1)) (Index M p) ℂ :=
  basisInclusion insertFirst

theorem creation_isometry (M p : ℕ) :
    (creation M p).conjTranspose * creation M p = 1 :=
  basisInclusion_isometry _ (insertFirst_injective M p)

@[simp] theorem creation_conjTranspose_mulVec (M p : ℕ)
    (v : Index (M + 1) (p + 1) → ℂ) (S : Index M p) :
    ((creation M p).conjTranspose *ᵥ v) S = v (insertFirst S) := by
  simp [creation, basisInclusion, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply]

/-- The conditional trace is exactly the original first-mode occupation. -/
theorem creation_trace_eq_oneParticle (M p : ℕ)
    (A : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ) :
    ((creation M p).conjTranspose * A * creation M p).trace =
      Fermionic.ExteriorDifferential.oneParticle A 0 0 := by
  simp only [Matrix.trace, Matrix.diag_apply, creation, basisInclusion_compress_apply,
    Fermionic.ExteriorDifferential.oneParticle_diag]
  rw [sum_insertFirst M p (fun T => A T T)]
  apply Finset.sum_congr rfl
  intro T _
  split_ifs <;> simp

/-- The occupied-occupied minor is the original lower-sector minor, with its
actual increasing enumeration and determinant sign. -/
theorem exteriorMatrix_fixFirst_compress (M p : ℕ)
    (U : Matrix.unitaryGroup (Fin M) ℂ) :
    (creation M p).conjTranspose *
      exteriorMatrix (p + 1) (HaarConditioning.fixFirstFinHom M U).val * creation M p =
      exteriorMatrix p U.val := by
  ext S T
  rw [creation, basisInclusion_compress_apply, exteriorMatrix_entry,
    exteriorMatrix_entry, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  simp only [Matrix.of_apply, enumerate_insertFirst_zero,
    enumerate_insertFirst_succ, HaarConditioning.fixFirstFinHom_zero_zero,
    HaarConditioning.fixFirstFinHom_succ_zero, Fin.val_zero, pow_zero,
    mul_one, zero_mul, mul_zero, Finset.sum_const_zero, add_zero,
    Fin.succAbove_zero, one_mul]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply]

/-- The actual first-mode creation operation intertwines the original exterior
representations of the fixed-first-mode unitary subgroup. -/
theorem creation_intertwine (M p : ℕ) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    exteriorMatrix (p + 1) (HaarConditioning.fixFirstFinHom M U).val * creation M p =
      creation M p * exteriorMatrix p U.val := by
  exact intertwine_of_unitary_compression _ _ _ (creation_isometry M p)
    (exteriorMatrix_mem_unitary (p + 1) _
      (HaarConditioning.fixFirstFinHom M U).property).1
    (exteriorMatrix_mem_unitary p U.val U.property).1
    (exteriorMatrix_fixFirst_compress M p U)

/-- Rotate the original full density matrix by the actual exterior unitary. -/
def rotated (M p : ℕ) (ρ : Matrix (Index M p) (Index M p) ℂ)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : Matrix (Index M p) (Index M p) ℂ :=
  (exteriorMatrix p U.val).conjTranspose * ρ * exteriorMatrix p U.val

theorem rotated_posSemidef (M p : ℕ) {ρ : Matrix (Index M p) (Index M p) ℂ}
    (hρ : ρ.PosSemidef) (U : Matrix.unitaryGroup (Fin M) ℂ) :
    (rotated M p ρ U).PosSemidef := hρ.conjTranspose_mul_mul_same _

theorem rotated_trace (M p : ℕ) (ρ : Matrix (Index M p) (Index M p) ℂ)
    (U : Matrix.unitaryGroup (Fin M) ℂ) : (rotated M p ρ U).trace = ρ.trace := by
  have hU : exteriorMatrix p U.val * (exteriorMatrix p U.val).conjTranspose = 1 :=
    (exteriorMatrix_mem_unitary p U.val U.property).2
  rw [rotated, Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- Complete first-mode compression of the same rotated original state. -/
def conditionalMatrix (M p : ℕ)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) : Matrix (Index M p) (Index M p) ℂ :=
  (creation M p).conjTranspose * rotated (M + 1) (p + 1) ρ U * creation M p

theorem conditionalMatrix_posSemidef (M p : ℕ)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) :
    (conditionalMatrix M p ρ U).PosSemidef :=
  (rotated_posSemidef _ _ hρ U).conjTranspose_mul_mul_same _

theorem conditional_weight_mem_unitInterval (M p : ℕ)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (htrace : ρ.trace = 1)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) :
    weight (conditionalMatrix M p ρ U) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact weight_nonneg (conditionalMatrix_posSemidef M p hρ U)
  · exact basisInclusion_compress_trace_le_one _ (insertFirst_injective M p)
      (rotated_posSemidef _ _ hρ U) ((rotated_trace _ _ ρ U).trans htrace)

/-- The success probability and the one-particle readout are two exact readings
of the same original density matrix and the same unitary, with no replacement
of that density by its one-particle reduction. -/
theorem conditional_weight_eq_oneParticleReadout (M p : ℕ)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ) :
    weight (conditionalMatrix M p ρ U) =
      Fermionic.OccupationMixture.oneParticleReadout ρ 0 U := by
  rw [weight, conditionalMatrix, creation_trace_eq_oneParticle, rotated,
    Fermionic.ExteriorDifferential.oneParticle_unitary_conjugation]
  rfl

/-- The original full Husimi quadratic readout after the two genuine unitary
actions is exactly the readout of the conditional full matrix.  The reference
vector is arbitrary, so all subsequent lower-sector observations are retained. -/
theorem conditional_readout (M p : ℕ)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (V : Matrix.unitaryGroup (Fin M) ℂ) (v : Index M p → ℂ) :
    quadratic ρ (exteriorMatrix (p + 1)
      (U * HaarConditioning.fixFirstFinHom M V).val *ᵥ (creation M p *ᵥ v)) =
      quadratic (conditionalMatrix M p ρ U) (exteriorMatrix p V.val *ᵥ v) := by
  have hv : exteriorMatrix (p + 1)
      (U * HaarConditioning.fixFirstFinHom M V).val *ᵥ (creation M p *ᵥ v) =
      exteriorMatrix (p + 1) U.val *ᵥ
        (creation M p *ᵥ (exteriorMatrix p V.val *ᵥ v)) := by
    change exteriorMatrix (p + 1)
      (U.val * (HaarConditioning.fixFirstFinHom M V).val) *ᵥ _ = _
    rw [exteriorMatrix_mul]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, creation_intertwine]
  rw [hv, quadratic_compression, quadratic_compression]
  rfl

/-- The zero-success branch vanishes for every later original observation. -/
theorem conditional_readout_zero (M p : ℕ)
    {ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ}
    (hρ : ρ.PosSemidef) (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (ha : weight (conditionalMatrix M p ρ U) = 0)
    (V : Matrix.unitaryGroup (Fin M) ℂ) (v : Index M p → ℂ) :
    quadratic ρ (exteriorMatrix (p + 1)
      (U * HaarConditioning.fixFirstFinHom M V).val *ᵥ (creation M p *ᵥ v)) = 0 := by
  rw [conditional_readout, compression_zero_of_weight_zero
    (conditionalMatrix_posSemidef M p hρ U) ha]
  simp [quadratic]

/-- Exact positive-branch factorization by the actual conditional probability. -/
theorem conditional_readout_normalized (M p : ℕ)
    (ρ : Matrix (Index (M + 1) (p + 1)) (Index (M + 1) (p + 1)) ℂ)
    (U : Matrix.unitaryGroup (Fin (M + 1)) ℂ)
    (ha : weight (conditionalMatrix M p ρ U) ≠ 0)
    (V : Matrix.unitaryGroup (Fin M) ℂ) (v : Index M p → ℂ) :
    quadratic ρ (exteriorMatrix (p + 1)
      (U * HaarConditioning.fixFirstFinHom M V).val *ᵥ (creation M p *ᵥ v)) =
      weight (conditionalMatrix M p ρ U) *
        quadratic (normalized (conditionalMatrix M p ρ U))
          (exteriorMatrix p V.val *ᵥ v) := by
  rw [conditional_readout, quadratic_eq_weight_mul_normalized ha]

end Fermionic.ConditionalSector
