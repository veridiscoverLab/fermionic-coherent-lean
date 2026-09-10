import Fermionic.RankCertificate
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.FinCases

/-! Trace certificate for the full target Gram. The basis reindexing below is
proved bijective onto all 120 ordered bivector directions. No target spectrum
or target trace value is assumed. -/
namespace Fermionic.RankCertificate

abbrev GramIndex := Fin 24 ⊕ (Fin 64 ⊕ ((Fin 2 × Fin 12) ⊕ (Fin 4 × Fin 2)))

def zeroPair : Fin 24 → Pair := ![(0,9),(0,10),(0,11),(1,8),(1,10),(1,11),(2,8),(2,9),(2,11),(3,8),(3,9),(3,10),(4,13),(4,14),(4,15),(5,12),(5,14),(5,15),(6,12),(6,13),(6,15),(7,12),(7,13),(7,14)]
def crossPair : Fin 64 → Pair := ![(0,4),(0,5),(0,6),(0,7),(0,12),(0,13),(0,14),(0,15),(1,4),(1,5),(1,6),(1,7),(1,12),(1,13),(1,14),(1,15),(2,4),(2,5),(2,6),(2,7),(2,12),(2,13),(2,14),(2,15),(3,4),(3,5),(3,6),(3,7),(3,12),(3,13),(3,14),(3,15),(4,8),(4,9),(4,10),(4,11),(5,8),(5,9),(5,10),(5,11),(6,8),(6,9),(6,10),(6,11),(7,8),(7,9),(7,10),(7,11),(8,12),(8,13),(8,14),(8,15),(9,12),(9,13),(9,14),(9,15),(10,12),(10,13),(10,14),(10,15),(11,12),(11,13),(11,14),(11,15)]
def twoPair : Fin 24 → Pair := ![(0,1),(10,11),(0,2),(9,11),(0,3),(9,10),(1,2),(8,11),(1,3),(8,10),(2,3),(8,9),(4,5),(14,15),(4,6),(13,15),(4,7),(13,14),(5,6),(12,15),(5,7),(12,14),(6,7),(12,13)]
def offDiagonal : Fin 12 → ℤ := ![-8,8,-8,-8,8,-8,-8,8,-8,-8,8,-8]

def coordinatePair : GramIndex → Pair
  | .inl i => zeroPair i
  | .inr (.inl i) => crossPair i
  | .inr (.inr (.inl (i,j))) => twoPair ⟨2*j.val+i.val, by omega⟩
  | .inr (.inr (.inr (i,j))) =>
      (⟨4*j.val+i.val, by omega⟩, ⟨4*j.val+i.val+8, by omega⟩)

set_option maxRecDepth 100000 in
theorem coordinate_pair_sorted :
    ∀ i : GramIndex, (coordinatePair i).1 < (coordinatePair i).2 := by
  decide

abbrev SortedPair := {p : Pair // p.1 < p.2}
def basisPair (i : GramIndex) : SortedPair :=
  ⟨coordinatePair i, coordinate_pair_sorted i⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem basisPair_bijective : Function.Bijective basisPair := by
  decide

def targetMatrix : Matrix GramIndex GramIndex ℤ :=
  fun i j => targetGram4 (coordinatePair i) (coordinatePair j)

def smallTwo (j : Fin 12) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![8, offDiagonal j; offDiagonal j, 8]
def smallFour : Matrix (Fin 4) (Fin 4) ℤ := fun _ _ => 4

def targetNormalMatrix : Matrix GramIndex GramIndex ℤ :=
  Matrix.fromBlocks (0 : Matrix (Fin 24) (Fin 24) ℤ) 0 0
    (Matrix.fromBlocks (Matrix.diagonal (fun _ : Fin 64 => (4 : ℤ))) 0 0
      (Matrix.fromBlocks (Matrix.blockDiagonal smallTwo) 0 0
        (Matrix.blockDiagonal (fun _ : Fin 2 => smallFour))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sparse_in_blocks :
    ∀ i j : GramIndex,
      targetGramSparse (coordinatePair i) (coordinatePair j) =
        targetNormalMatrix i j := by
  decide

theorem targetMatrix_eq : targetMatrix = targetNormalMatrix := by
  ext i j
  change targetGram4 (coordinatePair i) (coordinatePair j) = _
  rw [target_gram_all_entries _ _ _ _ (coordinate_pair_sorted i) (coordinate_pair_sorted j)]
  exact sparse_in_blocks i j

lemma trace_from_blocks {n m : Type*} [Fintype n] [Fintype m]
    (A : Matrix n n ℤ) (D : Matrix m m ℤ) :
    Matrix.trace (Matrix.fromBlocks A 0 0 D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.fromBlocks, Fintype.sum_sum_type]

theorem target_trace_power (k : ℕ) (hk : 0 < k) :
    Matrix.trace (targetMatrix ^ k) =
      64 * 4^k + (∑ j : Fin 12, Matrix.trace (smallTwo j ^ k)) +
        2 * Matrix.trace (smallFour ^ k) := by
  rw [targetMatrix_eq]
  simp only [targetNormalMatrix, Matrix.fromBlocks_diagonal_pow, trace_from_blocks,
    Matrix.diagonal_pow, ← Matrix.blockDiagonal_pow, Matrix.trace_blockDiagonal,
    Pi.pow_apply]
  simp [zero_pow (by omega : k ≠ 0), Matrix.trace_diagonal]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallTwo_trace_four : ∀ j : Fin 12,
    Matrix.trace (smallTwo j ^ 4) = 16^4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallTwo_trace_six : ∀ j : Fin 12,
    Matrix.trace (smallTwo j ^ 6) = 16^6 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallFour_trace_four :
    Matrix.trace (smallFour ^ 4) = 16^4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem smallFour_trace_six :
    Matrix.trace (smallFour ^ 6) = 16^6 := by
  decide

theorem target_int_trace_four :
    Matrix.trace (targetMatrix ^ 4) = 4^4 * 3648 := by
  rw [target_trace_power 4 (by omega), smallFour_trace_four]
  simp_rw [smallTwo_trace_four]
  norm_num

theorem target_int_trace_six :
    Matrix.trace (targetMatrix ^ 6) = 4^6 * 57408 := by
  rw [target_trace_power 6 (by omega), smallFour_trace_six]
  simp_rw [smallTwo_trace_six]
  norm_num


/-- The complete target Gram in complex coordinates, with the original
normalization A = (1/4) K restored. -/
noncomputable def actualTargetGram : Matrix GramIndex GramIndex ℂ :=
  (1/4 : ℂ) • targetMatrix.map (Int.castRingHom ℂ)

theorem actual_target_trace_four :
    Matrix.trace (actualTargetGram ^ 4) = 3648 := by
  unfold actualTargetGram
  rw [smul_pow, Matrix.trace_smul, ← Matrix.map_pow,
    ← AddMonoidHom.map_trace, target_int_trace_four]
  norm_num

theorem actual_target_trace_six :
    Matrix.trace (actualTargetGram ^ 6) = 57408 := by
  unfold actualTargetGram
  rw [smul_pow, Matrix.trace_smul, ← Matrix.map_pow,
    ← AddMonoidHom.map_trace, target_int_trace_six]
  norm_num

def invariant18 (s t4 t6 : ℂ) : ℂ := s * invariant16 s t4 t6

theorem actual_target_certificate :
    invariant18 2 (Matrix.trace (actualTargetGram ^ 4))
      (Matrix.trace (actualTargetGram ^ 6)) = 18063360 := by
  rw [actual_target_trace_four, actual_target_trace_six]
  norm_num [invariant18, invariant16]

theorem actual_target_certificate_nonzero :
    invariant18 2 (Matrix.trace (actualTargetGram ^ 4))
      (Matrix.trace (actualTargetGram ^ 6)) ≠ 0 := by
  rw [actual_target_certificate]
  norm_num


/-- Direct Chevalley self-pairing of all four target occupation terms. -/
def targetChevalleySelf : ℤ :=
  ∑ r : Fin 4, chevalleySign (targetMask r) *
    targetCoefficient (Nat.xor 255 (targetMask r))

theorem targetChevalleySelf_eq : targetChevalleySelf = 4 := by decide

noncomputable def actualTargetHalfPair : ℂ := (targetChevalleySelf : ℂ) / 2

theorem actualTargetHalfPair_eq : actualTargetHalfPair = 2 := by
  unfold actualTargetHalfPair
  rw [targetChevalleySelf_eq]
  norm_num

/-- The complete nonzero invariant certificate of the fixed target in the
explicit occupied basis, with no trace or self-pairing assumptions. -/
theorem full_coordinate_target_certificate :
    invariant18 actualTargetHalfPair (Matrix.trace (actualTargetGram ^ 4))
      (Matrix.trace (actualTargetGram ^ 6)) = 18063360 := by
  rw [actualTargetHalfPair_eq]
  exact actual_target_certificate

theorem full_coordinate_target_certificate_nonzero :
    invariant18 actualTargetHalfPair (Matrix.trace (actualTargetGram ^ 4))
      (Matrix.trace (actualTargetGram ^ 6)) ≠ 0 := by
  rw [full_coordinate_target_certificate]
  norm_num

end Fermionic.RankCertificate

#print axioms Fermionic.RankCertificate.basisPair_bijective
#print axioms Fermionic.RankCertificate.target_int_trace_four
#print axioms Fermionic.RankCertificate.target_int_trace_six

#print axioms Fermionic.RankCertificate.actual_target_certificate_nonzero

#print axioms Fermionic.RankCertificate.full_coordinate_target_certificate_nonzero
