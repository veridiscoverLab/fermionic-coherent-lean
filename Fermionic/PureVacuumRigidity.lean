import Fermionic.PureVacuumChart
import Fermionic.FockVacuumKernel
import Fermionic.PhysicalGaussianRank

/-!
Rigidity in the original nonzero-vacuum pure-spinor chart, followed by an
actual readout of the unchanged four-term eight-mode target. The resulting
lower bound is two, not four; no three-term exclusion is asserted.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Fermionic.PureVacuumRigidity

open Module Fermionic.Fock Fermionic.Spinor Fermionic.PureVacuumChart

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem graphDirection_eq_zero [FiniteDimensional K E] (s : Space K E)
    (hs : IsPure s) (h0 : vacuumCoefficient s ≠ 0)
    (h2 : ∀ f g : Module.Dual K E,
      vacuumCoefficient (annihilate g (annihilate f s)) = 0) :
    graphDirection s hs h0 = 0 := by
  ext f
  apply (Module.Free.chooseBasis K E).eval_injective
  ext g
  have h := graphDirection_two_contractions s hs h0 f g
  rw [h2 f g, neg_zero, zero_div] at h
  simpa using h

theorem pure_zero_two_contractions_is_vacuum [FiniteDimensional K E] [CharZero K]
    (s : Space K E) (hs : IsPure s) (h0 : vacuumCoefficient s ≠ 0)
    (h2 : ∀ f g : Module.Dual K E,
      vacuumCoefficient (annihilate g (annihilate f s)) = 0) :
    s = vacuumCoefficient s • (1 : Space K E) := by
  apply Fermionic.FockVacuumKernel.joint_annihilation_kernel
  intro f
  have h := graphDirection_annihilates s hs h0 f
  rw [graphDirection_eq_zero s hs h0 h2, LinearMap.zero_apply] at h
  simpa [create] using h

theorem vacuumCoefficient_wedge_zero {r : ℕ} (v : Fin r → E) (hr : r ≠ 0) :
    vacuumCoefficient (ExteriorAlgebra.ιMulti K r v) = 0 := by
  cases r with
  | zero => exact (hr rfl).elim
  | succ r =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    exact vacuumCoefficient_create _ _

theorem vacuumCoefficient_one_contraction_wedge {r : ℕ} (f : Module.Dual K E)
    (v : Fin r → E) (hr : r ≠ 1) :
    vacuumCoefficient (annihilate f (ExteriorAlgebra.ιMulti K r v)) = 0 := by
  cases r with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, annihilate]
  | succ r =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change vacuumCoefficient (annihilate f
      (create (v 0) (ExteriorAlgebra.ιMulti K r (Matrix.vecTail v)))) = 0
    rw [vacuumCoefficient_annihilate_create,
      vacuumCoefficient_wedge_zero _ (by omega), mul_zero]

theorem vacuumCoefficient_two_contractions_wedge {r : ℕ}
    (f g : Module.Dual K E) (v : Fin r → E) (hr : r ≠ 2) :
    vacuumCoefficient (annihilate g (annihilate f (ExteriorAlgebra.ιMulti K r v))) = 0 := by
  cases r with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, annihilate]
  | succ r =>
    let t := ExteriorAlgebra.ιMulti K r (Matrix.vecTail v)
    have h : annihilate f (create (v 0) t) = f (v 0) • t - create (v 0) (annihilate f t) :=
      eq_sub_of_add_eq (mixed_car f (v 0) t)
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change vacuumCoefficient (annihilate g (annihilate f (create (v 0) t))) = 0
    rw [h]
    simp only [map_sub, map_smul, vacuumCoefficient_annihilate_create]
    have hf : vacuumCoefficient (annihilate f t) = 0 :=
      vacuumCoefficient_one_contraction_wedge f _ (by omega)
    have hg : vacuumCoefficient (annihilate g t) = 0 :=
      vacuumCoefficient_one_contraction_wedge g _ (by omega)
    rw [hf, hg, smul_zero, mul_zero, sub_self]

theorem vacuumCoefficient_two_contractions_basis {I : Type*} [LinearOrder I]
    (b : Basis I K E) (S : Finset I) (hS : S.card ≠ 2) (f g : Module.Dual K E) :
    vacuumCoefficient (annihilate g (annihilate f (b.ExteriorAlgebra S))) = 0 := by
  rw [ExteriorAlgebra.basis_apply]
  exact vacuumCoefficient_two_contractions_wedge f g _ hS

theorem vacuumCoefficient_basis {I : Type*} [LinearOrder I]
    (b : Basis I K E) (S : Finset I) :
    vacuumCoefficient (b.ExteriorAlgebra S) = if S = ∅ then 1 else 0 := by
  classical
  by_cases hS : S = ∅
  · subst S
    rw [ExteriorAlgebra.basis_apply]
    change vacuumCoefficient (ExteriorAlgebra.ιMulti K 0 _) = _
    rw [ExteriorAlgebra.ιMulti_zero_apply, map_one, if_pos rfl]
  · rw [if_neg hS, ExteriorAlgebra.basis_apply]
    exact vacuumCoefficient_wedge_zero _
      (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS))

open Fermionic.PureDecomposition

theorem target_vacuumCoefficient : vacuumCoefficient target = 1 := by
  simp only [target, map_sum]
  change (∑ i : Fin 4, vacuumCoefficient
    ((EuclideanSpace.basisFun (Fin 8) ℂ).toBasis.ExteriorAlgebra (targetSupports i))) = 1
  simp only [vacuumCoefficient_basis, Fin.sum_univ_succ]
  simp [targetSupports, Finset.univ_nonempty.ne_empty]

theorem target_two_contractions_zero (f g : Module.Dual ℂ ModeSpace) :
    vacuumCoefficient (annihilate g (annihilate f target)) = 0 := by
  simp only [target, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply vacuumCoefficient_two_contractions_basis
  fin_cases i <;> decide

theorem target_first_block_coefficient :
    occupancyBasis.repr target ({0, 1, 2, 3} : Finset (Fin 8)) = 1 := by
  have hB : ({4, 5, 6, 7} : Finset (Fin 8)) ≠ {0, 1, 2, 3} := by decide
  have hU : (Finset.univ : Finset (Fin 8)) ≠ {0, 1, 2, 3} := by decide
  simp [target, targetSupports, Fin.sum_univ_succ, Basis.repr_self, hB, hU]

theorem target_ne_vacuum : target ≠ (1 : TargetSpace) := by
  intro h
  have hc := target_first_block_coefficient
  have he : occupancyBasis ∅ = (1 : TargetSpace) := by
    rw [occupancyBasis, ExteriorAlgebra.basis_apply]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  rw [h, ← he, Basis.repr_self] at hc
  simp at hc

theorem target_not_pure : ¬IsPure target := by
  intro hs
  have h0 : vacuumCoefficient target ≠ 0 := by rw [target_vacuumCoefficient]; exact one_ne_zero
  have h := pure_zero_two_contractions_is_vacuum target hs h0 target_two_contractions_zero
  rw [target_vacuumCoefficient, one_smul] at h
  exact target_ne_vacuum h

theorem targetGaussianRank_ne_one :
    Fermionic.PhysicalGaussianRank.targetGaussianRank ≠ 1 := by
  intro h
  have hd := Fermionic.PhysicalGaussianRank.targetGaussianRank_spec
  rw [h] at hd
  obtain ⟨g, hg, he⟩ := hd
  have ht : target = g 0 := by simpa using he
  apply target_not_pure
  rw [ht]
  exact Fermionic.PhysicalGaussian.gaussian_isPure (g 0) (hg 0)

theorem two_le_targetGaussianRank : 2 ≤ Fermionic.PhysicalGaussianRank.targetGaussianRank := by
  have h := Fermionic.PhysicalGaussianRank.one_le_targetGaussianRank
  have hn := targetGaussianRank_ne_one
  omega

end Fermionic.PureVacuumRigidity
