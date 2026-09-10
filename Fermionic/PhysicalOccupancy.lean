import Fermionic.PhysicalGaussian
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Tactic.FinCases

/-!
Constructive preparation of even orthonormal occupancy wedges using the
actual positive Euclidean Spin group and the full Fock representation.
No pure-spinor-to-Gaussian orbit classification is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Fermionic.PhysicalOccupancy

open Module Fermionic.Fock Fermionic.SpinorTransport Fermionic.PhysicalGaussian

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem majorana_square_one (v : H) (hv : ‖v‖ = 1) :
    CliffordAlgebra.ι (majoranaQuadratic (H := H)) v *
      CliffordAlgebra.ι majoranaQuadratic v = 1 := by
  rw [CliffordAlgebra.ι_sq_scalar, majoranaQuadratic_apply, hv, one_pow, map_one]

def majoranaUnit (v : H) (hv : ‖v‖ = 1) :
    (CliffordAlgebra (majoranaQuadratic (H := H)))ˣ where
  val := CliffordAlgebra.ι majoranaQuadratic v
  inv := CliffordAlgebra.ι majoranaQuadratic v
  val_inv := majorana_square_one v hv
  inv_val := majorana_square_one v hv

theorem majoranaUnit_mem_lipschitz (v : H) (hv : ‖v‖ = 1) :
    majoranaUnit v hv ∈ lipschitzGroup (majoranaQuadratic (H := H)) :=
  Subgroup.subset_closure ⟨v, rfl⟩

theorem majorana_pair_mem_spin (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    CliffordAlgebra.ι (majoranaQuadratic (H := H)) v *
      CliffordAlgebra.ι majoranaQuadratic w ∈ spinGroup majoranaQuadratic := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine ⟨majoranaUnit v hv * majoranaUnit w hw, ?_, rfl⟩
    exact (lipschitzGroup majoranaQuadratic).mul_mem
      (majoranaUnit_mem_lipschitz v hv) (majoranaUnit_mem_lipschitz w hw)
  · constructor
    · rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι, neg_mul_neg]
      calc
        _ = CliffordAlgebra.ι majoranaQuadratic w *
            (CliffordAlgebra.ι majoranaQuadratic v * CliffordAlgebra.ι majoranaQuadratic v) *
            CliffordAlgebra.ι majoranaQuadratic w := by simp only [mul_assoc]
        _ = 1 := by rw [majorana_square_one v hv, mul_one, majorana_square_one w hw]
    · rw [star_mul, CliffordAlgebra.star_ι, CliffordAlgebra.star_ι, neg_mul_neg]
      calc
        _ = CliffordAlgebra.ι majoranaQuadratic v *
            (CliffordAlgebra.ι majoranaQuadratic w * CliffordAlgebra.ι majoranaQuadratic w) *
            CliffordAlgebra.ι majoranaQuadratic v := by simp only [mul_assoc]
        _ = 1 := by rw [majorana_square_one w hw, mul_one, majorana_square_one v hv]
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero majoranaQuadratic v w

/-- Two unit Majorana vectors give an actual Spin element. Orthogonality is
not needed for this membership statement. -/
def majoranaPair (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    spinGroup (majoranaQuadratic (H := H)) :=
  ⟨CliffordAlgebra.ι majoranaQuadratic v * CliffordAlgebra.ι majoranaQuadratic w,
    majorana_pair_mem_spin v w hv hw⟩

theorem majoranaPair_action (v w : H) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (s : Space ℂ H) :
    euclideanSpinAction (majoranaPair v w hv hw) s =
      action (majoranaEmbedding v) (action (majoranaEmbedding w) s) := by
  simp only [euclideanSpinAction, majoranaPair, map_mul, majoranaCliffordMap_generator,
    representation_generator, Module.End.mul_apply]

/-- All contraction terms vanish together because the original covector
annihilates every vector in the same complete wedge. -/
theorem annihilate_wedge_eq_zero {r : ℕ} (f : Module.Dual ℂ H) (v : Fin r → H)
    (hf : ∀ i, f (v i) = 0) :
    annihilate f (ExteriorAlgebra.ιMulti ℂ r v) = 0 := by
  induction r with
  | zero => simp [ExteriorAlgebra.ιMulti_zero_apply, annihilate]
  | succ r ih =>
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    change CliffordAlgebra.contractLeft f
      (ExteriorAlgebra.ι ℂ (v 0) * ExteriorAlgebra.ιMulti ℂ r (Matrix.vecTail v)) = 0
    have ht := ih (Matrix.vecTail v) (fun i => hf i.succ)
    change CliffordAlgebra.contractLeft f (ExteriorAlgebra.ιMulti ℂ r (Matrix.vecTail v)) = 0 at ht
    rw [CliffordAlgebra.contractLeft_ι_mul, hf 0, zero_smul, ht, mul_zero, sub_self]

theorem majorana_action_wedge {r : ℕ} (w : H) (v : Fin r → H)
    (hw : ∀ i, inner ℂ w (v i) = 0) :
    action (majoranaEmbedding w) (ExteriorAlgebra.ιMulti ℂ r v) =
      ExteriorAlgebra.ι ℂ w * ExteriorAlgebra.ιMulti ℂ r v := by
  change annihilate (innerₛₗ ℂ w) (ExteriorAlgebra.ιMulti ℂ r v) +
    create w (ExteriorAlgebra.ιMulti ℂ r v) = _
  rw [annihilate_wedge_eq_zero _ v hw, zero_add, create_apply]

/-- Every even orthonormal wedge is prepared exactly, with its original
ordering, by one real Euclidean Spin element acting on the vacuum. -/
theorem even_orthonormal_wedge_orbit (r : ℕ) (v : Fin r → H)
    (hv : Orthonormal ℂ v) (hr : Even r) :
    ∃ x : spinGroup (majoranaQuadratic (H := H)),
      ExteriorAlgebra.ιMulti ℂ r v = euclideanSpinAction x (1 : Space ℂ H) := by
  induction r using Nat.twoStepInduction with
  | zero =>
    exact ⟨1, by simp [ExteriorAlgebra.ιMulti_zero_apply, euclideanSpinAction]⟩
  | one =>
    obtain ⟨k, hk⟩ := hr
    omega
  | more r ih _ =>
    let tail := Matrix.vecTail (Matrix.vecTail v)
    have ht : Orthonormal ℂ tail := hv.comp (fun i : Fin r => i.succ.succ) (by
      intro i j h
      exact Fin.succ_inj.mp (Fin.succ_inj.mp h))
    have he : Even r := by
      obtain ⟨k, hk⟩ := hr
      exact ⟨k - 1, by omega⟩
    obtain ⟨x, hx⟩ := ih tail ht he
    let pair := majoranaPair (v 0) (v (0 : Fin (r + 1)).succ)
      (hv.norm_eq_one 0) (hv.norm_eq_one _)
    have hsecond : action (majoranaEmbedding (v (0 : Fin (r + 1)).succ))
        (ExteriorAlgebra.ιMulti ℂ r tail) =
        ExteriorAlgebra.ιMulti ℂ (r + 1) (Matrix.vecTail v) := by
      conv_rhs => rw [ExteriorAlgebra.ιMulti_succ_apply]
      exact majorana_action_wedge _ tail (fun i => hv.inner_eq_zero (by
        change (0 : Fin (r + 1)).succ ≠ i.succ.succ
        intro h
        exact Fin.succ_ne_zero i (Fin.succ_inj.mp h).symm))
    have hfirst : action (majoranaEmbedding (v 0))
        (ExteriorAlgebra.ιMulti ℂ (r + 1) (Matrix.vecTail v)) =
        ExteriorAlgebra.ιMulti ℂ (r + 2) v := by
      conv_rhs => rw [ExteriorAlgebra.ιMulti_succ_apply]
      exact majorana_action_wedge _ (Matrix.vecTail v) (fun i => hv.inner_eq_zero (by
        exact (Fin.succ_ne_zero i).symm))
    refine ⟨pair * x, ?_⟩
    have hmul : euclideanSpinAction (pair * x) (1 : Space ℂ H) =
        euclideanSpinAction pair (euclideanSpinAction x (1 : Space ℂ H)) := by
      exact congrArg (fun f : Module.End ℂ (Space ℂ H) => f 1)
        (map_mul euclideanSpinRepresentation pair x)
    rw [hmul, ← hx, majoranaPair_action, hsecond, hfirst]

theorem even_orthonormal_wedge_isGaussian (r : ℕ) (v : Fin r → H)
    (hv : Orthonormal ℂ v) (hr : Even r) :
    IsGaussian (ExteriorAlgebra.ιMulti ℂ r v) := by
  obtain ⟨x, hx⟩ := even_orthonormal_wedge_orbit r v hv hr
  exact ⟨x, 1, one_ne_zero, by simpa only [one_smul] using hx⟩

theorem occupancy_isGaussian {I : Type*} [Fintype I] [LinearOrder I]
    (b : OrthonormalBasis I ℂ H) (S : Finset I) (hS : Even S.card) :
    IsGaussian (b.toBasis.ExteriorAlgebra S) := by
  rw [ExteriorAlgebra.basis_apply]
  apply even_orthonormal_wedge_isGaussian
  · exact b.orthonormal.comp _ (Set.powersetCard.ofFinEmbEquiv.symm _).injective
  · exact hS

theorem target_support_isGaussian (i : Fin 4) :
    IsGaussian (Fermionic.PureDecomposition.occupancyBasis
      (Fermionic.PureDecomposition.targetSupports i)) := by
  apply occupancy_isGaussian (EuclideanSpace.basisFun (Fin 8) ℂ)
  fin_cases i <;> decide

theorem target_has_gaussian_decomposition :
    HasDecomposition Fermionic.PureDecomposition.target 4 :=
  ⟨fun i => Fermionic.PureDecomposition.occupancyBasis
      (Fermionic.PureDecomposition.targetSupports i), target_support_isGaussian, rfl⟩

end Fermionic.PhysicalOccupancy
