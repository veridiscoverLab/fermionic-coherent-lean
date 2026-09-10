import FermionicRankGeometry
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
#check @Fermionic.Fock.Space
#check @Fermionic.Fock.create
#check @Fermionic.Fock.annihilate
#check @Fermionic.Fock.create_apply
#check @Fermionic.Fock.annihilate_apply
#check @Fermionic.Fock.create_square
#check @Fermionic.Fock.annihilate_square
#check @Fermionic.Fock.mixed_car
#check @Fermionic.Fock.action
#check @Fermionic.Fock.action_apply
#check @Fermionic.Fock.action_square
#check @Fermionic.Fock.action_square_end
#check @Fermionic.Fock.action_car
#check @Fermionic.Fock.representation
#check @Fermionic.Fock.representation_generator
#check @Fermionic.Fock.occupation
#check @Fermionic.Fock.vacancy
#check @Fermionic.Fock.occupation_vacancy
#check @Fermionic.Fock.occupation_idempotent
#check @Fermionic.Fock.vacancy_idempotent
#check @Fermionic.Fock.vacancy_occupation_zero
#check @Fermionic.Fock.occupation_vacancy_zero
#check @Fermionic.Spinor.Split
#check @Fermionic.Spinor.annihilator
#check @Fermionic.Spinor.mem_annihilator
#check @Fermionic.Spinor.split_nondegenerate
#check @Fermionic.Spinor.split_finrank
#check @Fermionic.Spinor.annihilator_pairing_zero
#check @Fermionic.Spinor.annihilator_isotropic
#check @Fermionic.Spinor.annihilator_finrank_le
#check @Fermionic.Spinor.IsPure
#check @Fermionic.Spinor.pure_self_orthogonal
#check @Fermionic.Spinor.intersection_annihilates
#check @Fermionic.Spinor.null_self_annihilates
#check @Fermionic.Spinor.hyperplane_dimension
#check @Fermionic.Spinor.null_action_preserves_pure
#check @Fermionic.Spinor.create_preserves_pure
#check @Fermionic.Spinor.annihilate_preserves_pure
#check @Fermionic.Spinor.occupation_preserves_pure
#check @Fermionic.Spinor.vacancy_preserves_pure
#check @Fermionic.Spinor.historyOperator
#check @Fermionic.Spinor.null_history_preserves_pure
#check @Fermionic.Spinor.mem_vacuum_annihilator
#check @Fermionic.Spinor.vacuumAnnihilatorEquiv
#check @Fermionic.Spinor.vacuum_isPure
#check @Fermionic.FockVacuumKernel.numberOperator
#check @Fermionic.FockVacuumKernel.numberOperator_apply
#check @Fermionic.FockVacuumKernel.numberOperator_one
#check @Fermionic.FockVacuumKernel.create_swap
#check @Fermionic.FockVacuumKernel.numberOperator_create
#check @Fermionic.FockVacuumKernel.numberOperator_wedge
#check @Fermionic.FockVacuumKernel.numberOperator_basis
#check @Fermionic.FockVacuumKernel.numberOperator_coord
#check @Fermionic.FockVacuumKernel.numberOperator_zero_of_annihilated
#check @Fermionic.FockVacuumKernel.nonempty_coordinate_zero
#check @Fermionic.FockVacuumKernel.vacuum_kernel_with_basis
#check @Fermionic.FockVacuumKernel.joint_annihilation_kernel
#check @Fermionic.FockVacuumKernel.joint_annihilation_iff_vacuum
#check @Fermionic.SpinorTransport.reflection_pairing
#check @Fermionic.SpinorTransport.reflection
#check @Fermionic.SpinorTransport.reflection_apply
#check @Fermionic.SpinorTransport.reflection_involutive
#check @Fermionic.SpinorTransport.action_injective
#check @Fermionic.SpinorTransport.action_reflection
#check @Fermionic.SpinorTransport.reflection_mem_annihilator_iff
#check @Fermionic.SpinorTransport.annihilatorEquiv
#check @Fermionic.SpinorTransport.nonnull_action_preserves_pure
#check @Fermionic.SpinorTransport.nonnull_action_isPure_iff
#check @Fermionic.SpinorTransport.action_preserves_pure
#check @Fermionic.SpinorTransport.history_preserves_pure
#check @Fermionic.SpinorTransport.invertible_history_preserves_pure
#check @Fermionic.SpinorTransport.invertible_history_vacuum_isPure
#check @Fermionic.SpinorTransport.unitAction
#check @Fermionic.SpinorTransport.unitAction_one
#check @Fermionic.SpinorTransport.unitAction_mul
#check @Fermionic.SpinorTransport.unitAction_inv_apply
#check @Fermionic.SpinorTransport.lipschitz_action_isPure_iff
#check @Fermionic.SpinorTransport.spin_action_preserves_pure
#check @Fermionic.SpinorTransport.spin_vacuum_isPure
#check @Fermionic.SpinorTransport.annihilator_smul
#check @Fermionic.SpinorTransport.smul_isPure_iff
#check @Fermionic.SpinorTransport.realInnerProduct
#check @Fermionic.SpinorTransport.majoranaQuadratic
#check @Fermionic.SpinorTransport.majoranaQuadratic_apply
#check @Fermionic.SpinorTransport.majoranaQuadratic_pos
#check @Fermionic.SpinorTransport.majoranaEmbedding
#check @Fermionic.SpinorTransport.majoranaEmbedding_quadratic
#check @Fermionic.SpinorTransport.majoranaCliffordMap
#check @Fermionic.SpinorTransport.majoranaCliffordMap_generator
#check @Fermionic.SpinorTransport.majorana_units_mem_lipschitz
#check @Fermionic.SpinorTransport.euclideanSpinAction
#check @Fermionic.SpinorTransport.euclideanSpinRepresentation
#check @Fermionic.SpinorTransport.majorana_fock_generator
#check @Fermionic.SpinorTransport.euclideanSpinAction_preserves_pure
#check @Fermionic.SpinorTransport.euclideanSpin_vacuum_isPure
#check @Fermionic.SpinorTransport.euclideanSpin_vacuum_ray_isPure
#check @Fermionic.PureDecomposition.wedge_isPure
#check @Fermionic.PureDecomposition.occupancy_isPure
#check @Fermionic.PureDecomposition.annihilator_smul
#check @Fermionic.PureDecomposition.smul_isPure
#check @Fermionic.PureDecomposition.HasPureDecomposition
#check @Fermionic.PureDecomposition.decomposition_zero_iff
#check @Fermionic.PureDecomposition.decomposition_one_iff
#check @Fermionic.PureDecomposition.ModeSpace
#check @Fermionic.PureDecomposition.TargetSpace
#check @Fermionic.PureDecomposition.occupancyBasis
#check @Fermionic.PureDecomposition.targetSupports
#check @Fermionic.PureDecomposition.target
#check @Fermionic.PureDecomposition.target_four_pure
#check @Fermionic.PureDecomposition.target_vacuum_coefficient
#check @Fermionic.PureDecomposition.target_ne_zero
#check @Fermionic.PureDecomposition.targetPureRank
#check @Fermionic.PureDecomposition.targetPureRank_spec
#check @Fermionic.PureDecomposition.targetPureRank_le_four
#check @Fermionic.PureDecomposition.targetPureRank_pos
#check @Fermionic.PhysicalGaussian.IsGaussian
#check @Fermionic.PhysicalGaussian.HasDecomposition
#check @Fermionic.PhysicalGaussian.gaussian_isPure
#check @Fermionic.PhysicalGaussian.decomposition_implies_pure
#check @Fermionic.PhysicalGaussian.vacuum_isGaussian
#check @Fermionic.PhysicalGaussian.gaussian_smul
#check @Fermionic.PhysicalOccupancy.majorana_square_one
#check @Fermionic.PhysicalOccupancy.majoranaUnit
#check @Fermionic.PhysicalOccupancy.majoranaUnit_mem_lipschitz
#check @Fermionic.PhysicalOccupancy.majorana_pair_mem_spin
#check @Fermionic.PhysicalOccupancy.majoranaPair
#check @Fermionic.PhysicalOccupancy.majoranaPair_action
#check @Fermionic.PhysicalOccupancy.annihilate_wedge_eq_zero
#check @Fermionic.PhysicalOccupancy.majorana_action_wedge
#check @Fermionic.PhysicalOccupancy.even_orthonormal_wedge_orbit
#check @Fermionic.PhysicalOccupancy.even_orthonormal_wedge_isGaussian
#check @Fermionic.PhysicalOccupancy.occupancy_isGaussian
#check @Fermionic.PhysicalOccupancy.target_support_isGaussian
#check @Fermionic.PhysicalOccupancy.target_has_gaussian_decomposition
#check @Fermionic.PhysicalGaussianRank.target_decomposable
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank_spec
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank_le_of_decomposition
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank_min
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank_le_four
#check @Fermionic.PhysicalGaussianRank.decomposition_zero_iff
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank_pos
#check @Fermionic.PhysicalGaussianRank.one_le_targetGaussianRank
#check @Fermionic.PhysicalGaussianRank.targetPureRank_le_targetGaussianRank
#check @Fermionic.PhysicalGaussianRank.targetGaussianRank_bounds
#check @Fermionic.GaussianScaling.decomposition_smul
#check @Fermionic.GaussianScaling.decomposition_smul_iff
#check @Fermionic.GaussianScaling.normalizedTarget
#check @Fermionic.GaussianScaling.normalizedTarget_decomposition_iff
#check @Fermionic.GaussianScaling.target_eq_two_smul_normalizedTarget
#check @Fermionic.GaussianScaling.normalizedTarget_minimum
#check @Fermionic.FockParity.create_even_to_odd
#check @Fermionic.FockParity.create_odd_to_even
#check @Fermionic.FockParity.annihilate_even_to_odd
#check @Fermionic.FockParity.annihilate_odd_to_even
#check @Fermionic.FockParity.action_even_to_odd
#check @Fermionic.FockParity.action_odd_to_even
#check @Fermionic.FockParity.realInnerProduct
#check @Fermionic.FockParity.real_even_preserves_even
#check @Fermionic.FockParity.euclideanSpinAction_preserves_even
#check @Fermionic.FockParity.euclideanSpin_vacuum_even
#check @Fermionic.FockParity.euclideanSpin_vacuum_smul_even
#check @Fermionic.FockParity.gaussian_even
#check @Fermionic.PureVacuumChart.vacuumCoefficient
#check @Fermionic.PureVacuumChart.vacuumCoefficient_create
#check @Fermionic.PureVacuumChart.vacuumCoefficient_annihilate_create
#check @Fermionic.PureVacuumChart.creator_eq_zero_of_vacuum_ne_zero
#check @Fermionic.PureVacuumChart.annihilatorProjection
#check @Fermionic.PureVacuumChart.annihilatorProjection_injective
#check @Fermionic.PureVacuumChart.annihilatorProjection_surjective
#check @Fermionic.PureVacuumChart.annihilatorProjectionEquiv
#check @Fermionic.PureVacuumChart.graphDirection
#check @Fermionic.PureVacuumChart.graphDirection_mem_annihilator
#check @Fermionic.PureVacuumChart.graphDirection_annihilates
#check @Fermionic.PureVacuumChart.graphDirection_skew
#check @Fermionic.PureVacuumChart.graphDirection_two_contractions
#check @Fermionic.PureVacuumRigidity.graphDirection_eq_zero
#check @Fermionic.PureVacuumRigidity.pure_zero_two_contractions_is_vacuum
#check @Fermionic.PureVacuumRigidity.vacuumCoefficient_wedge_zero
#check @Fermionic.PureVacuumRigidity.vacuumCoefficient_one_contraction_wedge
#check @Fermionic.PureVacuumRigidity.vacuumCoefficient_two_contractions_wedge
#check @Fermionic.PureVacuumRigidity.vacuumCoefficient_two_contractions_basis
#check @Fermionic.PureVacuumRigidity.vacuumCoefficient_basis
#check @Fermionic.PureVacuumRigidity.target_vacuumCoefficient
#check @Fermionic.PureVacuumRigidity.target_two_contractions_zero
#check @Fermionic.PureVacuumRigidity.target_first_block_coefficient
#check @Fermionic.PureVacuumRigidity.target_ne_vacuum
#check @Fermionic.PureVacuumRigidity.target_not_pure
#check @Fermionic.PureVacuumRigidity.targetGaussianRank_ne_one
#check @Fermionic.PureVacuumRigidity.two_le_targetGaussianRank
set_option pp.universes false
#print axioms Fermionic.Fock.Space
#print axioms Fermionic.Fock.create
#print axioms Fermionic.Fock.annihilate
#print axioms Fermionic.Fock.create_apply
#print axioms Fermionic.Fock.annihilate_apply
#print axioms Fermionic.Fock.create_square
#print axioms Fermionic.Fock.annihilate_square
#print axioms Fermionic.Fock.mixed_car
#print axioms Fermionic.Fock.action
#print axioms Fermionic.Fock.action_apply
#print axioms Fermionic.Fock.action_square
#print axioms Fermionic.Fock.action_square_end
#print axioms Fermionic.Fock.action_car
#print axioms Fermionic.Fock.representation
#print axioms Fermionic.Fock.representation_generator
#print axioms Fermionic.Fock.occupation
#print axioms Fermionic.Fock.vacancy
#print axioms Fermionic.Fock.occupation_vacancy
#print axioms Fermionic.Fock.occupation_idempotent
#print axioms Fermionic.Fock.vacancy_idempotent
#print axioms Fermionic.Fock.vacancy_occupation_zero
#print axioms Fermionic.Fock.occupation_vacancy_zero
#print axioms Fermionic.Spinor.Split
#print axioms Fermionic.Spinor.annihilator
#print axioms Fermionic.Spinor.mem_annihilator
#print axioms Fermionic.Spinor.split_nondegenerate
#print axioms Fermionic.Spinor.split_finrank
#print axioms Fermionic.Spinor.annihilator_pairing_zero
#print axioms Fermionic.Spinor.annihilator_isotropic
#print axioms Fermionic.Spinor.annihilator_finrank_le
#print axioms Fermionic.Spinor.IsPure
#print axioms Fermionic.Spinor.pure_self_orthogonal
#print axioms Fermionic.Spinor.intersection_annihilates
#print axioms Fermionic.Spinor.null_self_annihilates
#print axioms Fermionic.Spinor.hyperplane_dimension
#print axioms Fermionic.Spinor.null_action_preserves_pure
#print axioms Fermionic.Spinor.create_preserves_pure
#print axioms Fermionic.Spinor.annihilate_preserves_pure
#print axioms Fermionic.Spinor.occupation_preserves_pure
#print axioms Fermionic.Spinor.vacancy_preserves_pure
#print axioms Fermionic.Spinor.historyOperator
#print axioms Fermionic.Spinor.null_history_preserves_pure
#print axioms Fermionic.Spinor.mem_vacuum_annihilator
#print axioms Fermionic.Spinor.vacuumAnnihilatorEquiv
#print axioms Fermionic.Spinor.vacuum_isPure
#print axioms Fermionic.FockVacuumKernel.numberOperator
#print axioms Fermionic.FockVacuumKernel.numberOperator_apply
#print axioms Fermionic.FockVacuumKernel.numberOperator_one
#print axioms Fermionic.FockVacuumKernel.create_swap
#print axioms Fermionic.FockVacuumKernel.numberOperator_create
#print axioms Fermionic.FockVacuumKernel.numberOperator_wedge
#print axioms Fermionic.FockVacuumKernel.numberOperator_basis
#print axioms Fermionic.FockVacuumKernel.numberOperator_coord
#print axioms Fermionic.FockVacuumKernel.numberOperator_zero_of_annihilated
#print axioms Fermionic.FockVacuumKernel.nonempty_coordinate_zero
#print axioms Fermionic.FockVacuumKernel.vacuum_kernel_with_basis
#print axioms Fermionic.FockVacuumKernel.joint_annihilation_kernel
#print axioms Fermionic.FockVacuumKernel.joint_annihilation_iff_vacuum
#print axioms Fermionic.SpinorTransport.reflection_pairing
#print axioms Fermionic.SpinorTransport.reflection
#print axioms Fermionic.SpinorTransport.reflection_apply
#print axioms Fermionic.SpinorTransport.reflection_involutive
#print axioms Fermionic.SpinorTransport.action_injective
#print axioms Fermionic.SpinorTransport.action_reflection
#print axioms Fermionic.SpinorTransport.reflection_mem_annihilator_iff
#print axioms Fermionic.SpinorTransport.annihilatorEquiv
#print axioms Fermionic.SpinorTransport.nonnull_action_preserves_pure
#print axioms Fermionic.SpinorTransport.nonnull_action_isPure_iff
#print axioms Fermionic.SpinorTransport.action_preserves_pure
#print axioms Fermionic.SpinorTransport.history_preserves_pure
#print axioms Fermionic.SpinorTransport.invertible_history_preserves_pure
#print axioms Fermionic.SpinorTransport.invertible_history_vacuum_isPure
#print axioms Fermionic.SpinorTransport.unitAction
#print axioms Fermionic.SpinorTransport.unitAction_one
#print axioms Fermionic.SpinorTransport.unitAction_mul
#print axioms Fermionic.SpinorTransport.unitAction_inv_apply
#print axioms Fermionic.SpinorTransport.lipschitz_action_isPure_iff
#print axioms Fermionic.SpinorTransport.spin_action_preserves_pure
#print axioms Fermionic.SpinorTransport.spin_vacuum_isPure
#print axioms Fermionic.SpinorTransport.annihilator_smul
#print axioms Fermionic.SpinorTransport.smul_isPure_iff
#print axioms Fermionic.SpinorTransport.realInnerProduct
#print axioms Fermionic.SpinorTransport.majoranaQuadratic
#print axioms Fermionic.SpinorTransport.majoranaQuadratic_apply
#print axioms Fermionic.SpinorTransport.majoranaQuadratic_pos
#print axioms Fermionic.SpinorTransport.majoranaEmbedding
#print axioms Fermionic.SpinorTransport.majoranaEmbedding_quadratic
#print axioms Fermionic.SpinorTransport.majoranaCliffordMap
#print axioms Fermionic.SpinorTransport.majoranaCliffordMap_generator
#print axioms Fermionic.SpinorTransport.majorana_units_mem_lipschitz
#print axioms Fermionic.SpinorTransport.euclideanSpinAction
#print axioms Fermionic.SpinorTransport.euclideanSpinRepresentation
#print axioms Fermionic.SpinorTransport.majorana_fock_generator
#print axioms Fermionic.SpinorTransport.euclideanSpinAction_preserves_pure
#print axioms Fermionic.SpinorTransport.euclideanSpin_vacuum_isPure
#print axioms Fermionic.SpinorTransport.euclideanSpin_vacuum_ray_isPure
#print axioms Fermionic.PureDecomposition.wedge_isPure
#print axioms Fermionic.PureDecomposition.occupancy_isPure
#print axioms Fermionic.PureDecomposition.annihilator_smul
#print axioms Fermionic.PureDecomposition.smul_isPure
#print axioms Fermionic.PureDecomposition.HasPureDecomposition
#print axioms Fermionic.PureDecomposition.decomposition_zero_iff
#print axioms Fermionic.PureDecomposition.decomposition_one_iff
#print axioms Fermionic.PureDecomposition.ModeSpace
#print axioms Fermionic.PureDecomposition.TargetSpace
#print axioms Fermionic.PureDecomposition.occupancyBasis
#print axioms Fermionic.PureDecomposition.targetSupports
#print axioms Fermionic.PureDecomposition.target
#print axioms Fermionic.PureDecomposition.target_four_pure
#print axioms Fermionic.PureDecomposition.target_vacuum_coefficient
#print axioms Fermionic.PureDecomposition.target_ne_zero
#print axioms Fermionic.PureDecomposition.targetPureRank
#print axioms Fermionic.PureDecomposition.targetPureRank_spec
#print axioms Fermionic.PureDecomposition.targetPureRank_le_four
#print axioms Fermionic.PureDecomposition.targetPureRank_pos
#print axioms Fermionic.PhysicalGaussian.IsGaussian
#print axioms Fermionic.PhysicalGaussian.HasDecomposition
#print axioms Fermionic.PhysicalGaussian.gaussian_isPure
#print axioms Fermionic.PhysicalGaussian.decomposition_implies_pure
#print axioms Fermionic.PhysicalGaussian.vacuum_isGaussian
#print axioms Fermionic.PhysicalGaussian.gaussian_smul
#print axioms Fermionic.PhysicalOccupancy.majorana_square_one
#print axioms Fermionic.PhysicalOccupancy.majoranaUnit
#print axioms Fermionic.PhysicalOccupancy.majoranaUnit_mem_lipschitz
#print axioms Fermionic.PhysicalOccupancy.majorana_pair_mem_spin
#print axioms Fermionic.PhysicalOccupancy.majoranaPair
#print axioms Fermionic.PhysicalOccupancy.majoranaPair_action
#print axioms Fermionic.PhysicalOccupancy.annihilate_wedge_eq_zero
#print axioms Fermionic.PhysicalOccupancy.majorana_action_wedge
#print axioms Fermionic.PhysicalOccupancy.even_orthonormal_wedge_orbit
#print axioms Fermionic.PhysicalOccupancy.even_orthonormal_wedge_isGaussian
#print axioms Fermionic.PhysicalOccupancy.occupancy_isGaussian
#print axioms Fermionic.PhysicalOccupancy.target_support_isGaussian
#print axioms Fermionic.PhysicalOccupancy.target_has_gaussian_decomposition
#print axioms Fermionic.PhysicalGaussianRank.target_decomposable
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank_spec
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank_le_of_decomposition
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank_min
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank_le_four
#print axioms Fermionic.PhysicalGaussianRank.decomposition_zero_iff
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank_pos
#print axioms Fermionic.PhysicalGaussianRank.one_le_targetGaussianRank
#print axioms Fermionic.PhysicalGaussianRank.targetPureRank_le_targetGaussianRank
#print axioms Fermionic.PhysicalGaussianRank.targetGaussianRank_bounds
#print axioms Fermionic.GaussianScaling.decomposition_smul
#print axioms Fermionic.GaussianScaling.decomposition_smul_iff
#print axioms Fermionic.GaussianScaling.normalizedTarget
#print axioms Fermionic.GaussianScaling.normalizedTarget_decomposition_iff
#print axioms Fermionic.GaussianScaling.target_eq_two_smul_normalizedTarget
#print axioms Fermionic.GaussianScaling.normalizedTarget_minimum
#print axioms Fermionic.FockParity.create_even_to_odd
#print axioms Fermionic.FockParity.create_odd_to_even
#print axioms Fermionic.FockParity.annihilate_even_to_odd
#print axioms Fermionic.FockParity.annihilate_odd_to_even
#print axioms Fermionic.FockParity.action_even_to_odd
#print axioms Fermionic.FockParity.action_odd_to_even
#print axioms Fermionic.FockParity.realInnerProduct
#print axioms Fermionic.FockParity.real_even_preserves_even
#print axioms Fermionic.FockParity.euclideanSpinAction_preserves_even
#print axioms Fermionic.FockParity.euclideanSpin_vacuum_even
#print axioms Fermionic.FockParity.euclideanSpin_vacuum_smul_even
#print axioms Fermionic.FockParity.gaussian_even
#print axioms Fermionic.PureVacuumChart.vacuumCoefficient
#print axioms Fermionic.PureVacuumChart.vacuumCoefficient_create
#print axioms Fermionic.PureVacuumChart.vacuumCoefficient_annihilate_create
#print axioms Fermionic.PureVacuumChart.creator_eq_zero_of_vacuum_ne_zero
#print axioms Fermionic.PureVacuumChart.annihilatorProjection
#print axioms Fermionic.PureVacuumChart.annihilatorProjection_injective
#print axioms Fermionic.PureVacuumChart.annihilatorProjection_surjective
#print axioms Fermionic.PureVacuumChart.annihilatorProjectionEquiv
#print axioms Fermionic.PureVacuumChart.graphDirection
#print axioms Fermionic.PureVacuumChart.graphDirection_mem_annihilator
#print axioms Fermionic.PureVacuumChart.graphDirection_annihilates
#print axioms Fermionic.PureVacuumChart.graphDirection_skew
#print axioms Fermionic.PureVacuumChart.graphDirection_two_contractions
#print axioms Fermionic.PureVacuumRigidity.graphDirection_eq_zero
#print axioms Fermionic.PureVacuumRigidity.pure_zero_two_contractions_is_vacuum
#print axioms Fermionic.PureVacuumRigidity.vacuumCoefficient_wedge_zero
#print axioms Fermionic.PureVacuumRigidity.vacuumCoefficient_one_contraction_wedge
#print axioms Fermionic.PureVacuumRigidity.vacuumCoefficient_two_contractions_wedge
#print axioms Fermionic.PureVacuumRigidity.vacuumCoefficient_two_contractions_basis
#print axioms Fermionic.PureVacuumRigidity.vacuumCoefficient_basis
#print axioms Fermionic.PureVacuumRigidity.target_vacuumCoefficient
#print axioms Fermionic.PureVacuumRigidity.target_two_contractions_zero
#print axioms Fermionic.PureVacuumRigidity.target_first_block_coefficient
#print axioms Fermionic.PureVacuumRigidity.target_ne_vacuum
#print axioms Fermionic.PureVacuumRigidity.target_not_pure
#print axioms Fermionic.PureVacuumRigidity.targetGaussianRank_ne_one
#print axioms Fermionic.PureVacuumRigidity.two_le_targetGaussianRank
