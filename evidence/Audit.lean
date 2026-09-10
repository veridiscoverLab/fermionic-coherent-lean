import Fermionic
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
#check @Fermionic.CommonJensen.pointwise_jensen
#check @Fermionic.CommonJensen.integral_weighted_sum
#check @Fermionic.CommonJensen.integral_jensen
#check @Fermionic.CommonJensen.ae_eq_mixture_of_integral_eq
#check @Fermionic.CommonJensen.ae_eq_of_integral_eq
#check @Fermionic.CommonJensen.integral_eq_of_map_eq
#check @Fermionic.CommonJensen.common_law_jensen
#check @Fermionic.CommonJensen.common_law_eq_implies_ae_eq
#check @Fermionic.CommonJensen.integrable_map_of_continuousOn_unitInterval
#check @Fermionic.CommonJensen.integrable_comp_of_continuousOn_unitInterval
#check @Fermionic.CommonJensen.mixture_aemeasurable_and_range
#check @Fermionic.CommonJensen.common_law_jensen_continuous
#check @Fermionic.CommonJensen.common_law_eq_implies_ae_eq_continuous
#check @Fermionic.CommonJensen.mul_mem_unitInterval
#check @Fermionic.CommonJensen.scale_mixture_convex
#check @Fermionic.CommonJensen.scale_mixture_strictConvex
#check @Fermionic.CommonJensen.integrable_scaled_of_continuousOn
#check @Fermionic.CommonJensen.scale_mixture_continuousOn
#check @Fermionic.CommonJensen.scale_mixture_convex_continuous
#check @Fermionic.CommonJensen.scale_mixture_strictConvex_continuous
#check @Fermionic.DensityRigidity.column_eq_zero_of_diag_eq_zero
#check @Fermionic.DensityRigidity.row_eq_zero_of_diag_eq_zero
#check @Fermionic.DensityRigidity.row_and_column_eq_zero_of_diag_eq_zero
#check @Fermionic.DensityRigidity.basisProjector
#check @Fermionic.DensityRigidity.basisProjector_apply
#check @Fermionic.DensityRigidity.eq_basisProjector_of_trace_eq_one
#check @Fermionic.DensityRigidity.eq_zero_of_trace_eq_zero
#check @Fermionic.FourMode.Space
#check @Fermionic.FourMode.chevalleyQ
#check @Fermionic.FourMode.chevalleyB
#check @Fermionic.FourMode.chevalleyQ_zero
#check @Fermionic.FourMode.chevalleyB_self
#check @Fermionic.FourMode.chevalleyQ_add
#check @Fermionic.FourMode.chevalleyQ_smul
#check @Fermionic.FourMode.axis
#check @Fermionic.FourMode.axisCoefficient
#check @Fermionic.FourMode.axis_ne_zero
#check @Fermionic.FourMode.chevalleyQ_axis
#check @Fermionic.FourMode.chevalleyQ_sub_smul_axis
#check @Fermionic.FourMode.exists_axisCoefficient_ne_zero
#check @Fermionic.FourMode.nonisotropic_decomposition
#check @Fermionic.FourMode.IsQuadric
#check @Fermionic.FourMode.HasDecomposition
#check @Fermionic.FourMode.hasDecomposition_zero_iff
#check @Fermionic.FourMode.hasDecomposition_one_iff
#check @Fermionic.FourMode.hasDecomposition_two
#check @Fermionic.FourMode.decomposition_exists
#check @Fermionic.FourMode.exactRank
#check @Fermionic.FourMode.exactRank_spec
#check @Fermionic.FourMode.exactRank_le
#check @Fermionic.FourMode.exactRank_zero_iff
#check @Fermionic.FourMode.exactRank_eq_one
#check @Fermionic.FourMode.exactRank_one_iff
#check @Fermionic.FourMode.exactRank_eq_two
#check @Fermionic.FourMode.exactRank_two_iff
#check @Fermionic.FourMode.exactRank_nonzero
#check @Fermionic.FourMode.magic
#check @Fermionic.FourMode.chevalleyQ_magic
#check @Fermionic.FourMode.exactRank_magic
#check @Fermionic.ExteriorUnitary.Index
#check @Fermionic.ExteriorUnitary.AlgebraicSector
#check @Fermionic.ExteriorUnitary.Sector
#check @Fermionic.ExteriorUnitary.basis
#check @Fermionic.ExteriorUnitary.coordinates
#check @Fermionic.ExteriorUnitary.coordinates_basis
#check @Fermionic.ExteriorUnitary.exteriorMatrix
#check @Fermionic.ExteriorUnitary.coordinates_intertwine
#check @Fermionic.ExteriorUnitary.exteriorMatrix_mul
#check @Fermionic.ExteriorUnitary.exteriorMatrix_one
#check @Fermionic.ExteriorUnitary.enumerate
#check @Fermionic.ExteriorUnitary.diagonal_on_basis
#check @Fermionic.ExteriorUnitary.exteriorMatrix_diagonal
#check @Fermionic.ExteriorUnitary.exteriorMatrix_entry
#check @Fermionic.ExteriorUnitary.exteriorMatrix_conjTranspose
#check @Fermionic.ExteriorUnitary.exteriorMatrix_mem_unitary
#check @Fermionic.ExteriorUnitary.representation
#check @Fermionic.ExteriorUnitary.continuous_exteriorMatrix
#check @Fermionic.ExteriorUnitary.continuous_representation
#check @Fermionic.HaarConditioning.probabilityHaar
#check @Fermionic.HaarConditioning.probabilityHaar_isHaar
#check @Fermionic.HaarConditioning.probabilityHaar_isProbability
#check @Fermionic.HaarConditioning.probabilityHaar_isRightInvariant
#check @Fermionic.HaarConditioning.map_readout_mul_left
#check @Fermionic.HaarConditioning.map_readout_mul_right
#check @Fermionic.HaarConditioning.map_readout_positive_mass
#check @Fermionic.HaarConditioning.readout_eq_of_ae_eq
#check @Fermionic.HaarConditioning.integral_double_haar
#check @Fermionic.HaarConditioning.integral_eq_double_haar
#check @Fermionic.HaarConditioning.isCompact_unitaryGroup
#check @Fermionic.HaarConditioning.unitaryGroup_compactSpace
#check @Fermionic.HaarConditioning.unitaryGroup_measurableSpace
#check @Fermionic.HaarConditioning.unitaryGroup_borelSpace
#check @Fermionic.HaarConditioning.unitaryHaar
#check @Fermionic.HaarConditioning.unitaryHaar_isProbability
#check @Fermionic.HaarConditioning.unitaryHaar_isHaar
#check @Fermionic.HaarConditioning.unitaryHaar_isRightInvariant
#check @Fermionic.HaarConditioning.fixFirstHom
#check @Fermionic.HaarConditioning.fixFirstHom_continuous
#check @Fermionic.HaarConditioning.fixFirstHom_lower_apply
#check @Fermionic.HaarConditioning.fixFirstHom_first_apply
#check @Fermionic.HaarConditioning.fixFirstHom_first_row
#check @Fermionic.HaarConditioning.fixFirstHom_first_column
#check @Fermionic.HaarConditioning.fixFirstHom_injective
#check @Fermionic.HaarConditioning.unitary_integral_eq_double
#check @Fermionic.HaarConditioning.unitaryReindex
#check @Fermionic.HaarConditioning.unitaryReindex_apply
#check @Fermionic.HaarConditioning.unitaryReindex_continuous
#check @Fermionic.HaarConditioning.unitaryReindex_measurePreserving
#check @Fermionic.HaarConditioning.firstFinEquiv
#check @Fermionic.HaarConditioning.firstFinEquiv_zero
#check @Fermionic.HaarConditioning.firstFinEquiv_succ
#check @Fermionic.HaarConditioning.firstFinEquiv_symm_zero
#check @Fermionic.HaarConditioning.firstFinEquiv_symm_succ
#check @Fermionic.HaarConditioning.fixFirstFinHom
#check @Fermionic.HaarConditioning.fixFirstFinHom_zero_zero
#check @Fermionic.HaarConditioning.fixFirstFinHom_zero_succ
#check @Fermionic.HaarConditioning.fixFirstFinHom_succ_zero
#check @Fermionic.HaarConditioning.fixFirstFinHom_succ_succ
#check @Fermionic.HaarConditioning.fixFirstFinHom_continuous
#check @Fermionic.HaarConditioning.unitary_fin_integral_eq_double
#check @Fermionic.ExteriorDifferential.differentiable_exteriorMatrix
#check @Fermionic.ExteriorDifferential.infinitesimal
#check @Fermionic.ExteriorDifferential.hasFDerivAt_identity
#check @Fermionic.ExteriorDifferential.sandwich
#check @Fermionic.ExteriorDifferential.sandwich_apply
#check @Fermionic.ExteriorDifferential.infinitesimal_conjTranspose
#check @Fermionic.ExteriorDifferential.infinitesimal_unitary_conjugation
#check @Fermionic.ExteriorDifferential.infinitesimal_diagonal
#check @Fermionic.ExteriorDifferential.occupation
#check @Fermionic.ExteriorDifferential.infinitesimal_single_diag
#check @Fermionic.ExteriorDifferential.oneParticle
#check @Fermionic.ExteriorDifferential.oneParticle_isHermitian
#check @Fermionic.ExteriorDifferential.trace_infinitesimal
#check @Fermionic.ExteriorDifferential.oneParticle_diag
#check @Fermionic.ExteriorDifferential.oneParticle_unitary_conjugation
#check @Fermionic.OccupationMixture.eigenRotation
#check @Fermionic.OccupationMixture.eigenDensity
#check @Fermionic.OccupationMixture.eigenDensity_posSemidef
#check @Fermionic.OccupationMixture.eigenDensity_trace
#check @Fermionic.OccupationMixture.eigenDensity_oneParticle_diagonal
#check @Fermionic.OccupationMixture.probability
#check @Fermionic.OccupationMixture.probability_nonneg
#check @Fermionic.OccupationMixture.probability_sum
#check @Fermionic.OccupationMixture.probability_cast
#check @Fermionic.OccupationMixture.occupancyProjection
#check @Fermionic.OccupationMixture.common_diagonal_mixture
#check @Fermionic.OccupationMixture.common_projection_mixture
#check @Fermionic.OccupationMixture.oneParticleReadout
#check @Fermionic.OccupationMixture.common_readout_mixture
#check @Fermionic.ConditionalSector.insertFirst
#check @Fermionic.ConditionalSector.mem_insertFirst_zero
#check @Fermionic.ConditionalSector.mem_insertFirst_succ
#check @Fermionic.ConditionalSector.insertFirst_injective
#check @Fermionic.ConditionalSector.insertFirst_surjective_occupied
#check @Fermionic.ConditionalSector.insertFirst_range
#check @Fermionic.ConditionalSector.sum_insertFirst
#check @Fermionic.ConditionalSector.enumerate_insertFirst
#check @Fermionic.ConditionalSector.enumerate_insertFirst_zero
#check @Fermionic.ConditionalSector.enumerate_insertFirst_succ
#check @Fermionic.ConditionalSector.basisInclusion
#check @Fermionic.ConditionalSector.basisInclusion_compress_apply
#check @Fermionic.ConditionalSector.basisInclusion_compress
#check @Fermionic.ConditionalSector.basisInclusion_isometry
#check @Fermionic.ConditionalSector.basisInclusion_compress_posSemidef
#check @Fermionic.ConditionalSector.basisInclusion_compress_trace_le_one
#check @Fermionic.ConditionalSector.intertwine_of_unitary_compression
#check @Fermionic.ConditionalSector.quadratic
#check @Fermionic.ConditionalSector.quadratic_compression
#check @Fermionic.ConditionalSector.quadratic_smul
#check @Fermionic.ConditionalSector.weight
#check @Fermionic.ConditionalSector.weight_nonneg
#check @Fermionic.ConditionalSector.trace_eq_weight
#check @Fermionic.ConditionalSector.compression_zero_of_weight_zero
#check @Fermionic.ConditionalSector.normalized
#check @Fermionic.ConditionalSector.normalized_posSemidef
#check @Fermionic.ConditionalSector.normalized_trace_eq_one
#check @Fermionic.ConditionalSector.weight_smul_normalized
#check @Fermionic.ConditionalSector.quadratic_eq_weight_mul_normalized
#check @Fermionic.ConditionalSector.creation
#check @Fermionic.ConditionalSector.creation_isometry
#check @Fermionic.ConditionalSector.creation_conjTranspose_mulVec
#check @Fermionic.ConditionalSector.creation_trace_eq_oneParticle
#check @Fermionic.ConditionalSector.exteriorMatrix_fixFirst_compress
#check @Fermionic.ConditionalSector.creation_intertwine
#check @Fermionic.ConditionalSector.rotated
#check @Fermionic.ConditionalSector.rotated_posSemidef
#check @Fermionic.ConditionalSector.rotated_trace
#check @Fermionic.ConditionalSector.conditionalMatrix
#check @Fermionic.ConditionalSector.conditionalMatrix_posSemidef
#check @Fermionic.ConditionalSector.conditional_weight_mem_unitInterval
#check @Fermionic.ConditionalSector.conditional_weight_eq_oneParticleReadout
#check @Fermionic.ConditionalSector.conditional_readout
#check @Fermionic.ConditionalSector.conditional_readout_zero
#check @Fermionic.ConditionalSector.conditional_readout_normalized
#check @Fermionic.OccupancyOrbit.coordinateProjection
#check @Fermionic.OccupancyOrbit.permutationUnitary
#check @Fermionic.OccupancyOrbit.occupancyPermutation
#check @Fermionic.OccupancyOrbit.occupancyPermutation_mem
#check @Fermionic.OccupancyOrbit.permutation_conjugates_projection
#check @Fermionic.OccupancyOrbit.occupancy_same_orbit
#check @Fermionic.OccupancyOrbit.projectionReadout
#check @Fermionic.OccupancyOrbit.projectionReadout_eq_sum
#check @Fermionic.OccupancyOrbit.projectionReadout_mem_unitInterval
#check @Fermionic.OccupancyOrbit.continuous_projectionReadout
#check @Fermionic.OccupancyOrbit.projectionReadout_conjugate
#check @Fermionic.OccupancyOrbit.occupancy_readout_same_law
#check @Fermionic.OccupancyOrbit.projectionReadout_permutation
#check @Fermionic.OccupancyOrbit.projectionReadout_injective
#check @Fermionic.OccupationConvexOrder.component
#check @Fermionic.OccupationConvexOrder.component_continuous
#check @Fermionic.OccupationConvexOrder.component_range
#check @Fermionic.OccupationConvexOrder.component_common_law
#check @Fermionic.OccupationConvexOrder.actual_readout_eq_common_mixture
#check @Fermionic.OccupationConvexOrder.actual_readout_range
#check @Fermionic.OccupationConvexOrder.actual_readout_continuous
#check @Fermionic.OccupationConvexOrder.occupation_convex_order
#check @Fermionic.OccupationConvexOrder.IsSlaterDensity
#check @Fermionic.OccupationConvexOrder.component_injective
#check @Fermionic.OccupationConvexOrder.eigenDensity_basis_implies_slater
#check @Fermionic.OccupationConvexOrder.occupation_equality_implies_slater
#check @Fermionic.SlaterOrbit.orderedPermutation
#check @Fermionic.SlaterOrbit.orderedPermutation_enumerate
#check @Fermionic.SlaterOrbit.permutation_basis_vector
#check @Fermionic.SlaterOrbit.ordered_permutation_wedge
#check @Fermionic.SlaterOrbit.ordered_permutation_column
#check @Fermionic.SlaterOrbit.basis_projector_same_orbit
#check @Fermionic.SlaterOneParticle.signUnitary
#check @Fermionic.SlaterOneParticle.diagonal_unitary_preserves_basis
#check @Fermionic.SlaterOneParticle.sign_preserves_basis
#check @Fermionic.SlaterOneParticle.oneParticle_basisProjector
#check @Fermionic.SlaterClosure.basisUnitary
#check @Fermionic.SlaterClosure.basisUnitary_apply
#check @Fermionic.SlaterClosure.exists_unitary_extension
#check @Fermionic.SlaterClosure.exists_unitary_first_column
#check @Fermionic.SlaterClosure.exists_unitary_row_alignment
#check @Fermionic.SlaterClosure.exists_unitary_frame_extension
#check @Fermionic.SlaterClosure.frameVector
#check @Fermionic.SlaterClosure.frameVector_unitary_columns
#check @Fermionic.SlaterClosure.unitary_columns_isometry
#check @Fermionic.SlaterClosure.frameVector_mul
#check @Fermionic.SlaterClosure.frameVector_is_unitary_column
#check @Fermionic.SlaterClosure.creation_contract_frame
#check @Fermionic.SlaterClosure.contraction_unitary_column
#check @Fermionic.SlaterClosure.pureMatrix
#check @Fermionic.SlaterClosure.pureMatrix_compression
#check @Fermionic.SlaterClosure.pureMatrix_smul
#check @Fermionic.SlaterClosure.pureMatrix_unitary_column
#check @Fermionic.SlaterClosure.unitary_column_trace_one
#check @Fermionic.SlaterClosure.normalized_pos_smul
#check @Fermionic.SlaterClosure.normalized_compression_isSlater
#check @Fermionic.SlaterClosure.rotated_isSlater
#check @Fermionic.SlaterClosure.conditional_isSlater
#check @Fermionic.ExteriorHusimi.readout
#check @Fermionic.ExteriorHusimi.readout_continuous
#check @Fermionic.ExteriorHusimi.readout_mem_unitInterval
#check @Fermionic.ExteriorHusimi.continuous_test_readout
#check @Fermionic.ExteriorHusimi.quadratic_basis
#check @Fermionic.ExteriorHusimi.readout_eq_quadratic
#check @Fermionic.ExteriorHusimi.creation_basis
#check @Fermionic.ExteriorHusimi.basisProjector_posSemidef
#check @Fermionic.ExteriorHusimi.basisProjector_trace
#check @Fermionic.ExteriorHusimi.readout_basisProjector_one
#check @Fermionic.ExteriorHusimi.coherent_readout_positive_mass
#check @Fermionic.ExteriorHusimi.orderedPermutation_mul_basis
#check @Fermionic.ExteriorHusimi.readout_reference_translate
#check @Fermionic.ExteriorHusimi.readout_reference_same_law
#check @Fermionic.ExteriorHusimi.integral_readout_reference
#check @Fermionic.ExteriorHusimi.readout_rotated
#check @Fermionic.ExteriorHusimi.readout_rotated_same_law
#check @Fermionic.ExteriorHusimi.integral_readout_rotated
#check @Fermionic.ExteriorHusimi.readout_forward_rotated_same_law
#check @Fermionic.ExteriorHusimi.integral_readout_forward_rotated
#check @Fermionic.ExteriorHusimi.readout_coherent_input_same_law
#check @Fermionic.ExteriorHusimi.integral_readout_coherent_input
#check @Fermionic.ExteriorHusimi.readout_conditional
#check @Fermionic.ExteriorHusimi.readout_conditional_normalized
#check @Fermionic.ExteriorHusimi.readout_conditional_zero
#check @Fermionic.ExteriorHusimi.integral_conditional
#check @Fermionic.ExteriorHusimi.readout_eq_one_of_subsingleton
#check @Fermionic.ExteriorHusimi.readout_zero_particles
#check @Fermionic.ExteriorHusimi.readout_filled_sector
#check @Fermionic.HusimiScale.coherentLaw
#check @Fermionic.HusimiScale.coherentLaw_isProbability
#check @Fermionic.HusimiScale.coherentLaw_mem_unitInterval
#check @Fermionic.HusimiScale.scaleAverage
#check @Fermionic.HusimiScale.scaleAverage_eq_integral
#check @Fermionic.HusimiScale.continuous_scaleAverage
#check @Fermionic.HusimiScale.convex_scaleAverage
#check @Fermionic.HusimiScale.strictConvex_scaleAverage
#check @Fermionic.HusimiScale.scaleAverage_zero
#check @Fermionic.HusimiScale.coherent_inner_conditioning
#check @Fermionic.HusimiScale.coherent_integral_conditioning
#check @Fermionic.HusimiInduction.scaled_test_continuous
#check @Fermionic.HusimiInduction.scaled_test_convex
#check @Fermionic.HusimiInduction.readout_weight_normalized
#check @Fermionic.HusimiInduction.conditional_inner_integrable
#check @Fermionic.HusimiInduction.conditional_coherent_weight
#check @Fermionic.HusimiInduction.zero_sector_isSlater
#check @Fermionic.HusimiInduction.reference
#check @Fermionic.HusimiInduction.index_card_le
#check @Fermionic.HusimiInduction.conditional_inner_bound
#check @Fermionic.HusimiInduction.conditional_integral_bound
#check @Fermionic.HusimiInduction.occupation_integral_bound
#check @Fermionic.HusimiInduction.exterior_husimi_convex_order
#check @Fermionic.HusimiInduction.slater_integral_eq
#check @Fermionic.HusimiInduction.exterior_husimi_equality_implies_slater
#check @Fermionic.HusimiInduction.exterior_husimi_equality_iff
#check @Fermionic.HusimiInduction.exterior_husimi_convex_order_any_slater
#check @Fermionic.SlaterMeasure.sectorMatrixMeasurable
#check @Fermionic.SlaterMeasure.sectorMatrixBorel
#check @Fermionic.SlaterMeasure.projector
#check @Fermionic.SlaterMeasure.projector_continuous
#check @Fermionic.SlaterMeasure.conjugate
#check @Fermionic.SlaterMeasure.conjugate_continuous
#check @Fermionic.SlaterMeasure.projector_mul
#check @Fermionic.SlaterMeasure.orbitMeasure
#check @Fermionic.SlaterMeasure.orbitMeasure_isProbability
#check @Fermionic.SlaterMeasure.orbitMeasure_invariant
#check @Fermionic.SlaterMeasure.orbitMeasure_reference_independent
#check @Fermionic.SlaterMeasure.traceReadout
#check @Fermionic.SlaterMeasure.traceReadout_continuous
#check @Fermionic.SlaterMeasure.basisProjector_eq_single
#check @Fermionic.SlaterMeasure.traceReadout_projector
#check @Fermionic.SlaterMeasure.slater_iff_mem_range
#check @Fermionic.SlaterMeasure.orbitMeasure_ae_slater
#check @Fermionic.SlaterMeasure.orbit_readout_range
#check @Fermionic.SlaterMeasure.orbit_integral_eq_haar
#check @Fermionic.SlaterMeasure.orbit_husimi_convex_order
#check @Fermionic.SlaterMeasure.orbit_husimi_equality_iff
#check @Fermionic.ExteriorEntropy.sectorDimension
#check @Fermionic.ExteriorEntropy.sectorDimension_eq_choose
#check @Fermionic.ExteriorEntropy.sectorDimension_pos
#check @Fermionic.ExteriorEntropy.powerMoment
#check @Fermionic.ExteriorEntropy.normalizedMoment
#check @Fermionic.ExteriorEntropy.wehrl
#check @Fermionic.ExteriorEntropy.sum_readout
#check @Fermionic.ExteriorEntropy.normalizedMoment_one
#check @Fermionic.ExteriorEntropy.powerMoment_integrable
#check @Fermionic.ExteriorEntropy.rpow_strictConvex
#check @Fermionic.ExteriorEntropy.neg_rpow_strictConvex
#check @Fermionic.ExteriorEntropy.powerMoment_le_coherent
#check @Fermionic.ExteriorEntropy.coherent_le_powerMoment
#check @Fermionic.ExteriorEntropy.powerMoment_eq_iff_slater
#check @Fermionic.ExteriorEntropy.normalizedMoment_le_coherent
#check @Fermionic.ExteriorEntropy.coherent_le_normalizedMoment
#check @Fermionic.ExteriorEntropy.normalizedMoment_eq_iff_slater
#check @Fermionic.ExteriorEntropy.powerMoment_pos
#check @Fermionic.ExteriorEntropy.normalizedMoment_pos
#check @Fermionic.ExteriorEntropy.renyiWehrl
#check @Fermionic.ExteriorEntropy.renyiWehrl_minimum
#check @Fermionic.ExteriorEntropy.renyiWehrl_eq_iff_slater
#check @Fermionic.ExteriorEntropy.mul_log_strictConvex
#check @Fermionic.ExteriorEntropy.wehrl_minimum
#check @Fermionic.ExteriorEntropy.wehrl_eq_iff_slater
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
#print axioms Fermionic.CommonJensen.pointwise_jensen
#print axioms Fermionic.CommonJensen.integral_weighted_sum
#print axioms Fermionic.CommonJensen.integral_jensen
#print axioms Fermionic.CommonJensen.ae_eq_mixture_of_integral_eq
#print axioms Fermionic.CommonJensen.ae_eq_of_integral_eq
#print axioms Fermionic.CommonJensen.integral_eq_of_map_eq
#print axioms Fermionic.CommonJensen.common_law_jensen
#print axioms Fermionic.CommonJensen.common_law_eq_implies_ae_eq
#print axioms Fermionic.CommonJensen.integrable_map_of_continuousOn_unitInterval
#print axioms Fermionic.CommonJensen.integrable_comp_of_continuousOn_unitInterval
#print axioms Fermionic.CommonJensen.mixture_aemeasurable_and_range
#print axioms Fermionic.CommonJensen.common_law_jensen_continuous
#print axioms Fermionic.CommonJensen.common_law_eq_implies_ae_eq_continuous
#print axioms Fermionic.CommonJensen.mul_mem_unitInterval
#print axioms Fermionic.CommonJensen.scale_mixture_convex
#print axioms Fermionic.CommonJensen.scale_mixture_strictConvex
#print axioms Fermionic.CommonJensen.integrable_scaled_of_continuousOn
#print axioms Fermionic.CommonJensen.scale_mixture_continuousOn
#print axioms Fermionic.CommonJensen.scale_mixture_convex_continuous
#print axioms Fermionic.CommonJensen.scale_mixture_strictConvex_continuous
#print axioms Fermionic.DensityRigidity.column_eq_zero_of_diag_eq_zero
#print axioms Fermionic.DensityRigidity.row_eq_zero_of_diag_eq_zero
#print axioms Fermionic.DensityRigidity.row_and_column_eq_zero_of_diag_eq_zero
#print axioms Fermionic.DensityRigidity.basisProjector
#print axioms Fermionic.DensityRigidity.basisProjector_apply
#print axioms Fermionic.DensityRigidity.eq_basisProjector_of_trace_eq_one
#print axioms Fermionic.DensityRigidity.eq_zero_of_trace_eq_zero
#print axioms Fermionic.FourMode.Space
#print axioms Fermionic.FourMode.chevalleyQ
#print axioms Fermionic.FourMode.chevalleyB
#print axioms Fermionic.FourMode.chevalleyQ_zero
#print axioms Fermionic.FourMode.chevalleyB_self
#print axioms Fermionic.FourMode.chevalleyQ_add
#print axioms Fermionic.FourMode.chevalleyQ_smul
#print axioms Fermionic.FourMode.axis
#print axioms Fermionic.FourMode.axisCoefficient
#print axioms Fermionic.FourMode.axis_ne_zero
#print axioms Fermionic.FourMode.chevalleyQ_axis
#print axioms Fermionic.FourMode.chevalleyQ_sub_smul_axis
#print axioms Fermionic.FourMode.exists_axisCoefficient_ne_zero
#print axioms Fermionic.FourMode.nonisotropic_decomposition
#print axioms Fermionic.FourMode.IsQuadric
#print axioms Fermionic.FourMode.HasDecomposition
#print axioms Fermionic.FourMode.hasDecomposition_zero_iff
#print axioms Fermionic.FourMode.hasDecomposition_one_iff
#print axioms Fermionic.FourMode.hasDecomposition_two
#print axioms Fermionic.FourMode.decomposition_exists
#print axioms Fermionic.FourMode.exactRank
#print axioms Fermionic.FourMode.exactRank_spec
#print axioms Fermionic.FourMode.exactRank_le
#print axioms Fermionic.FourMode.exactRank_zero_iff
#print axioms Fermionic.FourMode.exactRank_eq_one
#print axioms Fermionic.FourMode.exactRank_one_iff
#print axioms Fermionic.FourMode.exactRank_eq_two
#print axioms Fermionic.FourMode.exactRank_two_iff
#print axioms Fermionic.FourMode.exactRank_nonzero
#print axioms Fermionic.FourMode.magic
#print axioms Fermionic.FourMode.chevalleyQ_magic
#print axioms Fermionic.FourMode.exactRank_magic
#print axioms Fermionic.ExteriorUnitary.Index
#print axioms Fermionic.ExteriorUnitary.AlgebraicSector
#print axioms Fermionic.ExteriorUnitary.Sector
#print axioms Fermionic.ExteriorUnitary.basis
#print axioms Fermionic.ExteriorUnitary.coordinates
#print axioms Fermionic.ExteriorUnitary.coordinates_basis
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix
#print axioms Fermionic.ExteriorUnitary.coordinates_intertwine
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix_mul
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix_one
#print axioms Fermionic.ExteriorUnitary.enumerate
#print axioms Fermionic.ExteriorUnitary.diagonal_on_basis
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix_diagonal
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix_entry
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix_conjTranspose
#print axioms Fermionic.ExteriorUnitary.exteriorMatrix_mem_unitary
#print axioms Fermionic.ExteriorUnitary.representation
#print axioms Fermionic.ExteriorUnitary.continuous_exteriorMatrix
#print axioms Fermionic.ExteriorUnitary.continuous_representation
#print axioms Fermionic.HaarConditioning.probabilityHaar
#print axioms Fermionic.HaarConditioning.probabilityHaar_isHaar
#print axioms Fermionic.HaarConditioning.probabilityHaar_isProbability
#print axioms Fermionic.HaarConditioning.probabilityHaar_isRightInvariant
#print axioms Fermionic.HaarConditioning.map_readout_mul_left
#print axioms Fermionic.HaarConditioning.map_readout_mul_right
#print axioms Fermionic.HaarConditioning.map_readout_positive_mass
#print axioms Fermionic.HaarConditioning.readout_eq_of_ae_eq
#print axioms Fermionic.HaarConditioning.integral_double_haar
#print axioms Fermionic.HaarConditioning.integral_eq_double_haar
#print axioms Fermionic.HaarConditioning.isCompact_unitaryGroup
#print axioms Fermionic.HaarConditioning.unitaryGroup_compactSpace
#print axioms Fermionic.HaarConditioning.unitaryGroup_measurableSpace
#print axioms Fermionic.HaarConditioning.unitaryGroup_borelSpace
#print axioms Fermionic.HaarConditioning.unitaryHaar
#print axioms Fermionic.HaarConditioning.unitaryHaar_isProbability
#print axioms Fermionic.HaarConditioning.unitaryHaar_isHaar
#print axioms Fermionic.HaarConditioning.unitaryHaar_isRightInvariant
#print axioms Fermionic.HaarConditioning.fixFirstHom
#print axioms Fermionic.HaarConditioning.fixFirstHom_continuous
#print axioms Fermionic.HaarConditioning.fixFirstHom_lower_apply
#print axioms Fermionic.HaarConditioning.fixFirstHom_first_apply
#print axioms Fermionic.HaarConditioning.fixFirstHom_first_row
#print axioms Fermionic.HaarConditioning.fixFirstHom_first_column
#print axioms Fermionic.HaarConditioning.fixFirstHom_injective
#print axioms Fermionic.HaarConditioning.unitary_integral_eq_double
#print axioms Fermionic.HaarConditioning.unitaryReindex
#print axioms Fermionic.HaarConditioning.unitaryReindex_apply
#print axioms Fermionic.HaarConditioning.unitaryReindex_continuous
#print axioms Fermionic.HaarConditioning.unitaryReindex_measurePreserving
#print axioms Fermionic.HaarConditioning.firstFinEquiv
#print axioms Fermionic.HaarConditioning.firstFinEquiv_zero
#print axioms Fermionic.HaarConditioning.firstFinEquiv_succ
#print axioms Fermionic.HaarConditioning.firstFinEquiv_symm_zero
#print axioms Fermionic.HaarConditioning.firstFinEquiv_symm_succ
#print axioms Fermionic.HaarConditioning.fixFirstFinHom
#print axioms Fermionic.HaarConditioning.fixFirstFinHom_zero_zero
#print axioms Fermionic.HaarConditioning.fixFirstFinHom_zero_succ
#print axioms Fermionic.HaarConditioning.fixFirstFinHom_succ_zero
#print axioms Fermionic.HaarConditioning.fixFirstFinHom_succ_succ
#print axioms Fermionic.HaarConditioning.fixFirstFinHom_continuous
#print axioms Fermionic.HaarConditioning.unitary_fin_integral_eq_double
#print axioms Fermionic.ExteriorDifferential.differentiable_exteriorMatrix
#print axioms Fermionic.ExteriorDifferential.infinitesimal
#print axioms Fermionic.ExteriorDifferential.hasFDerivAt_identity
#print axioms Fermionic.ExteriorDifferential.sandwich
#print axioms Fermionic.ExteriorDifferential.sandwich_apply
#print axioms Fermionic.ExteriorDifferential.infinitesimal_conjTranspose
#print axioms Fermionic.ExteriorDifferential.infinitesimal_unitary_conjugation
#print axioms Fermionic.ExteriorDifferential.infinitesimal_diagonal
#print axioms Fermionic.ExteriorDifferential.occupation
#print axioms Fermionic.ExteriorDifferential.infinitesimal_single_diag
#print axioms Fermionic.ExteriorDifferential.oneParticle
#print axioms Fermionic.ExteriorDifferential.oneParticle_isHermitian
#print axioms Fermionic.ExteriorDifferential.trace_infinitesimal
#print axioms Fermionic.ExteriorDifferential.oneParticle_diag
#print axioms Fermionic.ExteriorDifferential.oneParticle_unitary_conjugation
#print axioms Fermionic.OccupationMixture.eigenRotation
#print axioms Fermionic.OccupationMixture.eigenDensity
#print axioms Fermionic.OccupationMixture.eigenDensity_posSemidef
#print axioms Fermionic.OccupationMixture.eigenDensity_trace
#print axioms Fermionic.OccupationMixture.eigenDensity_oneParticle_diagonal
#print axioms Fermionic.OccupationMixture.probability
#print axioms Fermionic.OccupationMixture.probability_nonneg
#print axioms Fermionic.OccupationMixture.probability_sum
#print axioms Fermionic.OccupationMixture.probability_cast
#print axioms Fermionic.OccupationMixture.occupancyProjection
#print axioms Fermionic.OccupationMixture.common_diagonal_mixture
#print axioms Fermionic.OccupationMixture.common_projection_mixture
#print axioms Fermionic.OccupationMixture.oneParticleReadout
#print axioms Fermionic.OccupationMixture.common_readout_mixture
#print axioms Fermionic.ConditionalSector.insertFirst
#print axioms Fermionic.ConditionalSector.mem_insertFirst_zero
#print axioms Fermionic.ConditionalSector.mem_insertFirst_succ
#print axioms Fermionic.ConditionalSector.insertFirst_injective
#print axioms Fermionic.ConditionalSector.insertFirst_surjective_occupied
#print axioms Fermionic.ConditionalSector.insertFirst_range
#print axioms Fermionic.ConditionalSector.sum_insertFirst
#print axioms Fermionic.ConditionalSector.enumerate_insertFirst
#print axioms Fermionic.ConditionalSector.enumerate_insertFirst_zero
#print axioms Fermionic.ConditionalSector.enumerate_insertFirst_succ
#print axioms Fermionic.ConditionalSector.basisInclusion
#print axioms Fermionic.ConditionalSector.basisInclusion_compress_apply
#print axioms Fermionic.ConditionalSector.basisInclusion_compress
#print axioms Fermionic.ConditionalSector.basisInclusion_isometry
#print axioms Fermionic.ConditionalSector.basisInclusion_compress_posSemidef
#print axioms Fermionic.ConditionalSector.basisInclusion_compress_trace_le_one
#print axioms Fermionic.ConditionalSector.intertwine_of_unitary_compression
#print axioms Fermionic.ConditionalSector.quadratic
#print axioms Fermionic.ConditionalSector.quadratic_compression
#print axioms Fermionic.ConditionalSector.quadratic_smul
#print axioms Fermionic.ConditionalSector.weight
#print axioms Fermionic.ConditionalSector.weight_nonneg
#print axioms Fermionic.ConditionalSector.trace_eq_weight
#print axioms Fermionic.ConditionalSector.compression_zero_of_weight_zero
#print axioms Fermionic.ConditionalSector.normalized
#print axioms Fermionic.ConditionalSector.normalized_posSemidef
#print axioms Fermionic.ConditionalSector.normalized_trace_eq_one
#print axioms Fermionic.ConditionalSector.weight_smul_normalized
#print axioms Fermionic.ConditionalSector.quadratic_eq_weight_mul_normalized
#print axioms Fermionic.ConditionalSector.creation
#print axioms Fermionic.ConditionalSector.creation_isometry
#print axioms Fermionic.ConditionalSector.creation_conjTranspose_mulVec
#print axioms Fermionic.ConditionalSector.creation_trace_eq_oneParticle
#print axioms Fermionic.ConditionalSector.exteriorMatrix_fixFirst_compress
#print axioms Fermionic.ConditionalSector.creation_intertwine
#print axioms Fermionic.ConditionalSector.rotated
#print axioms Fermionic.ConditionalSector.rotated_posSemidef
#print axioms Fermionic.ConditionalSector.rotated_trace
#print axioms Fermionic.ConditionalSector.conditionalMatrix
#print axioms Fermionic.ConditionalSector.conditionalMatrix_posSemidef
#print axioms Fermionic.ConditionalSector.conditional_weight_mem_unitInterval
#print axioms Fermionic.ConditionalSector.conditional_weight_eq_oneParticleReadout
#print axioms Fermionic.ConditionalSector.conditional_readout
#print axioms Fermionic.ConditionalSector.conditional_readout_zero
#print axioms Fermionic.ConditionalSector.conditional_readout_normalized
#print axioms Fermionic.OccupancyOrbit.coordinateProjection
#print axioms Fermionic.OccupancyOrbit.permutationUnitary
#print axioms Fermionic.OccupancyOrbit.occupancyPermutation
#print axioms Fermionic.OccupancyOrbit.occupancyPermutation_mem
#print axioms Fermionic.OccupancyOrbit.permutation_conjugates_projection
#print axioms Fermionic.OccupancyOrbit.occupancy_same_orbit
#print axioms Fermionic.OccupancyOrbit.projectionReadout
#print axioms Fermionic.OccupancyOrbit.projectionReadout_eq_sum
#print axioms Fermionic.OccupancyOrbit.projectionReadout_mem_unitInterval
#print axioms Fermionic.OccupancyOrbit.continuous_projectionReadout
#print axioms Fermionic.OccupancyOrbit.projectionReadout_conjugate
#print axioms Fermionic.OccupancyOrbit.occupancy_readout_same_law
#print axioms Fermionic.OccupancyOrbit.projectionReadout_permutation
#print axioms Fermionic.OccupancyOrbit.projectionReadout_injective
#print axioms Fermionic.OccupationConvexOrder.component
#print axioms Fermionic.OccupationConvexOrder.component_continuous
#print axioms Fermionic.OccupationConvexOrder.component_range
#print axioms Fermionic.OccupationConvexOrder.component_common_law
#print axioms Fermionic.OccupationConvexOrder.actual_readout_eq_common_mixture
#print axioms Fermionic.OccupationConvexOrder.actual_readout_range
#print axioms Fermionic.OccupationConvexOrder.actual_readout_continuous
#print axioms Fermionic.OccupationConvexOrder.occupation_convex_order
#print axioms Fermionic.OccupationConvexOrder.IsSlaterDensity
#print axioms Fermionic.OccupationConvexOrder.component_injective
#print axioms Fermionic.OccupationConvexOrder.eigenDensity_basis_implies_slater
#print axioms Fermionic.OccupationConvexOrder.occupation_equality_implies_slater
#print axioms Fermionic.SlaterOrbit.orderedPermutation
#print axioms Fermionic.SlaterOrbit.orderedPermutation_enumerate
#print axioms Fermionic.SlaterOrbit.permutation_basis_vector
#print axioms Fermionic.SlaterOrbit.ordered_permutation_wedge
#print axioms Fermionic.SlaterOrbit.ordered_permutation_column
#print axioms Fermionic.SlaterOrbit.basis_projector_same_orbit
#print axioms Fermionic.SlaterOneParticle.signUnitary
#print axioms Fermionic.SlaterOneParticle.diagonal_unitary_preserves_basis
#print axioms Fermionic.SlaterOneParticle.sign_preserves_basis
#print axioms Fermionic.SlaterOneParticle.oneParticle_basisProjector
#print axioms Fermionic.SlaterClosure.basisUnitary
#print axioms Fermionic.SlaterClosure.basisUnitary_apply
#print axioms Fermionic.SlaterClosure.exists_unitary_extension
#print axioms Fermionic.SlaterClosure.exists_unitary_first_column
#print axioms Fermionic.SlaterClosure.exists_unitary_row_alignment
#print axioms Fermionic.SlaterClosure.exists_unitary_frame_extension
#print axioms Fermionic.SlaterClosure.frameVector
#print axioms Fermionic.SlaterClosure.frameVector_unitary_columns
#print axioms Fermionic.SlaterClosure.unitary_columns_isometry
#print axioms Fermionic.SlaterClosure.frameVector_mul
#print axioms Fermionic.SlaterClosure.frameVector_is_unitary_column
#print axioms Fermionic.SlaterClosure.creation_contract_frame
#print axioms Fermionic.SlaterClosure.contraction_unitary_column
#print axioms Fermionic.SlaterClosure.pureMatrix
#print axioms Fermionic.SlaterClosure.pureMatrix_compression
#print axioms Fermionic.SlaterClosure.pureMatrix_smul
#print axioms Fermionic.SlaterClosure.pureMatrix_unitary_column
#print axioms Fermionic.SlaterClosure.unitary_column_trace_one
#print axioms Fermionic.SlaterClosure.normalized_pos_smul
#print axioms Fermionic.SlaterClosure.normalized_compression_isSlater
#print axioms Fermionic.SlaterClosure.rotated_isSlater
#print axioms Fermionic.SlaterClosure.conditional_isSlater
#print axioms Fermionic.ExteriorHusimi.readout
#print axioms Fermionic.ExteriorHusimi.readout_continuous
#print axioms Fermionic.ExteriorHusimi.readout_mem_unitInterval
#print axioms Fermionic.ExteriorHusimi.continuous_test_readout
#print axioms Fermionic.ExteriorHusimi.quadratic_basis
#print axioms Fermionic.ExteriorHusimi.readout_eq_quadratic
#print axioms Fermionic.ExteriorHusimi.creation_basis
#print axioms Fermionic.ExteriorHusimi.basisProjector_posSemidef
#print axioms Fermionic.ExteriorHusimi.basisProjector_trace
#print axioms Fermionic.ExteriorHusimi.readout_basisProjector_one
#print axioms Fermionic.ExteriorHusimi.coherent_readout_positive_mass
#print axioms Fermionic.ExteriorHusimi.orderedPermutation_mul_basis
#print axioms Fermionic.ExteriorHusimi.readout_reference_translate
#print axioms Fermionic.ExteriorHusimi.readout_reference_same_law
#print axioms Fermionic.ExteriorHusimi.integral_readout_reference
#print axioms Fermionic.ExteriorHusimi.readout_rotated
#print axioms Fermionic.ExteriorHusimi.readout_rotated_same_law
#print axioms Fermionic.ExteriorHusimi.integral_readout_rotated
#print axioms Fermionic.ExteriorHusimi.readout_forward_rotated_same_law
#print axioms Fermionic.ExteriorHusimi.integral_readout_forward_rotated
#print axioms Fermionic.ExteriorHusimi.readout_coherent_input_same_law
#print axioms Fermionic.ExteriorHusimi.integral_readout_coherent_input
#print axioms Fermionic.ExteriorHusimi.readout_conditional
#print axioms Fermionic.ExteriorHusimi.readout_conditional_normalized
#print axioms Fermionic.ExteriorHusimi.readout_conditional_zero
#print axioms Fermionic.ExteriorHusimi.integral_conditional
#print axioms Fermionic.ExteriorHusimi.readout_eq_one_of_subsingleton
#print axioms Fermionic.ExteriorHusimi.readout_zero_particles
#print axioms Fermionic.ExteriorHusimi.readout_filled_sector
#print axioms Fermionic.HusimiScale.coherentLaw
#print axioms Fermionic.HusimiScale.coherentLaw_isProbability
#print axioms Fermionic.HusimiScale.coherentLaw_mem_unitInterval
#print axioms Fermionic.HusimiScale.scaleAverage
#print axioms Fermionic.HusimiScale.scaleAverage_eq_integral
#print axioms Fermionic.HusimiScale.continuous_scaleAverage
#print axioms Fermionic.HusimiScale.convex_scaleAverage
#print axioms Fermionic.HusimiScale.strictConvex_scaleAverage
#print axioms Fermionic.HusimiScale.scaleAverage_zero
#print axioms Fermionic.HusimiScale.coherent_inner_conditioning
#print axioms Fermionic.HusimiScale.coherent_integral_conditioning
#print axioms Fermionic.HusimiInduction.scaled_test_continuous
#print axioms Fermionic.HusimiInduction.scaled_test_convex
#print axioms Fermionic.HusimiInduction.readout_weight_normalized
#print axioms Fermionic.HusimiInduction.conditional_inner_integrable
#print axioms Fermionic.HusimiInduction.conditional_coherent_weight
#print axioms Fermionic.HusimiInduction.zero_sector_isSlater
#print axioms Fermionic.HusimiInduction.reference
#print axioms Fermionic.HusimiInduction.index_card_le
#print axioms Fermionic.HusimiInduction.conditional_inner_bound
#print axioms Fermionic.HusimiInduction.conditional_integral_bound
#print axioms Fermionic.HusimiInduction.occupation_integral_bound
#print axioms Fermionic.HusimiInduction.exterior_husimi_convex_order
#print axioms Fermionic.HusimiInduction.slater_integral_eq
#print axioms Fermionic.HusimiInduction.exterior_husimi_equality_implies_slater
#print axioms Fermionic.HusimiInduction.exterior_husimi_equality_iff
#print axioms Fermionic.HusimiInduction.exterior_husimi_convex_order_any_slater
#print axioms Fermionic.SlaterMeasure.sectorMatrixMeasurable
#print axioms Fermionic.SlaterMeasure.sectorMatrixBorel
#print axioms Fermionic.SlaterMeasure.projector
#print axioms Fermionic.SlaterMeasure.projector_continuous
#print axioms Fermionic.SlaterMeasure.conjugate
#print axioms Fermionic.SlaterMeasure.conjugate_continuous
#print axioms Fermionic.SlaterMeasure.projector_mul
#print axioms Fermionic.SlaterMeasure.orbitMeasure
#print axioms Fermionic.SlaterMeasure.orbitMeasure_isProbability
#print axioms Fermionic.SlaterMeasure.orbitMeasure_invariant
#print axioms Fermionic.SlaterMeasure.orbitMeasure_reference_independent
#print axioms Fermionic.SlaterMeasure.traceReadout
#print axioms Fermionic.SlaterMeasure.traceReadout_continuous
#print axioms Fermionic.SlaterMeasure.basisProjector_eq_single
#print axioms Fermionic.SlaterMeasure.traceReadout_projector
#print axioms Fermionic.SlaterMeasure.slater_iff_mem_range
#print axioms Fermionic.SlaterMeasure.orbitMeasure_ae_slater
#print axioms Fermionic.SlaterMeasure.orbit_readout_range
#print axioms Fermionic.SlaterMeasure.orbit_integral_eq_haar
#print axioms Fermionic.SlaterMeasure.orbit_husimi_convex_order
#print axioms Fermionic.SlaterMeasure.orbit_husimi_equality_iff
#print axioms Fermionic.ExteriorEntropy.sectorDimension
#print axioms Fermionic.ExteriorEntropy.sectorDimension_eq_choose
#print axioms Fermionic.ExteriorEntropy.sectorDimension_pos
#print axioms Fermionic.ExteriorEntropy.powerMoment
#print axioms Fermionic.ExteriorEntropy.normalizedMoment
#print axioms Fermionic.ExteriorEntropy.wehrl
#print axioms Fermionic.ExteriorEntropy.sum_readout
#print axioms Fermionic.ExteriorEntropy.normalizedMoment_one
#print axioms Fermionic.ExteriorEntropy.powerMoment_integrable
#print axioms Fermionic.ExteriorEntropy.rpow_strictConvex
#print axioms Fermionic.ExteriorEntropy.neg_rpow_strictConvex
#print axioms Fermionic.ExteriorEntropy.powerMoment_le_coherent
#print axioms Fermionic.ExteriorEntropy.coherent_le_powerMoment
#print axioms Fermionic.ExteriorEntropy.powerMoment_eq_iff_slater
#print axioms Fermionic.ExteriorEntropy.normalizedMoment_le_coherent
#print axioms Fermionic.ExteriorEntropy.coherent_le_normalizedMoment
#print axioms Fermionic.ExteriorEntropy.normalizedMoment_eq_iff_slater
#print axioms Fermionic.ExteriorEntropy.powerMoment_pos
#print axioms Fermionic.ExteriorEntropy.normalizedMoment_pos
#print axioms Fermionic.ExteriorEntropy.renyiWehrl
#print axioms Fermionic.ExteriorEntropy.renyiWehrl_minimum
#print axioms Fermionic.ExteriorEntropy.renyiWehrl_eq_iff_slater
#print axioms Fermionic.ExteriorEntropy.mul_log_strictConvex
#print axioms Fermionic.ExteriorEntropy.wehrl_minimum
#print axioms Fermionic.ExteriorEntropy.wehrl_eq_iff_slater
