(** Public surface and kernel-assumption audit for the Foundation modal port. *)

From FoundationModal Require Import
  Syntax NNFormula FormulaEncoding PLoN Axioms HilbertK PLoNCompleteness Kripke
  KripkeAlgebra
  NNFormulaSemantics HilbertKSoundness Complement ComplexityLimited Filtration
  Correspondence FiltrationExtensions CanonicalK Loeb FrameProperties
  CorrespondenceExtensions NormalHilbert LogicInfrastructure CanonicalExtensions
  FiniteMaximalContext Modality CanonicalDB5 StandardTranslation Preservation Root FrameTransformations StructuralFrames
  WeakCorrespondence CanonicalCombinations CanonicalTB Boxdot CanonicalPoint2
  CanonicalPoint3 CanonicalPoint4 CanonicalS5 CanonicalMcK CanonicalTrivVer
  CanonicalPoint2McK CanonicalPoint3McK CanonicalPoint4McK Undefinability.

Check substitute_comp.
Check satisfies_substitute.
Check valid_K.

(** Relational complex algebras and their exact agreement with Kripke
    satisfaction. *)
Check complex_box_top.
Check complex_box_intersection.
Check complex_dia_dual.
Check algebra_eval_dia.
Check algebraic_satisfies.
Check algebraic_valid_imp.
Check algebraic_valid_iff.
Check algebraic_valid.

Check nnformula_eq_dec.
Check nn_neg_involutive.
Check nn_neg_injective.
Check nn_degree_neg.
Check nn_degree_to_formula.
Check nn_dnf_part_degree_zero.
Check nn_modal_cnf_box.
Check nn_modal_dnf_dia.
Check nn_satisfies_neg.
Check nn_to_formula_correct.
Check formula_to_nnf_correct.
Check nn_to_formula_valid.
Check formula_to_nnf_valid.
Check formula_nnf_round_trip.
Check nn_formula_round_trip.

Check modal_formula_decode_code.
Check modal_formula_enum_surjective.
Check nnformula_decode_code.
Check nnformula_enum_surjective.

Check plon_satisfies_box.
Check plon_not_satisfies_box.
Check plon_model_valid_elim_contra.
Check plon_model_valid_nec.
Check plon_model_valid_mp.
Check plon_replacement_of_equivalents_fails.
Check plon_frame_class_invalid_iff_frame.
Check plon_frame_class_invalid_iff_model.
Check plon_frame_class_invalid_iff_model_world.

Check plon_soundness_frameclass.
Check plon_consistent_of_nonempty_frameclass.
Check plon_lindenbaum_extension.
Check plon_mct_neg_iff.
Check plon_mct_imp_iff.
Check plon_canonical_truth_lemma.
Check plon_canonical_countermodel.
Check plon_complete_of_canonical_frame.
Check plon_N_sound.
Check plon_N_consistent.
Check plon_N_complete.
Check plon_N_sound_complete.
Check plon_N_strictly_weaker_K.
Check plon_N_strictly_weaker_EN.

(** Complete named schema surface from Foundation/Modal/Axioms.lean. *)
Check Axioms.DiaDuality.
Check Axioms.K.
Check Axioms.M.
Check Axioms.C.
Check (@Axioms.N nat).
Check Axioms.T.
Check Axioms.DiaTc.
Check Axioms.B.
Check Axioms.D.
Check (@Axioms.P nat).
Check Axioms.Four.
Check Axioms.FourN.
Check Axioms.Five.
Check Axioms.Point2.
Check Axioms.WeakPoint2.
Check Axioms.C4.
Check Axioms.CD.
Check Axioms.Tc.
Check Axioms.DiaT.
Check Axioms.Ver.
Check Axioms.Point3.
Check Axioms.WeakPoint3.
Check Axioms.Point4.
Check Axioms.Grz.
Check Axioms.Dum.
Check Axioms.McK.
Check Axioms.L.
Check Axioms.Z.
Check Axioms.Hen.
Check Axioms.Mk.
Check Axioms.H.
Check Axioms.Geach.
Check Axioms.I.

Check K_proves_fold.
Check K_proves_substitute.
Check K_proves_identity.
Check K_proves_dne.
Check K_derives_empty_iff.
Check K_derives_deduction_iff.
Check theory_consistent_insert_iff.
Check theory_consistent_insert_neg_iff.
Check K_derives_boxed.
Check K_derives_box_from_unboxed.
Check K_proves_sound_on_frame.
Check K_derives_sound.
Check K_is_consistent.

Check lindenbaum_extension.
Check mct_neg_iff.
Check mct_derivable_mem.
Check mct_imp_iff.
Check canonical_successor_of_neg_box.
Check canonical_truth_lemma.
Check K_canonical_countermodel.
Check K_complete.
Check K_sound_complete.
Check K_finite_sound_complete.

Check normal_proves_weaken.
Check normal_proves_substitute.
Check empty_normal_proves_iff_K.
Check K_proves_normal.
Check KT_weaker_than_S4.
Check K4_weaker_than_S4.
Check KT_weaker_than_S5.
Check K5_weaker_than_S5.
Check normal_proves_sound_on_frame.
Check KT_proves_sound_on_reflexive_frame.
Check KD_proves_sound_on_serial_frame.
Check KB_proves_sound_on_symmetric_frame.
Check K4_proves_sound_on_transitive_frame.
Check K5_proves_sound_on_right_euclidean_frame.
Check S4_proves_sound_on_preorder_frame.
Check S5_proves_sound_on_reflexive_euclidean_frame.
Check GL_proves_sound_on_transitive_cwf_frame.
Check Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame.
Check KT_is_consistent.
Check KD_is_consistent.
Check KB_is_consistent.
Check K4_is_consistent.
Check K5_is_consistent.
Check S4_is_consistent.
Check S5_is_consistent.
Check GL_is_consistent.
Check Grz_is_consistent.

(** Predicate-valued logics, normal and quasinormal sums, and global
    consequence. *)
Check logic_eq_iff_equiv.
Check logic_consistent_iff_exists_unprovable.
Check logic_no_bot.
Check logic_list_conj_equivalence.
Check normal_proves_logic_is_normal.
Check normal_logic_contains_K.
Check logic_sum_normal_sym.
Check logic_sum_normal_normal_left.
Check logic_sum_quasi_normal_sym.
Check logic_sum_quasi_normal_iff_subset.
Check logic_sum_quasi_normal_sum_union.
Check logic_sum_quasi_normal_iff_finite_provable.
Check logic_sum_quasi_normal_iff_finite_provable_letterless.
Check logic_sum_quasi_normal_eq_alt.
Check logic_sum_quasi_normal_rec_omit_substitution_strong.
Check logic_sum_quasi_normal_rec_letterless_expansion.
Check global_consequence_weaken.
Check global_consequence_finite_box_le_provable.
Check global_consequence_of_finite_box_le_provable.
Check global_consequence_iff_finite_box_le_provable.
Check logic_global_foundation_box_le_equivalence.
Check global_consequence_iff_finite_foundation_box_le_provable.

Check normal_derives_deduction.
Check normal_theory_consistent_insert_neg_iff.
Check normal_derives_box_from_unboxed.
Check normal_lindenbaum_extension.
Check normal_mct_neg_iff.
Check normal_mct_imp_iff.
Check normal_canonical_successor_of_neg_box.
Check normal_canonical_truth_lemma.
Check normal_complete_of_canonical_frame.
Check KT_canonical_frame_reflexive.
Check K4_canonical_frame_transitive.
Check S4_canonical_frame_reflexive.
Check S4_canonical_frame_transitive.
Check KT_sound_complete.
Check K4_sound_complete.
Check S4_sound_complete.
Check K_strictly_weaker_KT.
Check K_strictly_weaker_K4.
Check KT_strictly_weaker_S4.
Check K4_strictly_weaker_S4.

(** Canonical D/B/Five frame properties and complete KD/KB/K5 metatheory. *)
Check normal_canonical_serial_of_schema_D.
Check normal_canonical_symmetric_of_schema_B.
Check normal_canonical_right_euclidean_of_schema_Five.
Check KD_canonical_frame_serial.
Check KB_canonical_frame_symmetric.
Check K5_canonical_frame_right_euclidean.
Check KD_sound_complete.
Check KB_sound_complete.
Check K5_sound_complete.
Check KD_proves_P.
Check normal_proves_P_of_schema_D.
Check K_strictly_weaker_KD.
Check K_strictly_weaker_KB.
Check K_strictly_weaker_K5.

(** Canonical combinations of D, B, Four, Five, and WeakPoint3. *)
Check K45_schema_substitution_closed.
Check KD45_schema_substitution_closed.
Check K4Point3_schema_substitution_closed.
Check K45_frame_class_in_K4Point3.
Check K45_canonical_frame.
Check KD4_canonical_frame.
Check KD5_canonical_frame.
Check KDB_canonical_frame.
Check KB4_canonical_frame.
Check KB5_canonical_frame.
Check KD45_canonical_frame.
Check K45_sound_complete.
Check KD4_sound_complete.
Check KD5_sound_complete.
Check KDB_sound_complete.
Check KB4_sound_complete.
Check KB5_sound_complete.
Check KD45_sound_complete.
Check K4Point3_strictly_weaker_K45.
Check K5_strictly_weaker_K45.
Check KD_strictly_weaker_KD4.
Check K4_strictly_weaker_KD4.
Check KD_strictly_weaker_KD5.
Check K5_strictly_weaker_KD5.
Check KD_strictly_weaker_KDB.
Check KB_strictly_weaker_KDB.
Check K45_strictly_weaker_KB4.
Check KB_strictly_weaker_KB4.
Check KD4_strictly_weaker_KD45.
Check KD5_strictly_weaker_KD45.
Check K45_strictly_weaker_KD45.

(** Reflexive-symmetric KTB and equivalence-frame KT4B, including finite
    completeness and the S5 comparison. *)
Check KTB_schema_substitution_closed.
Check KT4B_schema_substitution_closed.
Check KTB_frame_is_serial_symmetric.
Check KT4B_frame_class_iff_S5_frame_class.
Check KTB_canonical.
Check KT4B_canonical.
Check KTB_sound_complete.
Check KT4B_sound_complete.
Check KTB_finite_sound_complete.
Check KT4B_finite_sound_complete.
Check S5_KT4B_equivalent.
Check KT_strictly_weaker_KTB.
Check KDB_strictly_weaker_KTB.

(** Canonical K4.2 and S4.2, including the rooted finite-filtration argument
    for S4.2. *)
Check K4Point2_schema_substitution_closed.
Check S4Point2_schema_substitution_closed.
Check normal_canonical_piecewise_convergent_of_schema_WeakPoint2.
Check normal_canonical_strongly_confluent_of_schema_Point2.
Check K4Point2_canonical_frame.
Check S4Point2_canonical_frame.
Check K4Point2_sound_complete.
Check S4Point2_sound_complete.
Check finest_tc_preserves_piecewise_strongly_convergent.
Check S4Point2_finite_sound_complete.
Check S4Point2_frame_is_K4Point2.
Check K4_strictly_weaker_K4Point2.
Check S4_strictly_weaker_S4Point2.
Check K4Point2_strictly_weaker_S4Point2.
Check KT_strictly_weaker_S4Point2.

(** Canonical K4.3 and S4.3, including linear-preorder completeness and the
    rooted finite transitive-closure filtration for S4.3. *)
Check schema_Point3_substitution_closed.
Check S4Point3_schema_substitution_closed.
Check normal_canonical_piecewise_connected_of_schema_WeakPoint3.
Check normal_canonical_piecewise_strongly_connected_of_schema_Point3.
Check K4Point3_canonical_frame.
Check S4Point3_canonical_frame.
Check K4Point3_sound_complete.
Check S4Point3_sound_complete.
Check S4Point3_linear_preorder_sound_complete.
Check finest_tc_preserves_strongly_connected.
Check S4Point3_finite_sound_complete.
Check S4Point3_frame_is_S4Point2.
Check S4Point3_frame_is_K4Point3.
Check K4_strictly_weaker_K4Point3.
Check S4Point2_strictly_weaker_S4Point3.
Check S4_strictly_weaker_S4Point3.
Check K4Point3_strictly_weaker_S4Point3.
Check KT_strictly_weaker_S4Point3.

(** Canonical S4.4 and its exact Sobocinski frame condition. *)
Check S4Point4_axiom_schema_substitution_closed.
Check S4Point4_schema_substitution_closed.
Check S4Point4_frame_is_S4Point3.
Check normal_canonical_sobocinski_of_schema_Point4.
Check S4Point4_canonical_frame.
Check S4Point4_sound_complete.
Check S4Point3_weaker_than_S4Point4.
Check point4_three_chain_not_sobocinski.
Check S4Point3_strictly_weaker_S4Point4.

(** Universal-frame S5 completeness and the complete pinned predecessor
    hierarchy. *)
Check frame_universal.
Check point_generated_universal_of_s5.
Check valid_on_universal_frames_iff_valid_on_s5_frames.
Check S5_universal_sound_complete.
Check S5_frame_is_KTB.
Check S5_frame_is_KD45.
Check S5_frame_is_KB4.
Check S5_frame_is_S4Point4.
Check KTB_strictly_weaker_S5.
Check KD45_strictly_weaker_S5.
Check KB4_strictly_weaker_S5.
Check S4Point4_strictly_weaker_S5.
Check S4_strictly_weaker_S5.
Check KT_strictly_weaker_S5.

(** Canonical McKinsey successors and K4McK/S4McK completeness. *)
Check McK_axiom_schema_substitution_closed.
Check K4McK_schema_substitution_closed.
Check S4McK_schema_substitution_closed.
Check normal_proves_base_mck_switch_possible.
Check normal_proves_base_mck_jointly_possible.
Check normal_derives_base_mck_seed_partition.
Check base_mck_seed_theory_consistent.
Check normal_canonical_mckinsey_of_K4McK_schemas.
Check normal_canonical_mckinsey_of_schema_K4McK.
Check K4McK_canonical_frame.
Check S4McK_canonical_frame.
Check K4McK_sound_complete.
Check S4McK_sound_complete.
Check K_weaker_than_K4McK.
Check K4_strictly_weaker_K4McK.
Check S4_strictly_weaker_S4McK.
Check K4McK_strictly_weaker_S4McK.

(** Canonical S4.2McK and both pinned strict predecessors. *)
Check S4Point2McK_schema_substitution_closed.
Check S4Point2McK_frame_is_S4McK.
Check S4Point2McK_frame_is_S4Point2.
Check S4Point2McK_canonical_frame.
Check S4Point2McK_sound_complete.
Check S4McK_strictly_weaker_S4Point2McK.
Check S4Point2_strictly_weaker_S4Point2McK.

(** Canonical S4.3McK and both pinned strict predecessors. *)
Check S4Point3McK_schema_substitution_closed.
Check S4Point3McK_frame_is_S4Point2McK.
Check S4Point3McK_canonical_frame.
Check S4Point3McK_sound_complete.
Check S4Point2McK_strictly_weaker_S4Point3McK.
Check S4Point3_strictly_weaker_S4Point3McK.

(** Canonical S4.4McK and its S4.3McK inclusion. *)
Check S4Point3McK_schema_substitution_closed.
Check S4Point3McK_proves_sound_on_frame.
Check S4Point4McK_frame_is_S4Point3McK.
Check S4Point4McK_is_consistent.
Check S4Point4McK_canonical_frame.
Check S4Point4McK_sound_complete.
Check S4Point3McK_weaker_than_S4Point4McK.
Check S4Point3McK_strictly_weaker_S4Point4McK.
Check S4Point4_weaker_than_S4Point4McK.
Check S4Point4_strictly_weaker_S4Point4McK.

(** Coreflexive KTc, equality-frame Triv, and isolated-frame Ver, including
    their source-local entailments, finite completeness, and strictness
    chains. *)
Check schema_Tc_substitution_closed.
Check schema_DiaT_substitution_closed.
Check schema_Ver_substitution_closed.
Check Triv_schema_substitution_closed.
Check KTc_proves_Four.
Check KTc_proves_Five.
Check KTc_proves_DiaT.
Check KTc_prime_proves_Tc.
Check KTc_canonical.
Check Triv_canonical.
Check Ver_canonical.
Check KTc_sound_complete.
Check Triv_sound_complete.
Check Ver_sound_complete.
Check Triv_finite_sound_complete.
Check Ver_finite_sound_complete.
Check Triv_proves_Grz.
Check Ver_proves_bot_of_dia.
Check Ver_proves_Tc.
Check Ver_proves_L.
Check boxdot_Triv_complete_checked.
Check Ver_boxdot_proves_to_Triv_unconditional.
Check Ver_boxdot_iff_Triv_unconditional.
Check KB4_strictly_weaker_KTc.
Check KTc_strictly_weaker_Triv.
Check KTc_strictly_weaker_Ver.
Check GrzPoint3_strictly_weaker_Triv.
Check S4Point4McK_strictly_weaker_Triv.
Check GLPoint3_strictly_weaker_Ver.

(** Modal words, their finite size layers, generic reduction algebra, and
    checked S5 canonical normalization. *)
Check modality_eq_dec.
Check modality_add_assoc.
Check polarity_inv_involutive.
Check modality_add_size.
Check modality_split.
Check modality_split_le.
Check substitute_apply_modality.
Check normal_proves_modality_congruence.
Check modality_translation_of_atom.
Check modality_equivalence_iff_bitranslation.
Check modality_equivalence_expand_left.
Check modalities_all_of_size_iff.
Check modalities_all_of_size_le_iff.
Check modal_reduction_all_of_reducible_to_max.
Check Triv_box_modality_equivalence.
Check S5_canonical_frame_reflexive.
Check S5_canonical_frame_right_euclidean.
Check S5_complete.
Check S5_sound_complete.
Check s5_normalize_mem.
Check s5_normalize_equivalence.
Check s5_modal_reduction.

Check complement_neg.
Check complement_cases.
Check complementary_member_cases.
Check complementary_mem_box.
Check satisfies_complement_incompatible.
Check satisfies_neg_complement_incompatible.

(** Schema-generic finite consistency and complement-complete contexts over
    natural-number atoms. *)
Check finite_consistent_insert_iff.
Check finite_consistent_insert_neg_iff.
Check finite_provable_iff_insert_neg_inconsistent.
Check finite_singleton_complement_consistent_iff_unprovable.
Check finite_singleton_complement_inconsistent_iff_provable.
Check finite_union_consistent_intro.
Check normal_derives_complement_bottom.
Check normal_derives_neg_complement_bottom.
Check normal_derives_of_neg_complement.
Check finite_next_consistent.
Check finite_enumerate_origin.
Check finite_exists_consistent_complementary_closed.
Check fmc_equality_def.
Check finite_context_lindenbaum.
Check fmc_membership_iff_derivable.
Check fmc_mem_top.
Check fmc_bottom_absent.
Check fmc_mem_iff_not_mem_complement.
Check fmc_not_mem_iff_mem_complement.
Check fmc_mem_imp_iff.
Check fmc_not_mem_imp_iff.
Check finite_maximal_context_explicit_cover.

Check complexity_subformula_le.
Check complexity_limited_truth_aux.
Check complexity_limited_truth.
Check complexity_limited_subformula_closed_aux.
Check complexity_limited_subformula_closed.

Check coarsest_filtration_truth.
Check coarsest_filtration_truth_at_class.
Check filtered_world_cover_bound.
Check finite_countermodel.
Check modal_finite_model_property.
Check satisfiable_has_finite_model.
Check not_valid_has_finite_countermodel.

Check finest_filtration_truth.
Check finest_filtration_truth_at_class.
Check finest_filtered_frame_cover_bound.
Check finest_preserves_reflexive.
Check finest_preserves_serial.
Check finest_preserves_symmetric.
Check finest_tc_filtration_truth.
Check finest_tc_filtration_truth_at_class.
Check finest_tc_filtered_frame_cover_bound.
Check finest_tc_is_transitive.
Check finest_tc_preserves_preorder.
Check finest_tc_preserves_equivalence.

Check valid_Geach_atom_iff_geach_convergent.
Check valid_T_iff_reflexive.
Check valid_D_iff_serial.
Check valid_B_iff_symmetric.
Check valid_Four_iff_transitive.
Check valid_Five_iff_right_euclidean.
Check valid_Tc_iff_coreflexive.
Check valid_Point2_iff_strong_confluence.
Check valid_Point3_iff_piecewise_strong_connected.

Check valid_Loeb_atom_iff_transitive_cwf.

Check geach_convergent_four_n_iff_weakly_transitive.
Check valid_FourN_atom_iff_weakly_transitive.
Check valid_Ver_atom_iff_isolated.
Check valid_Point4_atom_iff_sobocinski.
Check valid_McK_of_mckinsey.
Check valid_Mk_of_makinson.
Check detour_free_iff_no_proper_detour.
Check valid_H_atom_iff_detour_free.
Check valid_I_of_transitive_boolos.
Check weak_cwf_iff_cwf_irreflexive_reduction.
Check valid_Grz_atom_iff_reflexive_transitive_weak_cwf.

Check asymmetric_iff_irreflexive_and_antisymmetric.
Check frame_refl_gen_partial_order_of_strict_preorder.
Check frame_trans_gen_equivalence.
Check frame_refl_trans_gen_equivalence.
Check terminated_iff_directly_terminated_of_transitive.
Check terminated_refl_trans_gen_iff.
Check converse_well_founded_iff_well_founded_converse.
Check converse_well_founded_trans_gen_iff.
Check terminated_cwf_target_terminal.

Check frame_root_unique_of_irreflexive_transitive.
Check rooted_point_rooted_of_irreflexive_transitive.
Check trans_rooted_rooted_of_transitive.
Check point_generated_frame_rooted.
Check point_generated_partial_order.
Check point_generated_convergent.
Check generated_submodel_truth.
Check point_generated_truth.
Check point_generated_truth_at_root.
Check point_trans_generated_trans_rooted.
Check point_generated_frame_finite.

Check irreflexivize_irreflexive.
Check irreflexivize_transitive.
Check irreflexivize_piecewise_connected.
Check irreflexivize_reflexive_valid_iff.
Check extend_root_point_rooted.
Check extend_root_transitive.
Check extend_root_embedding_p_morphism.
Check extend_root_embed_rel_iter_iff.
Check extend_root_embedded_truth.
Check extend_root_added_boxdot_truth.
Check extend_root_chain_pairwise.
Check extend_root_finite_cover_exact.
Check extend_root_converse_well_founded.
Check atmost_one_T_failure_on_chain.
Check extend_root_T_conjunction_witness.

Check cluster_of_eq_iff.
Check cluster_shape_trichotomy.
Check skeleton_partial_order.
Check skeleton_finite.
Check bounded_nat_finite_cover.
Check fin_lt_finite.
Check fin_le_finite.
Check nat_lt_validates_Z.
Check nat_le_validates_Dum.
Check trans_tree_is_tree.
Check trans_tree_unravelling_truth_at_root.
Check rank_eq_iff_iter_terminal.
Check rank_lt_iff_satisfies_box_bottom.
Check point_generated_rank_spec.
Check balloon_covers_envelope.
Check source_balloon_order_assumptions_inconsistent.
Check nat_lt_has_no_farthest_bottom.
Check balloon_validates_Z_of_cwf.

Check valid_WeakPoint2_atoms_iff_piecewise_convergent.
Check frame_piecewise_connected_iff_distinct.
Check valid_WeakPoint3_atoms_iff_piecewise_connected.

(** Boxdot's basic semantic laws, K4/S4 equivalence, and Ver/Triv equivalence
    are unconditional.  The remaining named equivalences visibly quantify
    over their still-missing completeness propositions; the Jeřábek results
    additionally quantify over the isolated global-consequence bridge.  These
    are hypotheses in theorem types, not declarations of completeness. *)
Check boxdot_translate.
Check normal_proves_boxdot_translation.
Check iff_boxdotboxdot.
Check boxdot_and.
Check boxdotTranslate_lconj.
Check iff_boxdotTranslateMultibox_boxdotTranslateBoxlt.
Check iff_boxdot_reflexive_closure.
Check iff_frame_boxdot_reflexive_closure.
Check iff_reflexivize_irreflexivize.
Check iff_reflexivize_irreflexivize'.
Check provable_boxdotTranslated_K4_of_provable_S4.
Check provable_S4_iff_boxdotTranslated.
Check provable_S4_of_provable_boxdotTranslated_K4.
Check iff_boxdotTranslatedK4_S4.
Check finite_GL_to_reflexive_closure_finite_Grz.
Check finite_Grz_to_irreflexivize_finite_GL.
Check boxdot_GL_finite_complete.
Check boxdot_Grz_finite_complete.
Check iff_provable_boxdot_GL_provable_Grz.
Check finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3.
Check finite_GrzPoint3_to_irreflexivize_finite_GLPoint3.
Check boxdot_GLPoint3_finite_complete.
Check boxdot_GrzPoint3_finite_complete.
Check iff_boxdotTranslated_GLPoint3_GrzPoint3.
Check provable_boxdotTranslated_Ver_of_Triv.
Check boxdot_Triv_complete.
Check iff_boxdotTranslated_Ver_Triv.
Check boxdot_Triv_complete_checked.
Check iff_boxdotTranslated_Ver_Triv_unconditional.
Check frame_twice.
Check frame_twice_p_morphism.
Check frame_twice_valid_reflects.
Check KT_frameclass_jerabek.
Check KTB_frameclass_jerabek.
Check S4_frameclass_jerabek.
Check S4Point2_frameclass_jerabek.
Check S4Point3_frameclass_jerabek.
Check S5_frameclass_jerabek.
Check atom_flag_boxdot_translated.
Check satisfies_neither_flag.
Check boxdot_preimage.
Check BoxdotProperty.
Check StrongBoxdotProperty.
Check BDP_of_SBDP.
Check jerabek_global_consequence_bridge.
Check jerabek_SBDP.
Check jerabek_BDP.
Check KT_BDP.
Check KTB_BDP.
Check S4_BDP.
Check S4Point2_BDP.
Check S4Point3_BDP.
Check S5_BDP.

Check bisimulation_invariance.
Check p_morphism_truth.
Check valid_of_surjective_p_morphism.
Check irreflexivity_not_modally_definable.

Check standard_translation_correct.
Check standard_translation_model_validity.
Check standard_translation_diamond_is_existential.

(** Constructive semantic kernel and preservation results. *)
Print Assumptions substitute_comp.
Print Assumptions satisfies_substitute.
Print Assumptions valid_K.
Print Assumptions nn_neg_involutive.
Print Assumptions nn_degree_to_formula.
Print Assumptions nn_dnf_part_degree_zero.
Print Assumptions nn_satisfies_atom.
Print Assumptions nn_satisfies_neg.
Print Assumptions nn_to_formula_correct.
Print Assumptions formula_to_nnf_correct.
Print Assumptions formula_nnf_round_trip.
Print Assumptions modal_formula_decode_code.
Print Assumptions modal_formula_enum_surjective.
Print Assumptions nnformula_decode_code.
Print Assumptions nnformula_enum_surjective.
Print Assumptions plon_satisfies_box.
Print Assumptions plon_not_satisfies_box.
Print Assumptions plon_model_valid_elim_contra.
Print Assumptions plon_replacement_of_equivalents_fails.
Print Assumptions plon_frame_class_invalid_iff_model_world.
Print Assumptions plon_soundness_frameclass.
Print Assumptions plon_consistent_of_nonempty_frameclass.
Print Assumptions plon_canonical_truth_lemma.
Print Assumptions plon_complete_of_canonical_frame.
Print Assumptions plon_N_sound_complete.
Print Assumptions plon_N_strictly_weaker_K.
Print Assumptions plon_N_strictly_weaker_EN.
Print Assumptions valid_T_of_reflexive.
Print Assumptions valid_D_of_serial.
Print Assumptions valid_B_of_symmetric.
Print Assumptions valid_Four_of_transitive.
Print Assumptions valid_Five_of_right_euclidean.
Print Assumptions valid_Tc_of_coreflexive.
Print Assumptions valid_Point2_of_strong_confluence.
Print Assumptions bisimulation_invariance.
Print Assumptions valid_of_surjective_p_morphism.
Print Assumptions irreflexivity_not_modally_definable.
Print Assumptions standard_translation_correct.
Print Assumptions standard_translation_model_validity.
Print Assumptions K_proves_substitute.
Print Assumptions K_proves_dne.
Print Assumptions K_derives_deduction_iff.
Print Assumptions theory_consistent_insert_neg_iff.
Print Assumptions K_derives_box_from_unboxed.
Print Assumptions K_proves_sound_on_frame.
Print Assumptions K_derives_sound.
Print Assumptions K_is_consistent.
Print Assumptions lindenbaum_extension.
Print Assumptions canonical_truth_lemma.
Print Assumptions K_complete.
Print Assumptions K_finite_sound_complete.
Print Assumptions normal_proves_substitute.
Print Assumptions normal_proves_sound_on_frame.
Print Assumptions S4_proves_sound_on_preorder_frame.
Print Assumptions S5_proves_sound_on_reflexive_euclidean_frame.
Print Assumptions GL_proves_sound_on_transitive_cwf_frame.
Print Assumptions Grz_proves_sound_on_reflexive_transitive_weak_cwf_frame.
Print Assumptions S4_is_consistent.
Print Assumptions S5_is_consistent.
Print Assumptions GL_is_consistent.
Print Assumptions Grz_is_consistent.
Print Assumptions logic_eq_iff_equiv.
Print Assumptions logic_consistent_iff_exists_unprovable.
Print Assumptions logic_no_bot.
Print Assumptions logic_list_conj_equivalence.
Print Assumptions normal_proves_logic_is_normal.
Print Assumptions normal_logic_contains_K.
Print Assumptions logic_sum_normal_sym.
Print Assumptions logic_sum_quasi_normal_sum_union.
Print Assumptions logic_sum_quasi_normal_iff_finite_provable.
Print Assumptions logic_sum_quasi_normal_iff_finite_provable_letterless.
Print Assumptions logic_sum_quasi_normal_eq_alt.
Print Assumptions logic_sum_quasi_normal_rec_letterless_expansion.
Print Assumptions global_consequence_finite_box_le_provable.
Print Assumptions global_consequence_of_finite_box_le_provable.
Print Assumptions global_consequence_iff_finite_box_le_provable.
Print Assumptions logic_global_foundation_box_le_equivalence.
Print Assumptions global_consequence_iff_finite_foundation_box_le_provable.
Print Assumptions normal_derives_deduction.
Print Assumptions normal_lindenbaum_extension.
Print Assumptions normal_canonical_truth_lemma.
Print Assumptions KT_canonical_frame_reflexive.
Print Assumptions K4_canonical_frame_transitive.
Print Assumptions KT_sound_complete.
Print Assumptions K4_sound_complete.
Print Assumptions S4_sound_complete.
Print Assumptions normal_canonical_serial_of_schema_D.
Print Assumptions normal_canonical_symmetric_of_schema_B.
Print Assumptions normal_canonical_right_euclidean_of_schema_Five.
Print Assumptions KD_sound_complete.
Print Assumptions KB_sound_complete.
Print Assumptions K5_sound_complete.
Print Assumptions normal_proves_P_of_schema_D.
Print Assumptions K_strictly_weaker_KD.
Print Assumptions K_strictly_weaker_KB.
Print Assumptions K_strictly_weaker_K5.
Print Assumptions normal_canonical_transitive_of_schema_Four.
Print Assumptions K45_frame_class_in_K4Point3.
Print Assumptions K45_sound_complete.
Print Assumptions KD4_sound_complete.
Print Assumptions KB5_sound_complete.
Print Assumptions KD45_sound_complete.
Print Assumptions K4Point3_strictly_weaker_K45.
Print Assumptions K5_strictly_weaker_K45.
Print Assumptions K45_strictly_weaker_KB4.
Print Assumptions KD5_strictly_weaker_KD45.
Print Assumptions KTB_schema_substitution_closed.
Print Assumptions KTB_proves_sound_on_frame.
Print Assumptions KTB_canonical.
Print Assumptions KTB_complete.
Print Assumptions KTB_finite_complete.
Print Assumptions KT4B_complete.
Print Assumptions KT4B_finite_complete.
Print Assumptions S5_KT4B_equivalent.
Print Assumptions KT_strictly_weaker_KTB.
Print Assumptions KDB_strictly_weaker_KTB.
Print Assumptions K4Point2_schema_substitution_closed.
Print Assumptions normal_canonical_piecewise_convergent_of_schema_WeakPoint2.
Print Assumptions normal_canonical_strongly_confluent_of_schema_Point2.
Print Assumptions K4Point2_complete.
Print Assumptions S4Point2_complete.
Print Assumptions finest_tc_preserves_piecewise_strongly_convergent.
Print Assumptions S4Point2_finite_complete.
Print Assumptions K4_strictly_weaker_K4Point2.
Print Assumptions K4Point2_strictly_weaker_S4Point2.
Print Assumptions schema_Point3_substitution_closed.
Print Assumptions normal_canonical_piecewise_connected_of_schema_WeakPoint3.
Print Assumptions normal_canonical_piecewise_strongly_connected_of_schema_Point3.
Print Assumptions K4Point3_complete.
Print Assumptions S4Point3_complete.
Print Assumptions S4Point3_linear_preorder_complete.
Print Assumptions finest_tc_preserves_strongly_connected.
Print Assumptions S4Point3_finite_complete.
Print Assumptions K4_strictly_weaker_K4Point3.
Print Assumptions S4Point2_strictly_weaker_S4Point3.
Print Assumptions K4Point3_strictly_weaker_S4Point3.
Print Assumptions S4Point4_axiom_schema_substitution_closed.
Print Assumptions normal_canonical_sobocinski_of_schema_Point4.
Print Assumptions S4Point4_complete.
Print Assumptions S4Point3_weaker_than_S4Point4.
Print Assumptions S4Point3_strictly_weaker_S4Point4.
Print Assumptions valid_on_universal_frames_iff_valid_on_s5_frames.
Print Assumptions S5_universal_complete.
Print Assumptions KTB_strictly_weaker_S5.
Print Assumptions KD45_strictly_weaker_S5.
Print Assumptions KB4_strictly_weaker_S5.
Print Assumptions S4Point4_strictly_weaker_S5.
Print Assumptions S4_strictly_weaker_S5.
Print Assumptions KT_strictly_weaker_S5.
Print Assumptions McK_axiom_schema_substitution_closed.
Print Assumptions normal_proves_base_mck_switch_possible.
Print Assumptions normal_proves_base_mck_jointly_possible.
Print Assumptions base_mck_seed_theory_consistent.
Print Assumptions normal_canonical_mckinsey_of_K4McK_schemas.
Print Assumptions K4McK_complete.
Print Assumptions S4McK_complete.
Print Assumptions K4_strictly_weaker_K4McK.
Print Assumptions S4_strictly_weaker_S4McK.
Print Assumptions K4McK_strictly_weaker_S4McK.
Print Assumptions S4Point2McK_schema_substitution_closed.
Print Assumptions S4Point2McK_canonical_frame.
Print Assumptions S4Point2McK_complete.
Print Assumptions S4McK_strictly_weaker_S4Point2McK.
Print Assumptions S4Point2_strictly_weaker_S4Point2McK.
Print Assumptions S4Point3McK_schema_substitution_closed.
Print Assumptions S4Point3McK_canonical_frame.
Print Assumptions S4Point3McK_complete.
Print Assumptions S4Point2McK_strictly_weaker_S4Point3McK.
Print Assumptions S4Point3_strictly_weaker_S4Point3McK.
Print Assumptions S4Point4McK_canonical_frame.
Print Assumptions S4Point4McK_complete.
Print Assumptions S4Point3McK_strictly_weaker_S4Point4McK.
Print Assumptions S4Point4_strictly_weaker_S4Point4McK.
Print Assumptions schema_DiaT_substitution_closed.
Print Assumptions KTc_proves_DiaT.
Print Assumptions KTc_prime_proves_Tc.
Print Assumptions KTc_complete.
Print Assumptions Triv_complete.
Print Assumptions Ver_complete.
Print Assumptions Triv_finite_complete.
Print Assumptions Ver_finite_complete.
Print Assumptions Triv_proves_Grz.
Print Assumptions Ver_proves_L.
Print Assumptions boxdot_Triv_complete_checked.
Print Assumptions Ver_boxdot_iff_Triv_unconditional.
Print Assumptions KB4_strictly_weaker_KTc.
Print Assumptions KTc_strictly_weaker_Triv.
Print Assumptions KTc_strictly_weaker_Ver.
Print Assumptions GrzPoint3_strictly_weaker_Triv.
Print Assumptions S4Point4McK_strictly_weaker_Triv.
Print Assumptions GLPoint3_strictly_weaker_Ver.
Print Assumptions K_strictly_weaker_KT.
Print Assumptions K_strictly_weaker_K4.
Print Assumptions KT_strictly_weaker_S4.
Print Assumptions K4_strictly_weaker_S4.

(** Modality syntax, size splitting, atom-instance lifting, and the generic
    finite reduction bootstrapping theorem are constructive.  Congruence and
    equivalence formation are routed through checked K completeness and thus
    inherit its classical/definite-description boundary.  S5 canonicality,
    completeness, and normalization inherit the same explicit boundary. *)
Print Assumptions modality_split.
Print Assumptions modality_split_le.
Print Assumptions modality_translation_of_atom.
Print Assumptions modal_reduction_all_of_reducible_to_max.
Print Assumptions normal_proves_modality_congruence.
Print Assumptions S5_canonical_frame_right_euclidean.
Print Assumptions S5_complete.
Print Assumptions s5_normalize_equivalence.
Print Assumptions s5_modal_reduction.
Print Assumptions complement_cases.
Print Assumptions complementary_mem_box.
Print Assumptions satisfies_complement_incompatible.
Print Assumptions normal_derives_complement_bottom.
Print Assumptions normal_derives_neg_complement_bottom.
Print Assumptions normal_derives_of_neg_complement.
Print Assumptions finite_consistent_insert_iff.
Print Assumptions finite_provable_iff_insert_neg_inconsistent.
Print Assumptions finite_singleton_complement_consistent_iff_unprovable.
Print Assumptions fmc_membership_iff_derivable.
Print Assumptions fmc_mem_imp_iff.
Print Assumptions fmc_not_mem_imp_iff.
(** Deterministic extension uses informative excluded middle/classical
    description.  Extensional context equality uses functional and
    propositional extensionality plus proof irrelevance; the explicit cover
    combines those two boundaries. *)
Print Assumptions finite_next_consistent.
Print Assumptions finite_exists_consistent_complementary_closed.
Print Assumptions fmc_equality_def.
Print Assumptions finite_maximal_context_explicit_cover.
(** The complex box laws, primitive evaluation/satisfaction theorem, and
    implication/formula validity characterizations are constructive.  The
    existential diamond dual and derived disjunction/equivalence readings
    expose excluded middle, matching the derived modal syntax. *)
Print Assumptions complex_box_top.
Print Assumptions complex_box_intersection.
Print Assumptions complex_dia_dual.
Print Assumptions algebraic_satisfies.
Print Assumptions algebraic_valid_imp.
Print Assumptions algebraic_valid_iff.
Print Assumptions algebraic_valid.
Print Assumptions complexity_limited_truth_aux.
Print Assumptions complexity_limited_truth.
Print Assumptions complexity_limited_subformula_closed.
Print Assumptions asymmetric_iff_irreflexive_and_antisymmetric.
Print Assumptions frame_refl_gen_partial_order_of_strict_preorder.
Print Assumptions terminated_refl_trans_gen_iff.
Print Assumptions converse_well_founded_iff_well_founded_converse.
Print Assumptions converse_well_founded_trans_gen_iff.
Print Assumptions terminated_cwf_target_terminal.
Print Assumptions valid_FourN_atom_iff_weakly_transitive.
Print Assumptions valid_Ver_atom_iff_isolated.
Print Assumptions valid_Point4_atom_iff_sobocinski.
Print Assumptions valid_McK_of_mckinsey.
Print Assumptions valid_Mk_of_makinson.
Print Assumptions valid_H_atom_iff_detour_free.
Print Assumptions valid_I_of_transitive_boolos.
Print Assumptions valid_Grz_atom_iff_reflexive_transitive_weak_cwf.
Print Assumptions generated_submodel_truth.
Print Assumptions point_generated_truth.
Print Assumptions point_generated_frame_rooted.
Print Assumptions point_trans_generated_trans_rooted.

(** Irreflexivization and the added-root relation algebra, embedding
    p-morphism, embedded-world truth theorem, ordered chain, and exact finite
    cover are constructive.  The reverse reflexivization-validity theorem,
    piecewise-connected inheritance, unique-root selection, and added-root
    boxdot theorem use propositional excluded middle.  Extracting converse
    well-foundedness from finite transitive irreflexivity and the finite-chain
    T witnesses additionally exposes Coq's relational and dependent unique
    choice principles. *)
Print Assumptions irreflexivize_irreflexive.
Print Assumptions irreflexivize_piecewise_connected.
Print Assumptions irreflexivize_reflexive_valid_iff.
Print Assumptions extend_root_embedding_p_morphism.
Print Assumptions extend_root_embed_rel_iter_iff.
Print Assumptions extend_root_embedded_truth.
Print Assumptions extend_root_added_boxdot_truth.
Print Assumptions extend_root_chain_pairwise.
Print Assumptions extend_root_finite_cover_exact.
Print Assumptions finite_transitive_irreflexive_cwf.
Print Assumptions atmost_one_T_failure_on_chain.
Print Assumptions extend_root_T_conjunction_witness.

(** The inductive tree and algebraic rank kernels are constructive.  The
    extensional cluster representation exposes functional/propositional
    extensionality and proof irrelevance; duplicate-free bounded-subtype
    enumeration uses only proof irrelevance.  Filtering a finite cover into a
    point-generated subtype uses informative excluded middle, classical
    description, and proof irrelevance.  Cluster classification, linear-frame
    semantics, and corrected balloon maximality use classical propositional
    logic. *)
Print Assumptions point_generated_frame_finite.
Print Assumptions cluster_shape_trichotomy.
Print Assumptions skeleton_partial_order.
Print Assumptions skeleton_finite.
Print Assumptions bounded_nat_finite_cover.
Print Assumptions nat_lt_validates_Z.
Print Assumptions trans_tree_unravelling_truth_at_root.
Print Assumptions rank_eq_iff_iter_terminal.
Print Assumptions point_generated_rank_spec.
Print Assumptions balloon_covers_envelope.
Print Assumptions farthest_counterexample_of_not_box.
Print Assumptions balloon_validates_Z_of_cwf.

Print Assumptions valid_WeakPoint2_atoms_iff_piecewise_convergent.
Print Assumptions valid_WeakPoint3_atoms_iff_piecewise_connected.

(** The doubled-frame p-morphism is constructive.  Boxdot itself uses the
    classically encoded derived conjunction, so its semantic truth laws expose
    excluded middle.  The nat-atom Hilbert equivalence additionally inherits
    the definite-description boundary of local K completeness.  Reverse
    reflexivization and the logical SBDP argument also use excluded middle.
    Explicit completeness/bridge arguments remain visible in the checked
    theorem types above and are not kernel assumptions. *)
Print Assumptions boxdot_reflexive_closure_truth.
Print Assumptions boxdot_translate_idempotent_truth.
Print Assumptions K4_boxdot_iff_S4.
Print Assumptions finite_GL_to_reflexive_closure_finite_Grz.
Print Assumptions finite_Grz_to_irreflexivize_finite_GL.
Print Assumptions GL_boxdot_iff_Grz.
Print Assumptions finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3.
Print Assumptions GLPoint3_boxdot_iff_GrzPoint3.
Print Assumptions Triv_proves_to_Ver_boxdot.
Print Assumptions Ver_boxdot_iff_Triv.
Print Assumptions Ver_boxdot_iff_Triv_unconditional.
Print Assumptions frame_twice_p_morphism.
Print Assumptions frame_twice_valid_reflects.
Print Assumptions S5_frameclass_jerabek.
Print Assumptions jerabek_SBDP.
Print Assumptions KT_BDP.

(** Filtration's finite list combinatorics is constructive.  Turning
    arbitrary semantic truth into Boolean data, selecting class
    representatives, and identifying subtype proofs are explicitly audited
    below. *)
Print Assumptions subformulas_trans.
Print Assumptions bool_profiles_complete.
Print Assumptions coarsest_filtration_truth.
Print Assumptions filtered_world_cover_bound.
Print Assumptions finite_countermodel.
Print Assumptions modal_finite_model_property.
Print Assumptions satisfiable_has_finite_model.
Print Assumptions finest_filtration_truth.
Print Assumptions finest_filtered_frame_cover_bound.
Print Assumptions finest_tc_filtration_truth.
Print Assumptions finest_tc_filtered_frame_cover_bound.
Print Assumptions finest_tc_preserves_equivalence.

(** Intentional classical boundary: diamond is defined as [~ box ~], so
    extracting witnesses and classical derived connectives uses excluded
    middle. *)
Print Assumptions satisfies_dia_elim.
Print Assumptions valid_Geach_atom_iff_geach_convergent.
Print Assumptions valid_Point3_iff_piecewise_strong_connected.
Print Assumptions valid_Loeb_atom_iff_transitive_cwf.
Print Assumptions standard_translation_diamond_is_existential.
