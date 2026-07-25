(** Public surface and kernel-assumption audit for the Foundation modal port. *)

From FoundationModal Require Import
  Syntax NNFormula FormulaEncoding PLoN Axioms HilbertK PLoNCompleteness Kripke
  NNFormulaSemantics HilbertKSoundness Complement ComplexityLimited Filtration
  Correspondence FiltrationExtensions CanonicalK Loeb FrameProperties
  CorrespondenceExtensions NormalHilbert CanonicalExtensions
  StandardTranslation Preservation Root WeakCorrespondence Undefinability.

Check substitute_comp.
Check satisfies_substitute.
Check valid_K.

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

Check complement_neg.
Check complement_cases.
Check complementary_member_cases.
Check complementary_mem_box.
Check satisfies_complement_incompatible.
Check satisfies_neg_complement_incompatible.

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

Check valid_WeakPoint2_atoms_iff_piecewise_convergent.
Check frame_piecewise_connected_iff_distinct.
Check valid_WeakPoint3_atoms_iff_piecewise_connected.

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
Print Assumptions normal_derives_deduction.
Print Assumptions normal_lindenbaum_extension.
Print Assumptions normal_canonical_truth_lemma.
Print Assumptions KT_canonical_frame_reflexive.
Print Assumptions K4_canonical_frame_transitive.
Print Assumptions KT_sound_complete.
Print Assumptions K4_sound_complete.
Print Assumptions S4_sound_complete.
Print Assumptions K_strictly_weaker_KT.
Print Assumptions K_strictly_weaker_K4.
Print Assumptions KT_strictly_weaker_S4.
Print Assumptions K4_strictly_weaker_S4.
Print Assumptions complement_cases.
Print Assumptions complementary_mem_box.
Print Assumptions satisfies_complement_incompatible.
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
Print Assumptions valid_WeakPoint2_atoms_iff_piecewise_convergent.
Print Assumptions valid_WeakPoint3_atoms_iff_piecewise_connected.

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
