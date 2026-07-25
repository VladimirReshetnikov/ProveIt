(** Public surface and kernel-assumption audit for the Foundation modal port. *)

From FoundationModal Require Import
  Syntax NNFormula Axioms HilbertK Kripke NNFormulaSemantics
  HilbertKSoundness Complement ComplexityLimited Filtration Correspondence
  FiltrationExtensions Loeb FrameProperties StandardTranslation Preservation
  Undefinability.

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

Check asymmetric_iff_irreflexive_and_antisymmetric.
Check frame_refl_gen_partial_order_of_strict_preorder.
Check frame_trans_gen_equivalence.
Check frame_refl_trans_gen_equivalence.
Check terminated_iff_directly_terminated_of_transitive.
Check terminated_refl_trans_gen_iff.
Check converse_well_founded_iff_well_founded_converse.
Check converse_well_founded_trans_gen_iff.
Check terminated_cwf_target_terminal.

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
