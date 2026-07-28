(** Public surface and kernel-assumption audit for the Foundation modal port. *)

From FoundationModal Require Import
  Syntax NNFormula FormulaEncoding PLoN Axioms HilbertK PLoNCompleteness Kripke
  KripkeAlgebra
  NNFormulaSemantics HilbertKSoundness Complement ComplexityLimited Filtration
  Correspondence FiltrationExtensions CanonicalK Loeb FrameProperties
  CorrespondenceExtensions NormalHilbert LogicInfrastructure CanonicalExtensions
  FiniteMaximalContext Modality CanonicalDB5 StandardTranslation Preservation Root
  FrameTransformations GLGrzDerivations FiniteCanonicalSupport CanonicalGL
  GLUnnecessitation GLModalDisjunction GLIndependence QuasiNormalS QuasiNormalD
  GLPlusBoxBot
  KHenIncompleteness GLAlternativeSystems
  CanonicalGrz StructuralFrames
  WeakCorrespondence CanonicalCombinations KD4Point3Z KTMkFiniteModelFailure
  CanonicalTB Boxdot CanonicalPoint2
  CanonicalPoint3 JerabekBoxdot CanonicalGLPoint3 CanonicalPoint4 CanonicalS4H CanonicalS5 CanonicalMcK
  CanonicalGrzMcK CanonicalTrivVer MaximalTranslations GLPoint3PlusBoxBot CanonicalS5Grz
  CanonicalK4n CanonicalPoint2McK CanonicalGrzPoint2 CanonicalGrzPoint3Strict
  CanonicalPoint3McK CanonicalPoint4McK
  Undefinability.

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

(** Derived GL/Grz proof theory and finite mini-canonical completeness. *)
Check GL_proves_Four.
Check GL_proves_Hen.
Check GL_proves_Z.
Check GL_proves_godel2.
Check GL_proves_boxdot_translated_Grz.
Check Grz_proves_T.
Check Grz_proves_Four.
Check Grz_proves_Dum.
Check GL_mini_canonical_countermodel.
Check GL_finite_sound_complete.
Check GL_sound_complete.
Check GL_unprovable_iff_exists_finite_rooted_countermodel.
Check GL_finite_rooted_sound_complete.
Check imply_boxdot_plain_of_imply_box_box.
Check GL_unnecessitation.
Check logic_unnecessitation.
Check GL_unnecessitation_instance.
Check mdp_counterexample_frame_asymmetric.
Check mdp_counterexample_frame_irreflexive.
Check mdp_counterexample_frame_transitive.
Check mdp_counterexample_frame_point_rooted.
Check mdp_counterexample_frame_finite.
Check mdp_left_p_morphism.
Check mdp_right_p_morphism.
Check mdp_through_original_root.
Check mdp_left_truth.
Check mdp_right_truth.
Check GL_MDP_boxed_antecedent.
Check normal_derives_finite_support.
Check GL_MDP_Aux_finite.
Check GL_MDP_Aux.
Check MDP_Aux.
Check modal_disjunctive.
Check GL_modal_disjunction.
Check GL_modal_disjunctive.
Check GL_modal_disjunctive_instance.
Check independency.
Check higher_independency.
Check higherIndependency.
Check GL_unprovable_notbox.
Check GL_unprovable_independency.
Check GL_proves_box_or_box_neg_of_not_independency.
Check GL_unprovable_not_independency_of_consistency.
Check GL_unprovable_higher_independency_of_consistency.
Check GL_unprovable_not_higher_independency_of_consistency.
(** The least quasinormal extension of GL containing T. *)
Check S_atomic_T_axiom.
Check S_quasi_normal.
Check GL_weaker_than_S.
Check S_proves_atomic_T.
Check S_proves_T.
Check S_proves_substitute.
Check GL_unprovable_atomic_T.
Check GL_strictly_weaker_S.
Check S_derivation_iff.
Check S_proves_induction.
Check S_rec.
(** The quasinormal extension D, its tail semantics, and exact GL
    reduction. *)
Check Dz.
Check D_atomic_axiom.
Check D_proves.
Check D_quasi_normal.
Check GL_weaker_than_D.
Check D_proves_P.
Check D_proves_atomic_Dz.
Check D_proves_Dz.
Check D_proves_substitute.
Check GL_strictly_weaker_D.
Check D_derivation_iff.
Check D_proves_induction.
Check D_rec.
Check D_list_disj.
Check D_boxed_list_disj.
Check D_list_Dz.
Check GL_proves_boxed_list_disj_Four.
Check D_proves_list_Dz.
Check D_proves_C4.
Check D_dz_subformula_list.
Check D_dz_subformula_conj.
Check D_dz_subformula_list_spec.
Check D_proves_dz_subformula_member.
Check D_proves_dz_subformula_conj.
Check D_finite_transitive_irreflexive_cwf.
Check D_tail_rel.
Check D_tail_frame.
Check D_tail_root.
Check D_tail_rooted.
Check D_tail_point_rooted.
Check D_tail_transitive.
Check D_tail_converse_well_founded.
Check D_tail_original_p_morphism.
Check D_tail_original_truth.
Check D_tail_box_from_root.
Check D_tail_extend_root_p_morphism.
Check D_satisfies_valuation_iff.
Check D_tail_extend_root_truth.
Check D_tail_extend_root_original_truth.
Check D_tail_extend_root_nat_truth.
Check D_tail_model_point_rooted.
Check D_T_subformula_list.
Check D_T_subformula_conj.
Check D_tail_nat_subformula_truth.
Check D_tail_valid.
Check D_cwf_tail_valid.
Check D_proves_sound_on_cwf_tail.
Check D_proves_sound_on_tail.
Check D_failed_box_list_spec.
Check D_failed_boxes_have_common_witness.
Check D_point_generated_T_subformula_context.
Check D_tail_reduction_subformula_truth.
Check D_GL_reduction.
Check D_rooted_GL_reduction_valid.
Check D_tail_valid_implies_rooted_GL_reduction_valid.
Check iff_provable_D_provable_GL.
Check D_proves_iff_tail_valid.
Check D_tail_valid_iff_rooted_GL_reduction_valid.
Check D_rooted_GL_reduction_valid_iff_GL_proves.
Check GL_D_TFAE.
Check D_unprovable_T.
Check D_weaker_than_S.
Check D_strictly_weaker_S.
(** The quasi-normal GL plus iterated boxed falsity hierarchy. *)
Check GLPlusBoxBot_axiom.
Check GLPlusBoxBot.
Check GLPlusBoxBot_quasi_normal.
Check GL_weaker_than_GLPlusBoxBot.
Check GLPlusBoxBot_boxbot.
Check substitute_GLPlusBoxBot_axiom.
Check iff_provable_GLPlusBoxBot_provable_GL.
Check eq_GLPlusBoxBot_omega_GL.
Check GL_proves_box_iter_regularity.
Check GL_proves_boxbot_successor.
Check GLPlusBoxBot_weakerThan_succ.
Check GLPlusBoxBot_weakerThan_add.
Check GLPlusBoxBot_weakerThan_lt.
(** Cresswell's KHen model and the resulting Kripke incompleteness. *)
Check schema_Hen_substitution_closed.
Check KHen_proves_substitute.
Check KHen_proves_Hen.
Check K_weaker_than_KHen.
Check KHen_weaker_than_GL.
Check valid_atomic_Hen_of_valid_atomic_Loeb.
Check valid_atomic_Loeb_of_valid_atomic_Hen.
Check valid_atomic_Loeb_iff_valid_atomic_Hen.
Check valid_atomic_Four_of_valid_atomic_Hen.
Check cresswell_sharp_to_flat.
Check cresswell_not_flat_to_sharp.
Check cresswell_sharp_to_sharp.
Check cresswell_flat_to_flat.
Check cresswell_rel_trichotomy.
Check cresswell_not_satisfies_Four_at_two_sharp.
Check cresswell_model_not_valid_Four.
Check cresswell_eventually_true_or_false.
Check eventually_true_has_last_counterexample.
Check counterexample_has_first.
Check cresswell_model_valid_Hen.
Check KHen_proves_valid_on_cresswell_model.
Check KHen_unprovable_atomic_Four.
Check KHen_Kripke_incomplete.
Check K_strictly_weaker_KHen.
Check KHen_strictly_weaker_GL.
(** Equivalent axiom/rule presentations of GL. *)
Check K4Loeb_proves_substitute.
Check K4Loeb_normal_logic.
Check K4Henkin_proves_substitute.
Check K4Henkin_normal_logic.
Check K4Hen_schema_substitution_closed.
Check K4Hen_normal_logic.
Check K4_proves_box_L_implies_L.
Check K4Loeb_proves_L.
Check K4Henkin_loeb_rule.
Check K4Henkin_proves_L.
Check K4Hen_henkin_rule.
Check K4Hen_loeb_rule.
Check K4Hen_proves_L.
Check GL_loeb_rule.
Check GL_henkin_rule.
Check provable_GL_K4Loeb_iff.
Check provable_GL_K4Henkin_iff.
Check provable_GL_K4Hen_iff.
Check provable_GL_TFAE.
Check GL_equiv_K4Loeb.
Check GL_equiv_K4Henkin.
Check GL_equiv_K4Hen.
(** Maximal Triv/Ver translations and their classical cores. *)
Check triv_translate.
Check ver_translate.
Check triv_translate_degree_zero.
Check ver_translate_degree_zero.
Check triv_translate_toIP_eq.
Check ver_translate_toIP_eq.
Check triv_translate_truth_on_Triv_frame.
Check ver_translate_truth_on_Ver_frame.
Check normal_proves_of_classical_tautology.
Check Triv_proves_iff_triv_translate.
Check Ver_proves_iff_ver_translate.
Check Triv_proves_iff_classical_tautology.
Check Ver_proves_iff_classical_tautology.
Check Triv_iff_trivTranslated.
Check Triv_iff_provable_Cl.
Check Triv_iff_tautology.
Check Ver_iff_verTranslated.
Check Ver_iff_provable_Cl.
Check Ver_iff_tautology.
Check Triv_unprovable_atomic_L.
Check Ver_unprovable_P.
Check K4_proves_triv_translate_classical_tautology.
Check GL_proves_ver_translate_classical_tautology.
Check K4_unprovable_AxiomL.
Check GL_unprovable_AxiomT.
Check K4_unprovable_atomic_L.
Check K4_strictly_weaker_GL.
Check not_S4_weakerThan_GL.
Check grz_mini_countermodel.
Check Grz_finite_sound_complete.
Check Grz_sound_complete.
Check finite_partial_order_mckinsey.
Check S4McK_weaker_than_Grz.
Check grz_mck_three_not_valid_Grz_atom.
Check S4McK_strictly_weaker_Grz.
Check S4_strictly_weaker_Grz.

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
Check K4_finite_sound_complete.
Check S4_finite_sound_complete.
Check K_strictly_weaker_KT.
Check K_strictly_weaker_K4.
Check KT_strictly_weaker_S4.
Check K4_strictly_weaker_S4.
Check KD_weaker_than_KT.
Check KD_strictly_weaker_KT.
Check KD4_weaker_than_S4.
Check KD_weaker_than_S4.
Check KD4_strictly_weaker_S4.
Check KD_strictly_weaker_S4.

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

(** KD4.3Z soundness and consistency on the strict natural frame. *)
Check schema_Z.
Check schema_Z_substitution_closed.
Check KD4Point3Z_schema_substitution_closed.
Check KD4Point3Z_frame_class.
Check KD4Point3Z_schema_valid_on_frame.
Check KD4Point3Z_proves_sound_on_frame.
Check schema_Z_valid_on_nat_lt.
Check nat_lt_is_KD4Point3Z_frame.
Check KD4Point3Z_proves_sound_on_nat_lt.
Check KD4Point3Z_is_consistent.

(** KTMk's finite-model collapse, recession countermodel, and strict
    KT--KTMk--S4 hierarchy. *)
Check Mk_axiom_schema_substitution_closed.
Check KTMk_schema_substitution_closed.
Check KTMk_frame_class.
Check KTMk_proves_sound_on_frame.
Check KTMk_proves_sound_on_class.
Check KTMk_is_consistent.
Check KTMk_model_valid_T.
Check KTMk_model_valid_Mk.
Check KTMk_model_box_level_step.
Check KTMk_box_levels_distinct.
Check KTMk_validate_Four_of_finite_model.
Check KTMk_finite_frame_valid_Four.
Check KTMk_finite_frame_transitive.
Check KTMk_model_infinite_of_not_Four.
Check recession_frame_is_KTMk.
Check recession_frame_not_transitive.
Check recession_frame_not_valid_Four_atom.
Check KTMk_exists_unprovable_Four.
Check KTMk_no_finite_model_property.
Check KTMk_non_theorem_valid_in_every_finite_model.
Check KT_strictly_weaker_KTMk.
Check KTMk_strictly_weaker_S4.

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

(** Selective finite canonical completeness for GL.3, its exact connected
    and piecewise-connected finite semantics, Boxdot specialization, and
    both strict predecessors. *)
Check GLPoint3_schema_substitution_closed.
Check GLPoint3_finite_frame_class.
Check GLPoint3_finite_piecewise_frame_class.
Check GLPoint3_proves_sound_on_transitive_cwf_piecewise_frame.
Check GLPoint3_unprovable_exists_finite_connected_countermodel.
Check GLPoint3_finite_sound_complete.
Check GLPoint3_finite_piecewise_sound_complete.
Check boxdot_GLPoint3_finite_complete_checked.
Check GLPoint3_proves_boxdot_Grz_axiom_unconditional.
Check GLPoint3_proves_boxdot_Point3_axiom_unconditional.
Check GrzPoint3_proves_to_GLPoint3_boxdot_unconditional.
Check GLPoint3_boxdot_iff_GrzPoint3_from_Grz_finite_completeness.
Check GL_strictly_weaker_GLPoint3.
Check K4Point3_strictly_weaker_GLPoint3.

(** The normal GL.3 plus iterated boxed-falsity hierarchy, including its
    first three exact stages. *)
Check GLPoint3PlusBoxBot_normal.
Check GLPoint3_weaker_than_GLPoint3PlusBoxBot.
Check GLPoint3PlusBoxBot_boxbot.
Check GLPoint3PlusBoxBot_axiomNVer.
Check iff_provable_GLPoint3PlusBoxBot_provable_GLPoint3.
Check eq_GLPoint3PlusBoxBot_omega_GLPoint3.
Check GLPoint3PlusBoxBot_weakerThan_succ.
Check GLPoint3PlusBoxBot_weakerThan_add.
Check GLPoint3PlusBoxBot_weakerThan_lt.
Check GLPoint3PlusBoxBot_strictlyWeakerThan_GLPoint3.
Check eq_GLPoint3PlusBoxBot_0_full.
Check eq_GLPoint3PlusBoxBot_1_Ver.
Check GLPoint2_schema_substitution_closed.
Check GLPoint2_normal_logic.
Check GLPoint2_provable_boxboxbot.
Check GLPoint2_provable_dia_boxdot_implies_box.
Check GLPoint2_provable_WeakPoint3.
Check GLPoint3PlusBoxBot_provable_WeakPoint2_in_2.
Check GLPoint2_weaker_than_GLPoint3PlusBoxBot_2.
Check GLPoint3_weaker_than_GLPoint2.
Check GLPoint3PlusBoxBot_2_weaker_than_GLPoint2.
Check eq_GLPoint3PlusBoxBot_2_GLPoint2.

(** Finite Grz.2 completeness and the complete proved Grz.3 surface.  The
    pinned Grz.3 completeness declaration is admitted upstream and is
    deliberately not reproduced here. *)
Check finite_frame_exists_nonempty_cover.
Check frame_exists_reflexive_terminal.
Check satisfies_box_at_reflexive_terminal.
Check GrzPoint2_schema_substitution_closed.
Check GrzPoint2_finite_frame_class.
Check GrzPoint2_finite_frame_is_S4Point2McK.
Check grzpoint2_root_atom_agreement.
Check grzpoint2_terminal_top_truth.
Check grzpoint2_adjoin_terminal_truth.
Check GrzPoint2_finite_sound_complete.
Check Grz_strictly_weaker_GrzPoint2.
Check S4Point2McK_strictly_weaker_GrzPoint2.
Check S4Point2_strictly_weaker_GrzPoint2.
Check GrzPoint3_finite_frame_class.
Check GrzPoint3_finite_frame_class'.
Check GrzPoint3_finite_frame_is_GrzPoint2.
Check GrzPoint3_proves_sound_on_finite_strong_frame.
Check GrzPoint3_proves_sound_on_finite_piecewise_strong_frame.
Check GrzPoint3_is_consistent.
Check GrzPoint2_weaker_than_GrzPoint3.
Check GrzPoint2_strictly_weaker_GrzPoint3.
Check S4Point3_strictly_weaker_GrzPoint3.

(** Canonical weak-n transitivity and the infinite strict K4n hierarchy. *)
Check schema_FourN_substitution_closed.
Check normal_canonical_rel_iter_iff_box_iter.
Check normal_canonical_weakly_transitive_of_schema_FourN.
Check K4n_canonical_frame.
Check K4n_sound_complete.
Check K4n_frame_class_zero_iff_KTc.
Check K4n_frame_class_one_iff_transitive.
Check K4n_zero_equiv_KTc.
Check K4n_one_equiv_K4.
Check k4n_counter_rel_iter_iff.
Check K_strictly_weaker_K4n.
Check K4n_strictly_weaker_of_lt.
Check K4n_family_pairwise_inequivalent.
Check K4n_family_injective.

(** Generic H canonicality, canonical S4H completeness, and the proved
    Grz-to-S4H strict comparison. *)
Check schema_H_substitution_closed.
Check schema_H_normal_proves_sound_on_frame.
Check schema_H_is_consistent.
Check point_generated_detour_free.
Check detour_free_weak_converse_well_founded.
Check normal_canonical_detour_free_of_schema_H.
Check S4H_canonical_frame.
Check S4H_sound_complete.
Check finite_S4H_frame_is_finite_Grz_frame.
Check Grz_weaker_than_S4H.
Check Grz_strictly_weaker_S4H.

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
Check normal_proves_base_mck_axiom_to_switch_possible.
Check normal_proves_base_mck_switch_possible_to_axiom.
Check normal_proves_base_mck_axiom_switch_iff.
Check normal_proves_base_mck_switch_possible.
Check normal_proves_base_mck_dia_box_to_dia_and.
Check normal_proves_base_mck_dia_box_elim.
Check normal_proves_base_mck_box_dia_elim.
Check normal_proves_base_mck_jointly_possible.
Check normal_proves_base_mck_nonempty_list_jointly_possible.
Check normal_proves_base_mck_switch_list_conjunction_possible.
Check base_mck_switch_finset_conjunction.
Check normal_proves_base_mck_switch_finset_conjunction_possible.
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
Check normal_canonical_isolated_of_schema_Ver.
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

(** S5 plus Grzegorczyk collapses proof-theoretically to Triv. *)
Check S5Grz_schema_substitution_closed.
Check S5Grz_proves_substitute.
Check S5Grz_proves_T.
Check S5Grz_proves_Five.
Check S5Grz_proves_Grz.
Check S5_weaker_than_S5Grz.
Check Grz_weaker_than_S5Grz.
Check S5_proves_dia_box_to_box.
Check S5Grz_proves_DiaT.
Check S5Grz_proves_Tc.
Check KTc_weaker_than_S5Grz.
Check S5Grz_proves_sound_on_Triv_frame.
Check S5Grz_proves_sound_on_finite_Triv_frame.
Check S5Grz_is_consistent.
Check S5Grz_weaker_than_Triv.
Check Triv_weaker_than_S5Grz.
Check S5Grz_Triv_provable_iff.
Check S5Grz_equiv_Triv.
Check S5Grz_finite_Triv_sound.
Check S5_strictly_weaker_S5Grz.
Check Grz_strictly_weaker_S5Grz.
Check S4_strictly_weaker_Triv.

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
Check formula_list_unbox_spec.
Check formula_list_box_spec.
Check normal_derives_finite_context_cut.
Check fmc_relevant_boxed_spec_closed.
Check fmc_equality_on_base.
Check grz_subformulas_generated.

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
Check finest_tc_filtered_rel_of_representatives.
Check finest_tc_filtered_rel_to_profile_class.
Check finest_tc_preserves_strongly_convergent.
Check FiltrationExtensions.finest_tc_preserves_strongly_connected.
Check finest_tc_point_generated_preserves_piecewise_strongly_convergent.
Check finest_tc_point_generated_preserves_piecewise_strongly_connected.
Check finest_tc_rooted_is_piecewise_strongly_convergent.
Check finest_tc_rooted_is_piecewise_strongly_connected.

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
Check finite_transitive_irreflexive_cwf.
Check valid_Loeb_of_finite_transitive_irreflexive.

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
Check finite_transitive_antisymmetric_weak_cwf.
Check valid_Grz_of_finite_partial_order.
Check valid_Grz_atom_of_finite_partial_order.
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
Check generated_submodel_of_atomic.
Check generated_submodel_p_morphism.
Check generated_submodel_truth.
Check generated_submodel_modal_equivalence.
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

(** Boxdot's basic semantic laws and K4/S4, GL/Grz, Ver/Triv, and Jeřábek
    results are unconditional.  The GL.3/Grz.3 results still expose their
    remaining Grz.3 completeness input. *)
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
Check boxdot_GL_finite_complete_checked.
Check boxdot_Grz_finite_complete_checked.
Check iff_provable_boxdot_GL_provable_Grz.
Check finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3.
Check finite_GrzPoint3_to_irreflexivize_finite_GLPoint3.
Check boxdot_GLPoint3_finite_complete.
Check boxdot_GrzPoint3_finite_complete.
Check boxdot_GLPoint3_finite_complete_checked.
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
Check jerabek_fresh_atom_not_subformula.
Check jerabek_context_spec.
Check boxdot_translate_logic_list_conj2.
Check boxdot_translate_box_iter_global.
Check jerabek_global_boxdot_T.
Check jerabek_subformula_boxdot_equiv.
Check jerabek_global_boxdot_target.
Check jerabek_doubled_subformula_truth.
Check jerabek_doubled_context_true.
Check jerabek_counterexample_lift.
Check jerabek_global_consequence_bridge_checked.
Check jerabek_SBDP_unconditional.
Check jerabek_BDP_unconditional.
Check KT_logic_complete_jerabek.
Check KTB_logic_complete_jerabek.
Check S4_logic_complete_jerabek.
Check S4Point2_logic_complete_jerabek.
Check S4Point3_logic_complete_jerabek.
Check S5_logic_complete_jerabek.
Check KT_BDP_unconditional.
Check boxdot_conjecture_unconditional.
Check KTB_BDP_unconditional.
Check S4_BDP_unconditional.
Check S4Point2_BDP_unconditional.
Check S4Point3_BDP_unconditional.
Check S5_BDP_unconditional.

Check bisimulation_invariance.
Check modal_equivalent_of_bisimilar.
Check modal_equivalent_symmetry.
Check p_morphism_id.
Check p_morphism_comp.
Check p_morphism_transitive_closure.
Check p_morphism_rel_iff_of_injective.
Check p_morphism_rel_iter_iff_of_injective.
Check p_morphism_truth.
Check model_p_morphism_id.
Check model_p_morphism_comp.
Check model_p_morphism_bisimulation.
Check model_p_morphism_modal_equivalence.
Check model_p_morphism_truth.
Check valid_of_surjective_p_morphism.
Check validates_predicate_of_surjective_p_morphism.
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
Print Assumptions p_morphism_transitive_closure.
Print Assumptions p_morphism_rel_iff_of_injective.
Print Assumptions p_morphism_rel_iter_iff_of_injective.
Print Assumptions model_p_morphism_modal_equivalence.
Print Assumptions valid_of_surjective_p_morphism.
Print Assumptions validates_predicate_of_surjective_p_morphism.
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
Print Assumptions GL_proves_Four.
Print Assumptions GL_proves_godel2.
Print Assumptions GL_proves_boxdot_translated_Grz.
Print Assumptions Grz_proves_T_and_Four.
Print Assumptions Grz_proves_Dum.
Print Assumptions GL_mini_canonical_countermodel.
Print Assumptions GL_finite_sound_complete.
Print Assumptions GL_sound_complete.
Print Assumptions GL_unprovable_iff_exists_finite_rooted_countermodel.
Print Assumptions imply_boxdot_plain_of_imply_box_box.
Print Assumptions GL_unnecessitation.
Print Assumptions mdp_left_p_morphism.
Print Assumptions mdp_left_truth.
Print Assumptions normal_derives_finite_support.
Print Assumptions GL_MDP_boxed_antecedent.
Print Assumptions GL_MDP_Aux.
Print Assumptions GL_modal_disjunction.
Print Assumptions GL_unprovable_notbox.
Print Assumptions GL_unprovable_independency.
Print Assumptions GL_unprovable_not_independency_of_consistency.
Print Assumptions GL_unprovable_higher_independency_of_consistency.
Print Assumptions GL_unprovable_not_higher_independency_of_consistency.
Print Assumptions S_quasi_normal.
Print Assumptions S_proves_T.
Print Assumptions GL_unprovable_atomic_T.
Print Assumptions GL_strictly_weaker_S.
Print Assumptions S_derivation_iff.
Print Assumptions S_proves_induction.
Print Assumptions D_proves_Dz.
Print Assumptions GL_strictly_weaker_D.
Print Assumptions D_derivation_iff.
Print Assumptions D_proves_induction.
Print Assumptions GL_proves_boxed_list_disj_Four.
Print Assumptions D_proves_list_Dz.
Print Assumptions D_proves_C4.
Print Assumptions D_dz_subformula_list_spec.
Print Assumptions D_proves_dz_subformula_conj.
Print Assumptions D_tail_transitive.
Print Assumptions D_tail_converse_well_founded.
Print Assumptions D_tail_original_truth.
Print Assumptions D_tail_extend_root_truth.
Print Assumptions D_tail_nat_subformula_truth.
Print Assumptions D_proves_sound_on_cwf_tail.
Print Assumptions D_proves_sound_on_tail.
Print Assumptions D_failed_boxes_have_common_witness.
Print Assumptions D_tail_reduction_subformula_truth.
Print Assumptions iff_provable_D_provable_GL.
Print Assumptions GL_D_TFAE.
Print Assumptions D_unprovable_T.
Print Assumptions D_weaker_than_S.
Print Assumptions D_strictly_weaker_S.
Print Assumptions GLPlusBoxBot_quasi_normal.
Print Assumptions iff_provable_GLPlusBoxBot_provable_GL.
Print Assumptions GL_proves_boxbot_successor.
Print Assumptions GLPlusBoxBot_weakerThan_succ.
Print Assumptions GLPlusBoxBot_weakerThan_add.
Print Assumptions GLPlusBoxBot_weakerThan_lt.
Print Assumptions valid_atomic_Loeb_iff_valid_atomic_Hen.
Print Assumptions valid_atomic_Four_of_valid_atomic_Hen.
Print Assumptions cresswell_eventually_true_or_false.
Print Assumptions cresswell_model_valid_Hen.
Print Assumptions KHen_proves_valid_on_cresswell_model.
Print Assumptions KHen_unprovable_atomic_Four.
Print Assumptions KHen_Kripke_incomplete.
Print Assumptions K_strictly_weaker_KHen.
Print Assumptions KHen_strictly_weaker_GL.
Print Assumptions K4_proves_box_L_implies_L.
Print Assumptions K4Loeb_proves_L.
Print Assumptions K4Henkin_loeb_rule.
Print Assumptions K4Hen_henkin_rule.
Print Assumptions provable_GL_TFAE.
Print Assumptions GL_equiv_K4Loeb.
Print Assumptions GL_equiv_K4Henkin.
Print Assumptions GL_equiv_K4Hen.
Print Assumptions triv_translate_degree_zero.
Print Assumptions Triv_proves_iff_triv_translate.
Print Assumptions Ver_proves_iff_ver_translate.
Print Assumptions normal_proves_of_classical_tautology.
Print Assumptions Triv_proves_iff_classical_tautology.
Print Assumptions Ver_proves_iff_classical_tautology.
Print Assumptions Triv_unprovable_atomic_L.
Print Assumptions Ver_unprovable_P.
Print Assumptions K4_proves_triv_translate_classical_tautology.
Print Assumptions GL_proves_ver_translate_classical_tautology.
Print Assumptions K4_unprovable_AxiomL.
Print Assumptions GL_unprovable_AxiomT.
Print Assumptions K4_unprovable_atomic_L.
Print Assumptions K4_strictly_weaker_GL.
Print Assumptions not_S4_weakerThan_GL.
Print Assumptions Grz_finite_sound_complete.
Print Assumptions Grz_sound_complete.
Print Assumptions finite_partial_order_mckinsey.
Print Assumptions grz_mck_three_in_S4McK_frame_class.
Print Assumptions grz_mck_three_not_valid_Grz_atom.
Print Assumptions S4McK_weaker_than_Grz.
Print Assumptions S4McK_strictly_weaker_Grz.
Print Assumptions S4_strictly_weaker_Grz.
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
Print Assumptions K4_finite_complete.
Print Assumptions S4_finite_complete.
Print Assumptions KD_strictly_weaker_KT.
Print Assumptions KD4_strictly_weaker_S4.
Print Assumptions KD_strictly_weaker_S4.
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
Print Assumptions schema_Z_valid_on_nat_lt.
Print Assumptions KD4Point3Z_proves_sound_on_nat_lt.
Print Assumptions KD4Point3Z_is_consistent.
Print Assumptions KTMk_proves_sound_on_frame.
Print Assumptions KTMk_is_consistent.
Print Assumptions KTMk_model_box_level_step.
Print Assumptions KTMk_validate_Four_of_finite_model.
Print Assumptions KTMk_finite_frame_transitive.
Print Assumptions KTMk_exists_unprovable_Four.
Print Assumptions KTMk_no_finite_model_property.
Print Assumptions KT_strictly_weaker_KTMk.
Print Assumptions KTMk_strictly_weaker_S4.
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
Print Assumptions GLPoint3_schema_substitution_closed.
Print Assumptions glpoint3_terminal_successor_unique.
Print Assumptions glpoint3_filtered_truth_lemma.
Print Assumptions GLPoint3_finite_complete.
Print Assumptions GLPoint3_finite_piecewise_complete.
Print Assumptions boxdot_GLPoint3_finite_complete_checked.
Print Assumptions GrzPoint3_proves_to_GLPoint3_boxdot_unconditional.
Print Assumptions GLPoint3_boxdot_iff_GrzPoint3_from_Grz_finite_completeness.
Print Assumptions GL_strictly_weaker_GLPoint3.
Print Assumptions K4Point3_strictly_weaker_GLPoint3.
Print Assumptions GLPoint3PlusBoxBot_normal.
Print Assumptions iff_provable_GLPoint3PlusBoxBot_provable_GLPoint3.
Print Assumptions GLPoint3PlusBoxBot_strictlyWeakerThan_GLPoint3.
Print Assumptions eq_GLPoint3PlusBoxBot_0_full.
Print Assumptions eq_GLPoint3PlusBoxBot_1_Ver.
Print Assumptions GLPoint2_provable_boxboxbot.
Print Assumptions GLPoint2_provable_WeakPoint3.
Print Assumptions GLPoint3PlusBoxBot_provable_WeakPoint2_in_2.
Print Assumptions eq_GLPoint3PlusBoxBot_2_GLPoint2.
Print Assumptions GrzPoint2_schema_substitution_closed.
Print Assumptions GrzPoint2_proves_sound_on_finite_frame.
Print Assumptions grzpoint2_root_atom_agreement.
Print Assumptions grzpoint2_terminal_top_truth.
Print Assumptions grzpoint2_adjoin_terminal_truth.
Print Assumptions GrzPoint2_finite_complete.
Print Assumptions Grz_strictly_weaker_GrzPoint2.
Print Assumptions S4Point2McK_strictly_weaker_GrzPoint2.
Print Assumptions S4Point2_strictly_weaker_GrzPoint2.
Print Assumptions GrzPoint3_finite_frame_is_GrzPoint2.
Print Assumptions GrzPoint3_proves_sound_on_finite_strong_frame.
Print Assumptions GrzPoint3_is_consistent.
Print Assumptions GrzPoint2_weaker_than_GrzPoint3.
Print Assumptions GrzPoint2_strictly_weaker_GrzPoint3.
Print Assumptions S4Point3_strictly_weaker_GrzPoint3.
Print Assumptions schema_FourN_substitution_closed.
Print Assumptions normal_canonical_rel_iter_iff_box_iter.
Print Assumptions normal_canonical_weakly_transitive_of_schema_FourN.
Print Assumptions K4n_complete.
Print Assumptions K4n_zero_equiv_KTc.
Print Assumptions K4n_one_equiv_K4.
Print Assumptions K_strictly_weaker_K4n.
Print Assumptions K4n_strictly_weaker_of_lt.
Print Assumptions K4n_family_injective.
Print Assumptions schema_H_substitution_closed.
Print Assumptions schema_H_normal_proves_sound_on_frame.
Print Assumptions schema_H_is_consistent.
Print Assumptions point_generated_detour_free.
Print Assumptions detour_free_weak_converse_well_founded.
Print Assumptions normal_canonical_detour_free_of_schema_H.
Print Assumptions S4H_complete.
Print Assumptions finite_S4H_frame_is_finite_Grz_frame.
Print Assumptions Grz_weaker_than_S4H.
Print Assumptions Grz_strictly_weaker_S4H.
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
Print Assumptions normal_proves_base_mck_axiom_switch_iff.
Print Assumptions normal_proves_base_mck_switch_possible.
Print Assumptions normal_proves_base_mck_dia_box_elim.
Print Assumptions normal_proves_base_mck_box_dia_elim.
Print Assumptions normal_proves_base_mck_jointly_possible.
Print Assumptions normal_proves_base_mck_nonempty_list_jointly_possible.
Print Assumptions normal_proves_base_mck_switch_list_conjunction_possible.
Print Assumptions normal_proves_base_mck_switch_finset_conjunction_possible.
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
Print Assumptions normal_canonical_isolated_of_schema_Ver.
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
(** S5Grz's DiaT/Tc collapse inherits only the established classical S5
    completeness boundary; the direct frame soundness and finite separators
    expose no project-local assumptions. *)
Print Assumptions S5Grz_proves_DiaT.
Print Assumptions S5Grz_proves_Tc.
Print Assumptions S5Grz_equiv_Triv.
Print Assumptions S5Grz_proves_sound_on_finite_Triv_frame.
Print Assumptions S5Grz_is_consistent.
Print Assumptions S5_strictly_weaker_S5Grz.
Print Assumptions Grz_strictly_weaker_S5Grz.
Print Assumptions S4_strictly_weaker_Triv.
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
Print Assumptions normal_derives_finite_context_cut.
Print Assumptions fmc_relevant_boxed_spec_closed.
Print Assumptions fmc_equality_on_base.
Print Assumptions grz_subformulas_generated.
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
Print Assumptions valid_Loeb_of_finite_transitive_irreflexive.
Print Assumptions finite_transitive_antisymmetric_weak_cwf.
Print Assumptions valid_Grz_of_finite_partial_order.
Print Assumptions valid_Grz_atom_iff_reflexive_transitive_weak_cwf.
Print Assumptions generated_submodel_p_morphism.
Print Assumptions generated_submodel_truth.
Print Assumptions generated_submodel_modal_equivalence.
Print Assumptions point_generated_truth.
Print Assumptions point_generated_frame_rooted.
Print Assumptions point_trans_generated_trans_rooted.

(** Irreflexivization, the finite strict-order maximal-element construction,
    and the added-root relation algebra, embedding
    p-morphism, embedded-world truth theorem, ordered chain, and exact finite
    cover are constructive.  The reverse reflexivization-validity theorem,
    piecewise-connected inheritance, finite maximal-element selection,
    unique-root selection, and added-root boxdot theorem use propositional
    excluded middle.  The finite-chain T witnesses additionally expose Coq's
    relational and dependent unique-choice principles. *)
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
    GL/Grz and GL.3 completeness are now checked above.  The remaining Grz.3
    argument stays visible in its theorem type.  Jeřábek's discharged bridge
    uses the global-consequence and filtration boundaries audited below. *)
Print Assumptions boxdot_reflexive_closure_truth.
Print Assumptions boxdot_translate_idempotent_truth.
Print Assumptions K4_boxdot_iff_S4.
Print Assumptions finite_GL_to_reflexive_closure_finite_Grz.
Print Assumptions finite_Grz_to_irreflexivize_finite_GL.
Print Assumptions boxdot_GL_finite_complete_checked.
Print Assumptions boxdot_Grz_finite_complete_checked.
Print Assumptions GL_boxdot_iff_Grz.
Print Assumptions finite_GLPoint3_to_reflexive_closure_finite_GrzPoint3.
Print Assumptions boxdot_GLPoint3_finite_complete_checked.
Print Assumptions GLPoint3_boxdot_iff_GrzPoint3.
Print Assumptions Triv_proves_to_Ver_boxdot.
Print Assumptions Ver_boxdot_iff_Triv.
Print Assumptions Ver_boxdot_iff_Triv_unconditional.
Print Assumptions frame_twice_p_morphism.
Print Assumptions frame_twice_valid_reflects.
Print Assumptions S5_frameclass_jerabek.
Print Assumptions jerabek_SBDP.
Print Assumptions KT_BDP.
Print Assumptions jerabek_doubled_subformula_truth.
Print Assumptions jerabek_counterexample_lift.
Print Assumptions jerabek_global_consequence_bridge_checked.
Print Assumptions jerabek_SBDP_unconditional.
Print Assumptions jerabek_BDP_unconditional.
Print Assumptions KT_logic_complete_jerabek.
Print Assumptions S5_logic_complete_jerabek.
Print Assumptions KT_BDP_unconditional.
Print Assumptions S5_BDP_unconditional.

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
Print Assumptions finest_tc_preserves_strongly_convergent.
Print Assumptions FiltrationExtensions.finest_tc_preserves_strongly_connected.
Print Assumptions
  finest_tc_point_generated_preserves_piecewise_strongly_convergent.
Print Assumptions
  finest_tc_point_generated_preserves_piecewise_strongly_connected.

(** Intentional classical boundary: diamond is defined as [~ box ~], so
    extracting witnesses and classical derived connectives uses excluded
    middle. *)
Print Assumptions satisfies_dia_elim.
Print Assumptions valid_Geach_atom_iff_geach_convergent.
Print Assumptions valid_Point3_iff_piecewise_strong_connected.
Print Assumptions valid_Loeb_atom_iff_transitive_cwf.
Print Assumptions standard_translation_diamond_is_existential.
