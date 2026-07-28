(** Public surface and kernel-assumption audit for the Foundation modal port. *)

From FoundationModal Require Import
  Syntax NNFormula FormulaEncoding PLoN Axioms HilbertK PLoNCompleteness Kripke
  KripkeAlgebra ModalAlgebra CoherenceSpace CoherenceStableFunction
  NNFormulaSemantics HilbertKSoundness Complement ComplexityLimited Filtration
  Correspondence FiltrationExtensions CanonicalK HilbertNNFormula Loeb
  FrameProperties
  RelationProperties ConverseWellFounded WeakConverseWellFounded
  CorrespondenceExtensions NormalHilbert LogicInfrastructure
  HilbertAxiom EntailmentExtensions EntailmentNamedExtensions EntailmentKT EntailmentS4
  EntailmentS5 HilbertWithRE HilbertNormal HilbertNormalAxiomAdapters
  HilbertNormalBaseSystems HilbertNormalClassicalBaseSystems
  HilbertNormalTransitiveBaseSystems HilbertNormalMcKSystems
  HilbertNormalK4PointSystems HilbertNormalMixedSystems
  HilbertNormalD45SymmetricSystems HilbertNormalS4Systems
  HilbertNormalS4PointMcKSystems HilbertNormalFiveSystems
  HilbertWithHenkin HilbertWithLoeb
  HilbertWithREClassicalCompleteness HilbertWithREBaseSystems
  HilbertWithREUnarySystems HilbertWithRETKSystems HilbertWithREFourSystems
  HilbertWithRESystems HilbertWithRESymmetrySystems
  HilbertWithRENormal HilbertWithREEquivalences
  KripkeSemantics KripkeHilbert CanonicalExtensions
  FiniteMaximalContext Modality CanonicalDB5 StandardTranslation Preservation Root
  FrameTransformations GLGrzDerivations FiniteCanonicalSupport CanonicalGL
  GLUnnecessitation GLModalDisjunction GLIndependence QuasiNormalS QuasiNormalD
  GLPlusBoxBot
  KHenIncompleteness GLAlternativeSystems HilbertRuleSystemBridges
  CanonicalGrz StructuralFrames FiniteCWFFrameRank
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

(** Complete source-facing Kripke semantic surface: local satisfaction,
    fixed-model validity, frame validity, and frame-class counterexamples. *)
Check inhabited_frame.
Check kripke_frame_class.
Check kripke_frame_class_valid.
Check kripke_frame_class_validates.
Check kripke_frame_class_validates_schema.
Check whitepoint_frame.
Check blackpoint_frame.
Check whitepoint_inhabited.
Check blackpoint_inhabited.
Check whitepoint_finite.
Check blackpoint_finite.
Check blackpoint_irreflexive.
Check blackpoint_transitive.
Check blackpoint_strict_order.
Check kripke_satisfies_atom.
Check kripke_satisfies_bottom.
Check kripke_satisfies_imp.
Check kripke_not_satisfies_imp.
Check kripke_satisfies_imp_or.
Check kripke_satisfies_or.
Check kripke_satisfies_and.
Check kripke_satisfies_neg.
Check kripke_satisfies_top.
Check kripke_satisfies_box.
Check kripke_not_satisfies_box.
Check kripke_satisfies_dia.
Check kripke_not_satisfies_dia.
Check kripke_satisfies_iff.
Check kripke_satisfies_negneg.
Check kripke_not_satisfies_and.
Check kripke_satisfies_box_iter_negneg.
Check kripke_satisfies_box_negneg.
Check kripke_satisfies_dia_iter_negneg.
Check kripke_satisfies_dia_negneg.
Check kripke_list_disj.
Check kripke_satisfies_list_conj.
Check kripke_satisfies_list_conj2.
Check kripke_satisfies_list_disj.
Check kripke_satisfies_indexed_list_conj.
Check kripke_not_satisfies_indexed_list_conj.
Check kripke_satisfies_indexed_list_disj.
Check kripke_not_satisfies_indexed_list_disj.
Check kripke_satisfies_imp_trans.
Check kripke_satisfies_mp.
Check kripke_neg_semiequiv.
Check kripke_box_iter_semiequiv.
Check kripke_box_semiequiv.
Check kripke_dia_iter_semiequiv.
Check kripke_dia_semiequiv.
Check kripke_neg_equiv.
Check kripke_box_iter_equiv.
Check kripke_box_equiv.
Check kripke_dia_iter_equiv.
Check kripke_dia_equiv.
Check kripke_dia_dual.
Check kripke_dia_iter_dual.
Check kripke_box_dual.
Check kripke_box_iter_dual.
Check kripke_not_imp_iff_and_neg.
Check kripke_satisfies_substitute.
Check kripke_model_valid_iff.
Check kripke_model_valid_top.
Check kripke_model_valid_bottom.
Check kripke_model_invalid_iff_exists_world.
Check kripke_model_valid_mp.
Check kripke_model_valid_nec.
Check kripke_model_valid_multinec.
Check kripke_model_valid_Hilbert_imply_K.
Check kripke_model_valid_Hilbert_imply_S.
Check kripke_model_valid_Hilbert_elim_contra.
Check kripke_model_valid_K.
Check kripke_frame_validates.
Check kripke_valid_iff.
Check kripke_frame_validates_iff.
Check kripke_valid_top.
Check kripke_valid_bottom.
Check kripke_not_valid_iff_exists_valuation.
Check kripke_not_valid_iff_exists_valuation_world.
Check kripke_not_valid_iff_exists_model_world.
Check kripke_valid_mp.
Check kripke_valid_nec.
Check kripke_valid_substitute.
Check kripke_valid_Hilbert_imply_K.
Check kripke_valid_Hilbert_imply_S.
Check kripke_valid_Hilbert_elim_contra.
Check kripke_valid_K.
Check kripke_frame_logic.
Check kripke_frame_class_logic.
Check kripke_frame_class_invalid_iff_exists_frame.
Check kripke_frame_class_invalid_iff_exists_model.
Check kripke_frame_class_invalid_iff_exists_model_world.
Check kripke_frame_class_invalid_iff_exists_valuation_world.
Check kripke_frame_class_validates_with_K.
Check kripke_frame_class_validates_with_K_nat.

(** Frame and frame-class Hilbert packaging. *)
Check normal_frame_class_sound.
Check normal_frame_sound.
Check normal_frame_class_complete.
Check normal_weaker_than.
Check normal_consistent_all_atoms.
Check normal_soundness_of_frame_class_validates_axioms.
Check normal_frame_class_sound_of_validates_axioms.
Check normal_soundness_of_frame_validates_axioms.
Check normal_frame_sound_of_validates_axioms.
Check normal_consistent_of_sound_frame_class.
Check normal_consistent_of_sound_frame.
Check normal_weaker_than_of_subset_frame_class.

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

(** Abstract Boolean modal algebras and the complete Magari layer. *)
Check boolean_algebra.
Check ba_imp_adjoint.
Check modal_algebra.
Check modal_box_top.
Check modal_box_meet.
Check modal_dia_dual.
Check dual_box.
Check compl_box.
Check compl_dia.
Check dia_bot.
Check box_imp_le_box_imp_box.
Check box_axiomK.
Check dia_or.
Check dia_monotone.
Check box_monotone.
Check transitive_modal_algebra.
Check reflexive_modal_algebra.
Check magari_algebra.
Check magari_box_diag.
Check box_diag.
Check dia_diag.
Check dia_trans.
Check box_trans.
Check magari_transitive_modal_algebra.
Check complex_boolean_algebra.
Check complex_modal_algebra.
Check complex_boolean_order_iff.
Check complex_boolean_equiv_iff.

Print Assumptions box_imp_le_box_imp_box.
Print Assumptions dia_or.
Print Assumptions dia_trans.
Print Assumptions box_trans.
Print Assumptions complex_boolean_algebra.
Print Assumptions complex_modal_algebra.

(** Complete coherence-space and stable-function surfaces. *)
Check coherence_space.
Check incoherent.
Check strictly_incoherent.
Check strictly_coherent.
Check coherence_refl.
Check coherence_sym.
Check coherence_sym_iff.
Check incoherence_refl.
Check incoherence_sym.
Check incoherence_sym_iff.
Check strictly_incoherent_iff_incoherent_ne.
Check incoherent_iff_strictly_incoherent_or_eq.
Check strictly_incoherent_sym.
Check strictly_incoherent_sym_iff.
Check strictly_coherent_iff_coherent_ne.
Check coherent_iff_strictly_coherent_or_eq.
Check strictly_coherent_sym.
Check strictly_coherent_sym_iff.
Check coherence_trichotomy.
Check coherence_set.
Check set_included.
Check set_equiv.
Check set_empty.
Check set_singleton.
Check set_insert.
Check set_intersection.
Check set_union.
Check set_big_union.
Check is_clique.
Check is_coclique.
Check clique_empty.
Check clique_singleton.
Check clique_of_subset.
Check clique_insert_iff.
Check set_doubleton.
Check clique_doubleton_iff.
Check clique_big_union_of_pairwise_union.
Check point.
Check point_included.
Check point_equiv.
Check point_equiv_refl.
Check point_equiv_sym.
Check point_equiv_trans.
Check point_equiv_equivalence.
Check point_included_refl.
Check point_included_trans.
Check point_included_preorder.
Check point_equiv_iff_mutual_inclusion.
Check point_included_respects_equiv.
Check point_empty.
Check point_singleton.
Check point_meet.
Check point_meet_member.
Check point_clique.
Check point_le_def.
Check directed_on.
Check directed_on_of_terminal_element.
Check raw_clique_colimit.
Check point_colimit.
Check raw_clique_colimit_member.
Check point_colimit_member.
Check discrete_coherence_space.
Check total_coherence_space.
Check coherence_top.
Check coherence_zero.
Check coherence_one.
Check coherence_bottom.
Check coherence_top_space.
Check coherence_zero_space.
Check coherence_one_space.
Check coherence_bottom_space.
Check empty_type_coherence_space.
Check unit_coherence_space.
Check bool_coherence_space.
Check lneg.
Check lneg_coherent.
Check lneg_space.
Check lneg_coherence_def.
Check lneg_mk_coherent_iff.
Check lneg_mk_strictly_coherent_iff.
Check lneg_mk_incoherent_iff.
Check lneg_mk_strictly_incoherent_iff.
Check tensor.
Check tensor_coherent.
Check tensor_space.
Check tensor_coherence_def.
Check tensor_mk_coherent_iff.
Check par.
Check par_to_pair.
Check par_coherent.
Check par_space.
Check par_coherence_def.
Check par_mk_coherent_iff.
Check par_mk_strictly_coherent_iff.
Check arrow_par_coherent.
Check arrow_par_space.
Check arrow_par_coherence_def.
Check arrow_par_coherent_iff.
Check arrow_par_strictly_coherent_iff.
Check lolli.
Check lolli_space.
Check lolli_identity_member.
Check lolli_identity_clique.
Check lolli_identity.
Check with_space_type.
Check with_coherent.
Check additive_with_space.
Check with_coherence_def.
Check big_with.
Check big_with_coherent.
Check additive_big_with_space.
Check big_with_coherence_def.
Check plus_space_type.
Check plus_coherent.
Check additive_plus_space.
Check plus_coherence_def.
Check big_plus.
Check big_plus_coherent.
Check additive_big_plus_space.
Check big_plus_coherence_def.
Check stable_function.
Check stable_function_equiv.
Check stable_function_equiv_refl.
Check stable_function_equiv_sym.
Check stable_function_equiv_trans.
Check stable_function_equiv_equivalence.
Check stable_monotone.
Check stable_respects_equiv.
Check stable_colimit.
Check stable_pullback.
Check point_union_of_clique.
Check point_left_included_union.
Check point_right_included_union.
Check stable_union_clique.
Check stable_function_extensional.
Check stable_image.
Check stable_image_directed.
Check stable_colimit_equiv.
Check stable_identity.
Check stable_identity_apply.
Check stable_compose.
Check stable_compose_apply.
Check stable_identity_compose.
Check stable_compose_identity.
Check stable_compose_associative.

(** Extensional points avoid function/proposition extensionality.  Classical
    logic is confined to DNE-based strict-coherence and duality laws; the
    stable-function/category layer is constructive. *)
Print Assumptions coherence_sym_iff.
Print Assumptions strictly_incoherent_iff_incoherent_ne.
Print Assumptions strictly_coherent_iff_coherent_ne.
Print Assumptions coherent_iff_strictly_coherent_or_eq.
Print Assumptions coherence_trichotomy.
Print Assumptions clique_big_union_of_pairwise_union.
Print Assumptions point_colimit_member.
Print Assumptions lneg_mk_strictly_coherent_iff.
Print Assumptions lneg_mk_incoherent_iff.
Print Assumptions tensor_mk_coherent_iff.
Print Assumptions par_mk_strictly_coherent_iff.
Print Assumptions arrow_par_strictly_coherent_iff.
Print Assumptions lolli_identity_clique.
Print Assumptions big_with_coherence_def.
Print Assumptions big_plus_coherence_def.
Print Assumptions stable_union_clique.
Print Assumptions stable_respects_equiv.
Print Assumptions stable_colimit_equiv.
Print Assumptions stable_identity.
Print Assumptions stable_compose.
Print Assumptions stable_identity_compose.
Print Assumptions stable_compose_associative.

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
Check K_proves_nnformula_iff_neg.
Check K_proves_exists_nnformula_iff.
Check K_proves_exists_nnformula_of_provable.

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
(** Constructor-by-constructor bridges from the exact raw calculi to the
    established concrete GL presentations. *)
Check with_henkin_K4_weaker_than_K4Henkin.
Check K4Henkin_weaker_than_with_henkin_K4.
Check provable_with_henkin_K4_K4Henkin_iff.
Check provable_GL_with_henkin_K4_iff.
Check with_loeb_K4_weaker_than_K4Loeb.
Check K4Loeb_weaker_than_with_loeb_K4.
Check provable_with_loeb_K4_K4Loeb_iff.
Check provable_GL_with_loeb_K4_iff.
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

(** Complete raw Hilbert axiom-template and capability surface. *)
Check raw_modal_axiom.
Check raw_axiom_instances.
Check raw_axiom_instance_of_mem.
Check raw_axioms_has_M.
Check raw_axioms_has_C.
Check raw_axioms_has_N.
Check raw_axioms_has_K.
Check raw_axioms_has_T.
Check raw_axioms_has_D.
Check raw_axioms_has_P.
Check raw_axioms_has_B.
Check raw_axioms_has_Four.
Check raw_axioms_has_FourN.
Check raw_axioms_has_Five.
Check raw_axioms_has_Point2.
Check raw_axioms_has_WeakPoint2.
Check raw_axioms_has_Point3.
Check raw_axioms_has_WeakPoint3.
Check raw_axioms_has_Point4.
Check raw_axioms_has_L.
Check raw_axioms_has_Z.
Check raw_axioms_has_Grz.
Check raw_axioms_has_Dum.
Check raw_axioms_has_Tc.
Check raw_axioms_has_Ver.
Check raw_axioms_has_Hen.
Check raw_axioms_has_McK.
Check raw_axioms_has_Mk.
Check raw_axioms_has_H1.
Check raw_axioms_has_Geach.

(** Complete substitution-free E/EM/EN/EMC/EMCN entailment, duality, and
    Geach-duality surfaces. *)
Check replacement_of_equivalents.
Check box_regularity.
Check necessitation.
Check has_M.
Check has_C.
Check has_N.
Check has_K.
Check has_T.
Check has_DiaTc.
Check has_P.
Check has_Four.
Check has_Five.
Check has_Geach.
Check has_DiaDuality.
Check dia_dual_entailment.
Check dia_dual_axiom.
Check e_entailment.
Check dia_dual_of_E.
Check em_entailment.
Check en_entailment.
Check emc_entailment.
Check emcn_entailment.
Check k_entailment.
Check logic_iff_intro.
Check logic_iff_elim_left.
Check logic_iff_elim_right.
Check logic_iff_sym.
Check logic_iff_trans.
Check logic_contraposition.
Check logic_neg_iff.
Check logic_double_neg_iff.
Check logic_double_neg_iff_rev.
Check logic_iff_top_left_from.
Check logic_iff_not_top_bottom.
Check conj_cons.
Check iff_top_left_raw.
Check iff_top_left.
Check iff_symm.
Check iff_top_right.
Check iff_not_bot_top.
Check EMNLN_raw.
Check EMNLN.
Check IMNLN_raw.
Check IMNLN.
Check NLN_of_M.
Check INLNM_raw.
Check INLNM.
Check M_of_NLN_raw.
Check M_of_NLN.
Check has_DiaTc_of_E_T.
Check has_P_of_T.
Check multire_raw.
Check multire.
Check multi_ELLNN_raw.
Check multi_ELLNN.
Check ELLNN_raw.
Check ELLNN.
Check ILLNN_raw.
Check ILLNN.
Check box_dni.
Check box_dni_bang.
Check ILNNL_raw.
Check ILNNL.
Check box_dne.
Check box_dne_bang.
Check box_dne_applied_raw.
Check box_dne_applied.
Check INMNL_raw.
Check INMNL.
Check INLMN_raw.
Check INLMN.
Check multiDiaDuality.
Check diaItr_duality.
Check diaItrDuality_mp.
Check diaDuality_mp.
Check diaItrDuality_mpr.
Check diaDuality_mpr.
Check diaDuality_prime_mp.
Check diaDuality_prime_mpr.
Check diaItr_duality_mp.
Check dia_duality_mp.
Check diaItr_duality_mpr.
Check dia_duality_mpr.
Check dia_duality_iff.
Check diaItr_duality_iff.
Check boxItrDuality.
Check boxItr_duality.
Check boxItrDuality_mp.
Check boxDuality_mp.
Check boxItrDuality_mpr.
Check boxDuality_mpr.
Check boxItr_duality_mp.
Check boxItr_duality_mp_applied.
Check boxItr_duality_mpr.
Check boxItr_duality_mpr_applied.
Check boxDuality.
Check box_duality.
Check boxDuality_mp_wrapped.
Check boxDuality_mp_applied_raw.
Check boxDuality_mp_applied.
Check boxDuality_mpr_wrapped.
Check boxDuality_mpr_applied_raw.
Check boxDuality_mpr_applied.
Check logic_curry.
Check box_regularity_of_EM.
Check EM_of_E_box_regularity.
Check necessitation_of_EN.
Check has_N_of_necessitation.
Check has_K_of_EMC.
Check box_regularity_of_k.
Check e_entailment_of_k.
Check has_C_of_k.
Check k_entailment_of_EMCN.
Check EMCN_of_k_entailment.
Check geach_dual.
Check has_Geach_dual.
Check axiom_T_dual_raw.
Check axiom_T_dual.
Check axiom_Four_dual_raw.
Check axiom_Four_dual.
Check axiom_Five_dual_raw.
Check axiom_Five_dual.

(** Complete named substitution-free EMK/END/ET/ETB/ET5/KP surfaces. *)
Check has_D.
Check has_B.
Check has_Point2.
Check minimal_implication_entailment.
Check minimal_implication_of_classical.
Check et_entailment.
Check ed_entailment.
Check eb_entailment.
Check e5_entailment.
Check kp_entailment.
Check emk_entailment.
Check has_C_of_EMK.
Check end_entailment.
Check has_P_of_END.
Check diabot_raw.
Check diabot.
Check has_D_of_ET.
Check ED_of_ET.
Check C_of_raw.
Check C_of.
Check etb_entailment.
Check ET_of_ETB.
Check EB_of_ETB.
Check necessitation_of_ETB.
Check has_N_of_ETB.
Check EN_of_ETB.
Check et5_entailment.
Check ET_of_ET5.
Check E5_of_ET5.
Check has_B_of_ET5.
Check ETB_of_ET5.
Check EN_of_ET5.
Check has_Point2_of_ET5.
Check has_Four_of_ET5.
Check KP_axiomD.
Check has_D_of_KP.

(** Complete KT/S4/S5 substitution-free derived-rule surfaces. *)
Check kd_entailment.
Check kt_entailment.
Check kt_prime_entailment.
Check has_T_of_KT_prime.
Check KT_of_KT_prime.
Check KP_of_KT_prime.
Check KD_of_KT_prime.
Check ET_of_KT.
Check KD_of_KT.
Check reduce_box_in_CAnt_bang.
Check s4_entailment.
Check Diadot.
Check iff_box_boxdot_raw.
Check iff_box_boxdot.
Check iff_dia_diadot_raw.
Check iff_dia_diadot.
Check s5_entailment.
Check s5_E.
Check diabox_box_raw.
Check diabox_box.
Check diabox_box_applied_raw.
Check diabox_box_applied.
Check rm_diabox_raw.
Check rm_diabox.
Check rm_diabox_applied_raw.
Check rm_diabox_applied.
Check lem1_diaT_of_S5Grz.
Check lem2_diaT_of_S5Grz.

(** Faithful ten-declaration generic core of raw Hilbert.Normal. *)
Check normal_hilbert_proves.
Check NH_axm.
Check NH_mp.
Check NH_nec.
Check NH_imply_K.
Check NH_imply_S.
Check NH_elim_contra.
Check normal_hilbert_axm.
Check normal_hilbert_axm_substituted.
Check normal_hilbert_axm_bang.
Check normal_hilbert_lukasiewicz.
Check normal_hilbert_necessitation.
Check normal_hilbert_proves_substitute.
Check normal_hilbert_proves_fold.
Check normal_hilbert_weaker_of_provable_axioms.
Check normal_hilbert_weaker_of_subset_axioms.

(** Complete 25-declaration raw-axiom adapter block of Hilbert.Normal. *)
Check has_FourN.
Check has_L.
Check has_Z.
Check has_Hen.
Check has_WeakPoint2.
Check has_Point3.
Check has_WeakPoint3.
Check has_Point4.
Check has_Grz.
Check has_Dum.
Check has_Tc.
Check has_Ver.
Check has_McK.
Check has_Mk.
Check has_H.
Check structural_normal_entailment.
Check normal_hilbert_identity.
Check normal_hilbert_imply_intro.
Check normal_hilbert_under_mp.
Check normal_hilbert_and_intro.
Check normal_hilbert_iff_refl.
Check normal_hilbert_has_DiaDuality.
Check normal_hilbert_instantiate_unary.
Check normal_hilbert_instantiate_binary.
Check normal_hilbert_has_K.
Check normal_hilbert_is_normal.
Check normal_hilbert_has_T.
Check normal_hilbert_has_D.
Check normal_hilbert_has_P.
Check normal_hilbert_has_B.
Check normal_hilbert_has_Four.
Check normal_hilbert_has_FourN.
Check normal_hilbert_has_Five.
Check normal_hilbert_has_L.
Check normal_hilbert_has_Z.
Check normal_hilbert_has_Hen.
Check normal_hilbert_has_Point2.
Check normal_hilbert_has_WeakPoint2.
Check normal_hilbert_has_Point3.
Check normal_hilbert_has_WeakPoint3.
Check normal_hilbert_has_Point4.
Check normal_hilbert_has_Grz.
Check normal_hilbert_has_Dum.
Check normal_hilbert_has_Tc.
Check normal_hilbert_has_Ver.
Check normal_hilbert_has_McK.
Check normal_hilbert_has_Mk.
Check normal_hilbert_has_H.
Check normal_hilbert_has_Geach.

(** First 15 declarations of the raw Normal named-system catalogue: exact
    K, KT, and KD plus syntactic compatibility with the legacy systems. *)
Check structural_k_entailment.
Check structural_kt_entailment.
Check structural_kd_entailment.
Check structural_k_of_normal.
Check normal_K_axioms.
Check normal_K_axioms_has_K.
Check normal_K.
Check normal_K_entailment.
Check normal_K_weaker_than_structural_normal.
Check normal_KT_axioms.
Check normal_KT_axioms_has_K.
Check normal_KT_axioms_has_T.
Check normal_KT.
Check normal_KT_entailment.
Check normal_KD_axioms.
Check normal_KD_axioms_has_K.
Check normal_KD_axioms_has_D.
Check normal_KD.
Check normal_KD_entailment.
Check normal_K_to_K_normal_proves.
Check K_normal_proves_to_normal_K.
Check normal_K_iff_K_normal_proves.
Check normal_K_equiv_K_normal_proves.
Check normal_KT_to_KT_proves.
Check KT_proves_to_normal_KT.
Check normal_KT_iff_KT_proves.
Check normal_KT_equiv_KT_proves.
Check normal_KD_to_KD_proves.
Check KD_proves_to_normal_KD.
Check normal_KD_iff_KD_proves.
Check normal_KD_equiv_KD_proves.

(** Exact KP, KB, KDB, and KTB raw systems, including the wholly syntactic
    KP/KD equivalence and the constructorwise KB compatibility bridge. *)
Check structural_kp_entailment.
Check structural_kb_entailment.
Check structural_kdb_entailment.
Check structural_ktb_entailment.
Check normal_KP_axioms.
Check normal_KP_axioms_has_K.
Check normal_KP_axioms_has_P.
Check normal_KP.
Check normal_KP_entailment.
Check normal_KP_equiv_KD.
Check normal_KB_axioms.
Check normal_KB_axioms_has_K.
Check normal_KB_axioms_has_B.
Check normal_KB.
Check normal_KB_entailment.
Check normal_KDB_axioms.
Check normal_KDB_axioms_has_K.
Check normal_KDB_axioms_has_D.
Check normal_KDB_axioms_has_B.
Check normal_KDB.
Check normal_KDB_entailment.
Check normal_KTB_axioms.
Check normal_KTB_axioms_has_K.
Check normal_KTB_axioms_has_T.
Check normal_KTB_axioms_has_B.
Check normal_KTB.
Check normal_KTB_entailment.
Check normal_KB_to_KB_proves.
Check KB_proves_to_normal_KB.
Check normal_KB_iff_KB_proves.
Check normal_KB_equiv_KB_proves.

(** Exact raw K4 and indexed K4n systems from the Normal catalogue. *)
Check structural_k4_entailment.
Check structural_k4n_entailment.
Check normal_K4_axioms.
Check normal_K4_axioms_has_K.
Check normal_K4_axioms_has_Four.
Check normal_K4.
Check normal_K4_entailment.
Check normal_K4n_axioms.
Check normal_K4n_axioms_has_K.
Check normal_K4n_axioms_has_FourN.
Check normal_K4n.
Check normal_K4n_entailment.
Check normal_K4_to_K4_proves.
Check K4_proves_to_normal_K4.
Check normal_K4_iff_K4_proves.
Check normal_K4_equiv_K4_proves.

(** Exact raw KMcK/K4McK systems and the generic source capability lift. *)
Check structural_kmck_entailment.
Check structural_k4mck_entailment.
Check normal_KMcK_axioms.
Check normal_KMcK_axioms_has_K.
Check normal_KMcK_axioms_has_McK.
Check normal_KMcK.
Check normal_KMcK_entailment.
Check normal_K4McK_axioms.
Check normal_K4McK_axioms_has_K.
Check normal_K4McK_axioms_has_Four.
Check normal_K4McK_axioms_has_McK.
Check normal_K4McK.
Check normal_K4McK_entailment.
Check normal_K4McK_entailment_of_subset.

(** Exact raw K4Point2/K4Point3 systems from the Normal catalogue. *)
Check structural_k4point2_entailment.
Check structural_k4point3_entailment.
Check normal_K4Point2_axioms.
Check normal_K4Point2_axioms_has_K.
Check normal_K4Point2_axioms_has_Four.
Check normal_K4Point2_axioms_has_WeakPoint2.
Check normal_K4Point2.
Check normal_K4Point2_entailment.
Check normal_K4Point3_axioms.
Check normal_K4Point3_axioms_has_K.
Check normal_K4Point3_axioms_has_Four.
Check normal_K4Point3_axioms_has_WeakPoint3.
Check normal_K4Point3.
Check normal_K4Point3_entailment.

(** Exact raw KT4B/K45/KD4/KD5 systems from the Normal catalogue. *)
Check structural_kt4b_entailment.
Check structural_k45_entailment.
Check structural_kd4_entailment.
Check structural_kd5_entailment.
Check normal_KT4B_axioms.
Check normal_KT4B_axioms_has_K.
Check normal_KT4B_axioms_has_T.
Check normal_KT4B_axioms_has_Four.
Check normal_KT4B_axioms_has_B.
Check normal_KT4B.
Check normal_KT4B_entailment.
Check normal_K45_axioms.
Check normal_K45_axioms_has_K.
Check normal_K45_axioms_has_Four.
Check normal_K45_axioms_has_Five.
Check normal_K45.
Check normal_K45_entailment.
Check normal_KD4_axioms.
Check normal_KD4_axioms_has_K.
Check normal_KD4_axioms_has_D.
Check normal_KD4_axioms_has_Four.
Check normal_KD4.
Check normal_KD4_entailment.
Check normal_KD5_axioms.
Check normal_KD5_axioms_has_K.
Check normal_KD5_axioms_has_D.
Check normal_KD5_axioms_has_Five.
Check normal_KD5.
Check normal_KD5_entailment.

(** Exact raw KD45/KB4/KB5 systems from the Normal catalogue. *)
Check structural_kd45_entailment.
Check structural_kb4_entailment.
Check structural_kb5_entailment.
Check normal_KD45_axioms.
Check normal_KD45_axioms_has_K.
Check normal_KD45_axioms_has_D.
Check normal_KD45_axioms_has_Four.
Check normal_KD45_axioms_has_Five.
Check normal_KD45.
Check normal_KD45_entailment.
Check normal_KB4_axioms.
Check normal_KB4_axioms_has_K.
Check normal_KB4_axioms_has_B.
Check normal_KB4_axioms_has_Four.
Check normal_KB4.
Check normal_KB4_entailment.
Check normal_KB5_axioms.
Check normal_KB5_axioms_has_K.
Check normal_KB5_axioms_has_B.
Check normal_KB5_axioms_has_Five.
Check normal_KB5.
Check normal_KB5_entailment.

(** Exact raw S4/S4McK systems and their source inclusions. *)
Check structural_s4_entailment.
Check structural_s4mck_entailment.
Check normal_S4_axioms.
Check normal_S4_axioms_has_K.
Check normal_S4_axioms_has_T.
Check normal_S4_axioms_has_Four.
Check normal_S4.
Check normal_S4_entailment.
Check normal_K4_weaker_than_normal_S4.
Check normal_S4McK_axioms.
Check normal_S4McK_axioms_has_K.
Check normal_S4McK_axioms_has_T.
Check normal_S4McK_axioms_has_Four.
Check normal_S4McK_axioms_has_McK.
Check normal_S4McK.
Check normal_S4McK_entailment.
Check normal_K4McK_weaker_than_normal_S4McK.

(** Exact raw S4Point2/3/4McK systems and K4McK inclusions. *)
Check structural_s4point2mck_entailment.
Check structural_s4point3mck_entailment.
Check structural_s4point4mck_entailment.
Check normal_S4Point2McK_axioms.
Check normal_S4Point2McK_axioms_has_K.
Check normal_S4Point2McK_axioms_has_T.
Check normal_S4Point2McK_axioms_has_Four.
Check normal_S4Point2McK_axioms_has_McK.
Check normal_S4Point2McK_axioms_has_Point2.
Check normal_S4Point2McK.
Check normal_S4Point2McK_entailment.
Check normal_K4McK_weaker_than_normal_S4Point2McK.
Check normal_S4Point3McK_axioms.
Check normal_S4Point3McK_axioms_has_K.
Check normal_S4Point3McK_axioms_has_T.
Check normal_S4Point3McK_axioms_has_Four.
Check normal_S4Point3McK_axioms_has_McK.
Check normal_S4Point3McK_axioms_has_Point3.
Check normal_S4Point3McK.
Check normal_S4Point3McK_entailment.
Check normal_K4McK_weaker_than_normal_S4Point3McK.
Check normal_S4Point4McK_axioms.
Check normal_S4Point4McK_axioms_has_K.
Check normal_S4Point4McK_axioms_has_T.
Check normal_S4Point4McK_axioms_has_Four.
Check normal_S4Point4McK_axioms_has_McK.
Check normal_S4Point4McK_axioms_has_Point4.
Check normal_S4Point4McK.
Check normal_S4Point4McK_entailment.
Check normal_K4McK_weaker_than_normal_S4Point4McK.

(** Exact raw K5/S5 systems from the Normal catalogue. *)
Check structural_k5_entailment.
Check structural_s5_entailment.
Check normal_K5_axioms.
Check normal_K5_axioms_has_K.
Check normal_K5_axioms_has_Five.
Check normal_K5.
Check normal_K5_entailment.
Check normal_S5_axioms.
Check normal_S5_axioms_has_K.
Check normal_S5_axioms_has_T.
Check normal_S5_axioms_has_Five.
Check normal_S5.
Check normal_S5_entailment.

(** Complete 17-declaration raw-axiom calculus with the Henkin rule. *)
Check henkin_rule.
Check with_henkin_proves.
Check WH_axm.
Check WH_mp.
Check WH_nec.
Check WH_henkin.
Check WH_imply_K.
Check WH_imply_S.
Check WH_elim_contra.
Check with_henkin_axm_substituted.
Check with_henkin_axm.
Check with_henkin_lukasiewicz.
Check with_henkin_necessitation.
Check with_henkin_henkin_rule.
Check with_henkin_proves_substitute.
Check with_henkin_proves_fold.
Check with_henkin_weaker_of_provable_axioms.
Check with_henkin_weaker_of_subset_axioms.
Check with_henkin_instantiate_unary.
Check with_henkin_instantiate_binary.
Check with_henkin_has_K.
Check with_henkin_has_Four.
Check with_henkin_identity.
Check with_henkin_imply_intro.
Check with_henkin_under_mp.
Check with_henkin_and_intro.
Check with_henkin_iff_refl.
Check with_henkin_has_DiaDuality.
Check with_henkin_K4_axioms.
Check with_henkin_K4_axioms_has_K.
Check with_henkin_K4_axioms_has_Four.
Check with_henkin_K4.
Check structural_k4_henkin_entailment.
Check with_henkin_K4_entailment.

(** Complete 17-declaration raw-axiom calculus with Loeb's rule. *)
Check loeb_rule.
Check structural_k4loeb_entailment.
Check with_loeb_proves.
Check WL_axm.
Check WL_mp.
Check WL_nec.
Check WL_loeb.
Check WL_imply_K.
Check WL_imply_S.
Check WL_elim_contra.
Check with_loeb_axm_substituted.
Check with_loeb_axm.
Check with_loeb_lukasiewicz.
Check with_loeb_necessitation.
Check with_loeb_loeb_rule.
Check with_loeb_proves_substitute.
Check with_loeb_proves_fold.
Check with_loeb_weaker_of_provable_axioms.
Check with_loeb_weaker_of_subset_axioms.
Check with_loeb_has_K.
Check with_loeb_has_Four.
Check with_loeb_K4_axioms.
Check with_loeb_K4_axioms_has_K.
Check with_loeb_K4_axioms_has_Four.
Check with_loeb_K4_proves.
Check with_loeb_K4Loeb_entailment.

(** Faithful generic WithRE calculus core and source-schema adapters. *)
Check with_re_axiom.
Check with_re_proves.
Check WRE_axm.
Check WRE_mp.
Check WRE_re.
Check WRE_imply_K.
Check WRE_imply_S.
Check WRE_elim_contra.
Check with_re_axm_substituted.
Check with_re_axm.
Check lukasiewicz_entailment.
Check with_re_lukasiewicz.
Check with_re_proves_substitute.
Check with_re_substitution_closed.
Check with_re_proves_fold.
Check with_re_proves_dependent_fold.
Check with_re_weaker_of_provable_axioms.
Check with_re_weaker_of_subset_axioms.
Check with_re_classical_complete.
Check with_re_classical_logic.
Check with_re_e_entailment.
Check with_re_axioms_has_M.
Check with_re_axioms_has_C.
Check with_re_axioms_has_N.
Check with_re_axioms_has_K.
Check with_re_axioms_has_T.
Check with_re_axioms_has_D.
Check with_re_axioms_has_P.
Check with_re_axioms_has_Four.
Check with_re_axioms_has_B.
Check with_re_axioms_has_Five.
Check atom_decidable_equality.
Check with_re_single_substitution.
Check with_re_double_substitution.
Check with_re_single_substitution_at.
Check with_re_double_substitution_left.
Check with_re_double_substitution_right.
Check with_re_instantiate_unary.
Check with_re_instantiate_binary.
Check with_re_has_M.
Check with_re_has_C.
Check with_re_has_N.
Check with_re_has_K.
Check with_re_has_T.
Check with_re_has_D.
Check with_re_has_P.
Check with_re_has_Four.
Check with_re_has_B.
Check with_re_has_Five.

(** The finite propositional skeleton closes the classical-basis gap without
    changing the faithful six-constructor calculus. *)
Check with_re_empty_axioms.
Check with_re_erase_boxes.
Check with_re_empty_identity.
Check with_re_empty_top.
Check K_proves_erase_boxes_with_re.
Check with_re_empty_substitute_between.
Check with_re_propositional_support.
Check with_re_classical_eq_dec.
Check with_re_support_index.
Check with_re_nth_support_index.
Check with_re_propositional_skeleton.
Check with_re_support_decode.
Check with_re_skeleton_classical_eval.
Check with_re_skeleton_tautology.
Check with_re_erase_skeleton.
Check with_re_decode_skeleton.
Check with_re_decode_own_skeleton.
Check with_re_empty_classical_complete.
Check with_re_classical_complete_weaken.
Check with_re_classical_logic_from_basis.
Check with_re_e_entailment_from_basis.

(** Empty and elementary M/C/N/K concrete WithRE systems. *)
Check ec_entailment.
Check emn_entailment.
Check ecn_entailment.
Check ek_entailment.
Check with_re_E.
Check with_re_EM_axioms.
Check with_re_EM_axioms_has_M.
Check with_re_EM.
Check with_re_EM_entailment.
Check with_re_EC_axioms.
Check with_re_EC_axioms_has_C.
Check with_re_EC.
Check with_re_EC_entailment.
Check with_re_EN_axioms.
Check with_re_EN_axioms_has_N.
Check with_re_EN.
Check with_re_EN_entailment.
Check with_re_EMC_axioms.
Check with_re_EMC_axioms_has_M.
Check with_re_EMC_axioms_has_C.
Check with_re_EMC.
Check with_re_EMC_entailment.
Check with_re_EMN_axioms.
Check with_re_EMN_axioms_has_M.
Check with_re_EMN_axioms_has_N.
Check with_re_EMN.
Check with_re_EMN_entailment.
Check with_re_ECN_axioms.
Check with_re_ECN_axioms_has_C.
Check with_re_ECN_axioms_has_N.
Check with_re_ECN.
Check with_re_ECN_entailment.
Check with_re_EK_axioms.
Check with_re_EK_axioms_has_K.
Check with_re_EK.
Check with_re_EK_entailment.

(** Exact EMCN, EMCNT, and EMCNT4 raw systems and entailment adapters. *)
Check with_re_EMCN_axioms.
Check with_re_EMCN_axioms_has_M.
Check with_re_EMCN_axioms_has_C.
Check with_re_EMCN_axioms_has_N.
Check with_re_EMCN.
Check with_re_EMCN_entailment_of_classical_complete.
Check with_re_EMCN_entailment.
Check with_re_EMCNT_axioms.
Check with_re_EMCNT_axioms_has_M.
Check with_re_EMCNT_axioms_has_C.
Check with_re_EMCNT_axioms_has_N.
Check with_re_EMCNT_axioms_has_T.
Check with_re_EMCNT.
Check with_re_EMCNT_emc_entailment_of_classical_complete.
Check with_re_EMCNT_emc_entailment.
Check with_re_EMCNT_en_entailment_of_classical_complete.
Check with_re_EMCNT_en_entailment.
Check with_re_EMCNT4_axioms.
Check with_re_EMCNT4_axioms_has_M.
Check with_re_EMCNT4_axioms_has_C.
Check with_re_EMCNT4_axioms_has_N.
Check with_re_EMCNT4_axioms_has_T.
Check with_re_EMCNT4_axioms_has_Four.
Check with_re_EMCNT4.
Check with_re_EMCNT4_emc_entailment_of_classical_complete.
Check with_re_EMCNT4_emc_entailment.
Check with_re_EMCNT4_en_entailment_of_classical_complete.
Check with_re_EMCNT4_en_entailment.

(** Unary/nullary Four, D, and P catalogue systems. *)
Check e4_entailment.
Check with_re_E4_axioms.
Check with_re_E4_axioms_has_Four.
Check with_re_E4.
Check with_re_E4_e4_entailment.
Check with_re_EN4_axioms.
Check with_re_EN4_axioms_has_N.
Check with_re_EN4_axioms_has_Four.
Check with_re_EN4.
Check with_re_EN4_en_entailment.
Check with_re_EN4_e4_entailment.
Check with_re_E4_weaker_than_EN4.
Check with_re_ET4_axioms.
Check with_re_ET4_axioms_has_Four.
Check with_re_ET4_axioms_has_T.
Check with_re_ET4.
Check with_re_ET4_e_entailment.
Check with_re_ET4_et_entailment.
Check with_re_ET4_e4_entailment.
Check with_re_ENT4_axioms.
Check with_re_ENT4_axioms_has_N.
Check with_re_ENT4_axioms_has_T.
Check with_re_ENT4_axioms_has_Four.
Check with_re_ENT4.
Check with_re_ENT4_en_entailment.
Check with_re_ENT4_et_entailment.
Check with_re_ENT4_e4_entailment.
Check with_re_ED_axioms.
Check with_re_ED_axioms_has_D.
Check with_re_ED.
Check with_re_ED_has_D.
Check with_re_END_axioms.
Check with_re_END_axioms_has_N.
Check with_re_END_axioms_has_D.
Check with_re_END.
Check with_re_END_entailment.
Check with_re_END4_axioms.
Check with_re_END4_axioms_has_N.
Check with_re_END4_axioms_has_D.
Check with_re_END4_axioms_has_Four.
Check with_re_END4.
Check with_re_END4_source_END_entailment.
Check with_re_END4_e4_entailment.
Check with_re_EMND4_axioms.
Check with_re_EMND4_axioms_has_M.
Check with_re_EMND4_axioms_has_N.
Check with_re_EMND4_axioms_has_D.
Check with_re_EMND4_axioms_has_Four.
Check with_re_EMND4.
Check with_re_EMND4_source_END_entailment.
Check with_re_EMND4_em_entailment.
Check with_re_EMND4_e4_entailment.
Check with_re_EP_axioms.
Check with_re_EP_axioms_has_P.
Check with_re_EP.
Check with_re_EP_has_P.

(** B/Five systems and the exact ETB/ENTB equivalence. *)
Check with_re_EB_axioms.
Check with_re_EB_axioms_has_B.
Check with_re_EB.
Check with_re_EB_entailment.
Check with_re_ETB_axioms.
Check with_re_ETB_axioms_has_B.
Check with_re_ETB_axioms_has_T.
Check with_re_ETB.
Check with_re_ETB_entailment.
Check with_re_ETB_en_entailment.
Check with_re_ENTB_axioms.
Check with_re_ENTB_axioms_has_N.
Check with_re_ENTB_axioms_has_T.
Check with_re_ENTB_axioms_has_B.
Check with_re_ENTB.
Check with_re_ENTB_etb_entailment.
Check with_re_ENTB_en_entailment.
Check with_re_ETB_equiv_ENTB.
Check with_re_E5_axioms.
Check with_re_E5_axioms_has_Five.
Check with_re_E5.
Check with_re_E5_entailment.
Check with_re_ET5_axioms.
Check with_re_ET5_axioms_has_Five.
Check with_re_ET5_axioms_has_T.
Check with_re_ET5.
Check with_re_ET5_entailment.

(** T/K and mixed Four-system remainder of the concrete catalogue. *)
Check emt_entailment.
Check with_re_ET_axioms.
Check with_re_ET_axioms_has_T.
Check with_re_ET.
Check with_re_ET_entailment.
Check with_re_EMT_axioms.
Check with_re_EMT_axioms_has_M.
Check with_re_EMT_axioms_has_T.
Check with_re_EMT.
Check with_re_EMT_entailment.
Check with_re_EMK_axioms.
Check with_re_EMK_axioms_has_M.
Check with_re_EMK_axioms_has_K.
Check with_re_EMK.
Check with_re_EMK_entailment.
Check with_re_EMCK_axioms.
Check with_re_EMCK_axioms_has_M.
Check with_re_EMCK_axioms_has_C.
Check with_re_EMCK_axioms_has_K.
Check with_re_EMCK.
Check with_re_EMK_equiv_EMCK.
Check with_re_EMC_equiv_EMCK.
Check emt4_entailment.
Check emc4_entailment.
Check with_re_EMT4_axioms.
Check with_re_EMT4_axioms_has_M.
Check with_re_EMT4_axioms_has_T.
Check with_re_EMT4_axioms_has_Four.
Check with_re_EMT4.
Check with_re_EMT4_entailment.
Check with_re_EMNT4_axioms.
Check with_re_EMNT4_axioms_has_M.
Check with_re_EMNT4_axioms_has_N.
Check with_re_EMNT4_axioms_has_T.
Check with_re_EMNT4_axioms_has_Four.
Check with_re_EMNT4.
Check with_re_EMNT4_em_entailment.
Check with_re_EMNT4_en_entailment.
Check with_re_EMNT4_et_entailment.
Check with_re_EMNT4_e4_entailment.
Check with_re_EMC4_axioms.
Check with_re_EMC4_axioms_has_M.
Check with_re_EMC4_axioms_has_C.
Check with_re_EMC4_axioms_has_Four.
Check with_re_EMC4.
Check with_re_EMC4_entailment.
Check with_re_EMCN4_axioms.
Check with_re_EMCN4_axioms_has_M.
Check with_re_EMCN4_axioms_has_C.
Check with_re_EMCN4_axioms_has_N.
Check with_re_EMCN4_axioms_has_Four.
Check with_re_EMCN4.
Check with_re_EMCN4_emc_entailment.

(** Generic WithRE/normal bridge and all three source named equivalences. *)
Check with_re_axiom_instances_provable_in_normal.
Check normal_generator.
Check normal_generator_modal_K.
Check normal_generator_extra.
Check normal_generators_provable_in_with_re.
Check with_re_normal_equiv_of_provable_generators.
Check equiv_WithRE_Normal_of_provable_axiomInstances.
Check with_re_EMCN_equiv_K_of_classical_complete.
Check with_re_EMCNT_equiv_KT_of_classical_complete.
Check with_re_EMCNT4_equiv_S4_of_classical_complete.
Check with_re_EMCN_equiv_K.
Check with_re_EMCNT_equiv_KT.
Check with_re_EMCNT4_equiv_S4.

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

(** Complete generic surface of Foundation/Vorspiel/Rel: iteration and
    closure generators followed by the elementary named properties. *)
Check rel_iter_positive_succ_iff.
Check rel_iter_succ_left.
Check rel_iter_equality_iff.
Check rel_iter_succ_right_iff.
Check rel_iter_true_of_eq.
Check rel_iter_congr_index.
Check rel_iter_comp_iff.
Check rel_iter_unwrap_transitive_succ.
Check rel_iter_unwrap_transitive_positive.
Check rel_iter_unwrap_reflexive_transitive.
Check rel_iter_prefix_transitive_positive.
Check relation_refl_gen_reflexive.
Check relation_refl_gen_transitive.
Check relation_refl_gen_symmetric.
Check relation_irreflexive.
Check relation_refl_gen_antisymmetric.
Check relation_partial_order.
Check relation_refl_gen_partial_order.
Check relation_trans_gen_transitive.
Check relation_trans_gen_trans.
Check relation_trans_gen_single.
Check relation_trans_gen_head.
Check relation_trans_gen_tail.
Check relation_trans_gen_exists_iterate.
Check relation_trans_gen_remove_iterate.
Check relation_trans_gen_unwrap.
Check relation_trans_gen_unwrap_iff.
Check relation_trans_gen_reflexive.
Check relation_trans_gen_symmetric.
Check relation_trans_gen_antisymmetric.
Check relation_refl_trans_gen_reflexive.
Check relation_refl_trans_gen_transitive.
Check relation_refl_trans_gen_exists_iterate.
Check relation_refl_trans_gen_remove_iterate.
Check relation_refl_trans_gen_unwrap.
Check relation_refl_trans_gen_symmetric.
Check relation_irreflexive_generator.
Check relation_irreflexive_generator_irreflexive.
Check relation_irreflexive_generator_transitive.
Check relation_strict_order.
Check relation_irreflexive_generator_strict_order.
Check relation_coreflexive.
Check relation_coreflexive_of_symmetric_antisymmetric.
Check relation_coreflexive_transitive.
Check relation_coreflexive_symmetric.
Check relation_eq_coreflexive.
Check relation_equality.
Check relation_equality_iff.
Check relation_equality_symmetric.
Check relation_equality_antisymmetric.
Check relation_equality_transitive.
Check relation_piecewise_strongly_connected.
Check relation_equality_piecewise_strongly_connected.
Check relation_eq_is_equality.
Check relation_serial.
Check relation_reflexive_serial.
Check relation_reflexive_of_symmetric_transitive_serial.
Check relation_right_euclidean.
Check relation_left_euclidean.
Check relation_right_euclidean_of_symmetric_transitive.
Check relation_symmetric_of_reflexive_right_euclidean.
Check relation_transitive_of_symmetric_right_euclidean.
Check relation_transitive_of_reflexive_right_euclidean.
Check relation_convergent.
Check relation_strongly_convergent.
Check relation_strongly_convergent_convergent.
Check relation_piecewise_convergent.
Check relation_piecewise_strongly_convergent.
Check relation_piecewise_strongly_convergent_convergent.
Check relation_piecewise_connected.
Check relation_piecewise_connected_distinct.
Check relation_piecewise_connected_of_trichotomous.
Check relation_piecewise_connected_of_right_euclidean.
Check relation_piecewise_strongly_connected_of_total.
Check relation_piecewise_strongly_connected_of_reflexive_connected.
Check relation_piecewise_connected_of_strongly_connected.
Check relation_piecewise_strongly_convergent_of_reflexive_connected.
Check relation_isolated.
Check relation_isolated_elim.
Check relation_isolated_coreflexive.
Check relation_isolated_irreflexive.
Check relation_isolated_transitive.
Check relation_universal.
Check relation_universal_reflexive.
Check relation_universal_right_euclidean.

(** Complete generic converse-well-founded and finite-height surface. *)
Check converse_well_founded.
Check is_converse_well_founded.
Check converse_well_founded_iff_has_max.
Check converse_well_founded_has_max.
Check finite_converse_well_founded_of_transitive_irreflexive.
Check finite_transitive_irreflexive_is_converse_well_founded.
Check cwf_height.
Check cwf_height_eq.
Check cwf_height_gt_of.
Check cwf_height_eq_zero_iff.
Check cwf_height_le.
Check lt_cwf_height.
Check cwf_height_eq_of_lt_of_le.
Check cwf_height_eq_succ.
Check cwf_height_eq_succ_cwf_height.
Check cwf_height_lt.
Check cwf_height_congr.

(** Complete generic weak-converse-well-founded surface. *)
Check weakly_converse_well_founded.
Check is_weakly_converse_well_founded.
Check wcwf_dependent_choice.
Check finite_exists_ne_map_eq_of_infinite_lt.
Check antisymmetric_of_weakly_converse_well_founded.
Check weakly_converse_well_founded_is_antisymmetric.
Check weakly_converse_well_founded_of_finite_transitive_antisymmetric.
Check finite_transitive_antisymmetric_is_weakly_converse_well_founded.

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

(** Complete canonical finite-CWF adapter for the pinned Rank module. *)
Check finite_enumeration_frame_finite.
Check frame_cwf_as_converse_well_founded.
Check frame_rank_spec_converse_well_founded.
Check finite_cwf_frame_rank.
Check finite_cwf_frame_height.
Check finite_cwf_frame_rank_spec.
Check frame_rank_spec_unique.
Check point_generated_finite_enumeration.
Check point_generated_frame_is_tree.
Check finite_cwf_point_generated_relation_cwf.
Check finite_cwf_point_generated_rank.
Check finite_cwf_point_generated_rank_spec.
Check finite_cwf_point_generated_rank_original.
Check fin_value_of_nat_lt.
Check extend_root_finite_enumeration.
Check finite_cwf_extend_root_relation_cwf.
Check finite_cwf_extend_root_rank.
Check finite_cwf_extend_root_rank_spec.
Check finite_cwf_extend_root_embedded_rank.
Check finite_cwf_extend_root_embedded_rank_spec.
Check finite_cwf_extend_root_rank_original.
Check extend_root_algebraic_rank.
Check extend_root_algebraic_rank_spec.
Check finite_cwf_extend_root_rank_eq_algebraic.
Check finite_cwf_extend_root_height.
Check finite_cwf_extend_root_height_unfold.
Check finite_cwf_extend_root_height_eq.
Check finite_cwf_extend_root_height_positive.
Check finite_cwf_one_root_height_successor.
Check finite_cwf_extend_root_rank_base_root.
Check finite_cwf_extend_root_eq_base_height_iff.
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
Check boxdot_translate_list_conj2.
Check boxdotTranslate_lconj.
Check boxdotTranslate_lconj2.
Check boxdotTranslate_fconj2.
Check boxdot_translate_box_iter_foundation_truth.
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
(** Primitive box/implication laws, model/frame closure, substitution, and
    inhabited-frame bottom counterexamples are constructive.  Quantifier
    counterexample extraction, derived diamond/Boolean readings, and modal
    duality expose exactly propositional excluded middle. *)
Print Assumptions whitepoint_finite.
Print Assumptions blackpoint_strict_order.
Print Assumptions kripke_satisfies_imp.
Print Assumptions kripke_not_satisfies_box.
Print Assumptions kripke_satisfies_list_conj.
Print Assumptions kripke_not_satisfies_indexed_list_conj.
Print Assumptions kripke_box_iter_equiv.
Print Assumptions kripke_dia_iter_dual.
Print Assumptions kripke_satisfies_substitute.
Print Assumptions kripke_model_valid_bottom.
Print Assumptions kripke_model_invalid_iff_exists_world.
Print Assumptions kripke_model_valid_multinec.
Print Assumptions kripke_valid_bottom.
Print Assumptions kripke_not_valid_iff_exists_valuation_world.
Print Assumptions kripke_valid_substitute.
Print Assumptions kripke_frame_class_invalid_iff_exists_model_world.
Print Assumptions kripke_frame_class_validates_with_K_nat.
(** Soundness packages inherit the classical propositional Hilbert basis;
    consistency from an inhabited sound frame and class comparison are
    otherwise closed. *)
Print Assumptions normal_soundness_of_frame_class_validates_axioms.
Print Assumptions normal_frame_class_sound_of_validates_axioms.
Print Assumptions normal_consistent_of_sound_frame_class.
Print Assumptions normal_consistent_of_sound_frame.
Print Assumptions normal_weaker_than_of_subset_frame_class.
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
Print Assumptions K_proves_nnformula_iff_neg.
Print Assumptions K_proves_exists_nnformula_iff.
Print Assumptions K_proves_exists_nnformula_of_provable.
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
Print Assumptions with_henkin_K4_weaker_than_K4Henkin.
Print Assumptions K4Henkin_weaker_than_with_henkin_K4.
Print Assumptions provable_with_henkin_K4_K4Henkin_iff.
Print Assumptions provable_GL_with_henkin_K4_iff.
Print Assumptions with_loeb_K4_weaker_than_K4Loeb.
Print Assumptions K4Loeb_weaker_than_with_loeb_K4.
Print Assumptions provable_with_loeb_K4_K4Loeb_iff.
Print Assumptions provable_GL_with_loeb_K4_iff.
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
(** The raw axiom API and membership-to-instance construction are entirely
    constructive.  Witness-bearing records live in Type to permit clients to
    build substitutions from their atoms. *)
Print Assumptions raw_axiom_instance_of_mem.
(** The capability hierarchy adds no substitution premise.  Classical
    propositional reasoning is visible only through the existing
    Prop-valued [classical_tautology] representation. *)
Print Assumptions conj_cons.
Print Assumptions has_DiaTc_of_E_T.
Print Assumptions multiDiaDuality.
Print Assumptions boxItrDuality.
Print Assumptions box_regularity_of_EM.
Print Assumptions EM_of_E_box_regularity.
Print Assumptions necessitation_of_EN.
Print Assumptions has_N_of_necessitation.
Print Assumptions has_K_of_EMC.
Print Assumptions k_entailment_of_EMCN.
Print Assumptions EMCN_of_k_entailment.
Print Assumptions has_Geach_dual.
Print Assumptions axiom_T_dual.
Print Assumptions axiom_Four_dual.
Print Assumptions axiom_Five_dual.
Print Assumptions has_C_of_EMK.
Print Assumptions has_P_of_END.
Print Assumptions diabot_raw.
Print Assumptions necessitation_of_ETB.
Print Assumptions has_Four_of_ET5.
Print Assumptions KP_axiomD.
Print Assumptions has_T_of_KT_prime.
Print Assumptions KT_of_KT_prime.
Print Assumptions KP_of_KT_prime.
Print Assumptions KD_of_KT_prime.
Print Assumptions ET_of_KT.
Print Assumptions KD_of_KT.
Print Assumptions reduce_box_in_CAnt_bang.
Print Assumptions iff_box_boxdot_raw.
Print Assumptions iff_dia_diadot_raw.
Print Assumptions diabox_box_raw.
Print Assumptions diabox_box_applied_raw.
Print Assumptions rm_diabox_raw.
Print Assumptions rm_diabox_applied_raw.
Print Assumptions lem1_diaT_of_S5Grz.
Print Assumptions lem2_diaT_of_S5Grz.
Print Assumptions normal_hilbert_axm.
Print Assumptions normal_hilbert_axm_substituted.
Print Assumptions normal_hilbert_axm_bang.
Print Assumptions normal_hilbert_lukasiewicz.
Print Assumptions normal_hilbert_necessitation.
Print Assumptions normal_hilbert_proves_substitute.
Print Assumptions normal_hilbert_proves_fold.
Print Assumptions normal_hilbert_weaker_of_provable_axioms.
Print Assumptions normal_hilbert_weaker_of_subset_axioms.
(** The source's definitional diamond-duality instance and all 25 raw-schema
    adapters are derived solely from the six raw constructors and template
    membership; no semantic completeness bridge is used. *)
Print Assumptions normal_hilbert_identity.
Print Assumptions normal_hilbert_and_intro.
Print Assumptions normal_hilbert_has_DiaDuality.
Print Assumptions normal_hilbert_instantiate_unary.
Print Assumptions normal_hilbert_instantiate_binary.
Print Assumptions normal_hilbert_has_K.
Print Assumptions normal_hilbert_is_normal.
Print Assumptions normal_hilbert_has_T.
Print Assumptions normal_hilbert_has_D.
Print Assumptions normal_hilbert_has_P.
Print Assumptions normal_hilbert_has_B.
Print Assumptions normal_hilbert_has_Four.
Print Assumptions normal_hilbert_has_FourN.
Print Assumptions normal_hilbert_has_Five.
Print Assumptions normal_hilbert_has_L.
Print Assumptions normal_hilbert_has_Z.
Print Assumptions normal_hilbert_has_Hen.
Print Assumptions normal_hilbert_has_Point2.
Print Assumptions normal_hilbert_has_WeakPoint2.
Print Assumptions normal_hilbert_has_Point3.
Print Assumptions normal_hilbert_has_WeakPoint3.
Print Assumptions normal_hilbert_has_Point4.
Print Assumptions normal_hilbert_has_Grz.
Print Assumptions normal_hilbert_has_Dum.
Print Assumptions normal_hilbert_has_Tc.
Print Assumptions normal_hilbert_has_Ver.
Print Assumptions normal_hilbert_has_McK.
Print Assumptions normal_hilbert_has_Mk.
Print Assumptions normal_hilbert_has_H.
Print Assumptions normal_hilbert_has_Geach.
(** The first three named raw systems and all their compatibility bridges are
    constructorwise and closed under the global context. *)
Print Assumptions structural_k_of_normal.
Print Assumptions normal_K_axioms_has_K.
Print Assumptions normal_K_entailment.
Print Assumptions normal_K_weaker_than_structural_normal.
Print Assumptions normal_KT_axioms_has_K.
Print Assumptions normal_KT_axioms_has_T.
Print Assumptions normal_KT_entailment.
Print Assumptions normal_KD_axioms_has_K.
Print Assumptions normal_KD_axioms_has_D.
Print Assumptions normal_KD_entailment.
Print Assumptions normal_K_to_K_normal_proves.
Print Assumptions K_normal_proves_to_normal_K.
Print Assumptions normal_K_iff_K_normal_proves.
Print Assumptions normal_K_equiv_K_normal_proves.
Print Assumptions normal_KT_to_KT_proves.
Print Assumptions KT_proves_to_normal_KT.
Print Assumptions normal_KT_iff_KT_proves.
Print Assumptions normal_KT_equiv_KT_proves.
Print Assumptions normal_KD_to_KD_proves.
Print Assumptions KD_proves_to_normal_KD.
Print Assumptions normal_KD_iff_KD_proves.
Print Assumptions normal_KD_equiv_KD_proves.
(** KP, KB, KDB, and KTB use only the raw calculus.  The KP/KD equivalence
    and KB compatibility bridge are closed, syntactic translations. *)
Print Assumptions normal_KP_axioms_has_K.
Print Assumptions normal_KP_axioms_has_P.
Print Assumptions normal_KP_entailment.
Print Assumptions normal_KP_equiv_KD.
Print Assumptions normal_KB_axioms_has_K.
Print Assumptions normal_KB_axioms_has_B.
Print Assumptions normal_KB_entailment.
Print Assumptions normal_KDB_axioms_has_K.
Print Assumptions normal_KDB_axioms_has_D.
Print Assumptions normal_KDB_axioms_has_B.
Print Assumptions normal_KDB_entailment.
Print Assumptions normal_KTB_axioms_has_K.
Print Assumptions normal_KTB_axioms_has_T.
Print Assumptions normal_KTB_axioms_has_B.
Print Assumptions normal_KTB_entailment.
Print Assumptions normal_KB_to_KB_proves.
Print Assumptions KB_proves_to_normal_KB.
Print Assumptions normal_KB_iff_KB_proves.
Print Assumptions normal_KB_equiv_KB_proves.
(** K4/K4n witnesses, structural bundles, and the K4 bridge are likewise
    closed and syntactic. *)
Print Assumptions normal_K4_axioms_has_K.
Print Assumptions normal_K4_axioms_has_Four.
Print Assumptions normal_K4_entailment.
Print Assumptions normal_K4n_axioms_has_K.
Print Assumptions normal_K4n_axioms_has_FourN.
Print Assumptions normal_K4n_entailment.
Print Assumptions normal_K4_to_K4_proves.
Print Assumptions K4_proves_to_normal_K4.
Print Assumptions normal_K4_iff_K4_proves.
Print Assumptions normal_K4_equiv_K4_proves.
(** Both McKinsey systems and the generic theorem-inclusion lift are
    constructive and closed under the global context. *)
Print Assumptions normal_KMcK_axioms_has_K.
Print Assumptions normal_KMcK_axioms_has_McK.
Print Assumptions normal_KMcK_entailment.
Print Assumptions normal_K4McK_axioms_has_K.
Print Assumptions normal_K4McK_axioms_has_Four.
Print Assumptions normal_K4McK_axioms_has_McK.
Print Assumptions normal_K4McK_entailment.
Print Assumptions normal_K4McK_entailment_of_subset.
(** The two weak-point raw systems and their structural bundles are also
    constructive and closed under the global context. *)
Print Assumptions normal_K4Point2_axioms_has_K.
Print Assumptions normal_K4Point2_axioms_has_Four.
Print Assumptions normal_K4Point2_axioms_has_WeakPoint2.
Print Assumptions normal_K4Point2_entailment.
Print Assumptions normal_K4Point3_axioms_has_K.
Print Assumptions normal_K4Point3_axioms_has_Four.
Print Assumptions normal_K4Point3_axioms_has_WeakPoint3.
Print Assumptions normal_K4Point3_entailment.
(** The exact KT4B, K45, KD4, and KD5 witnesses and bundles are likewise
    constructive and closed under the global context. *)
Print Assumptions normal_KT4B_axioms_has_K.
Print Assumptions normal_KT4B_axioms_has_T.
Print Assumptions normal_KT4B_axioms_has_Four.
Print Assumptions normal_KT4B_axioms_has_B.
Print Assumptions normal_KT4B_entailment.
Print Assumptions normal_K45_axioms_has_K.
Print Assumptions normal_K45_axioms_has_Four.
Print Assumptions normal_K45_axioms_has_Five.
Print Assumptions normal_K45_entailment.
Print Assumptions normal_KD4_axioms_has_K.
Print Assumptions normal_KD4_axioms_has_D.
Print Assumptions normal_KD4_axioms_has_Four.
Print Assumptions normal_KD4_entailment.
Print Assumptions normal_KD5_axioms_has_K.
Print Assumptions normal_KD5_axioms_has_D.
Print Assumptions normal_KD5_axioms_has_Five.
Print Assumptions normal_KD5_entailment.
(** The exact KD45, KB4, and KB5 raw witnesses and structural bundles are
    constructive and closed under the global context. *)
Print Assumptions normal_KD45_axioms_has_K.
Print Assumptions normal_KD45_axioms_has_D.
Print Assumptions normal_KD45_axioms_has_Four.
Print Assumptions normal_KD45_axioms_has_Five.
Print Assumptions normal_KD45_entailment.
Print Assumptions normal_KB4_axioms_has_K.
Print Assumptions normal_KB4_axioms_has_B.
Print Assumptions normal_KB4_axioms_has_Four.
Print Assumptions normal_KB4_entailment.
Print Assumptions normal_KB5_axioms_has_K.
Print Assumptions normal_KB5_axioms_has_B.
Print Assumptions normal_KB5_axioms_has_Five.
Print Assumptions normal_KB5_entailment.
(** S4, S4McK, and both source inclusions are wholly syntactic and closed
    under the global context. *)
Print Assumptions normal_S4_axioms_has_K.
Print Assumptions normal_S4_axioms_has_T.
Print Assumptions normal_S4_axioms_has_Four.
Print Assumptions normal_S4_entailment.
Print Assumptions normal_K4_weaker_than_normal_S4.
Print Assumptions normal_S4McK_axioms_has_K.
Print Assumptions normal_S4McK_axioms_has_T.
Print Assumptions normal_S4McK_axioms_has_Four.
Print Assumptions normal_S4McK_axioms_has_McK.
Print Assumptions normal_S4McK_entailment.
Print Assumptions normal_K4McK_weaker_than_normal_S4McK.
(** All three S4 point/McKinsey systems and their K4McK inclusions are
    constructive and closed under the global context. *)
Print Assumptions normal_S4Point2McK_axioms_has_K.
Print Assumptions normal_S4Point2McK_axioms_has_T.
Print Assumptions normal_S4Point2McK_axioms_has_Four.
Print Assumptions normal_S4Point2McK_axioms_has_McK.
Print Assumptions normal_S4Point2McK_axioms_has_Point2.
Print Assumptions normal_S4Point2McK_entailment.
Print Assumptions normal_K4McK_weaker_than_normal_S4Point2McK.
Print Assumptions normal_S4Point3McK_axioms_has_K.
Print Assumptions normal_S4Point3McK_axioms_has_T.
Print Assumptions normal_S4Point3McK_axioms_has_Four.
Print Assumptions normal_S4Point3McK_axioms_has_McK.
Print Assumptions normal_S4Point3McK_axioms_has_Point3.
Print Assumptions normal_S4Point3McK_entailment.
Print Assumptions normal_K4McK_weaker_than_normal_S4Point3McK.
Print Assumptions normal_S4Point4McK_axioms_has_K.
Print Assumptions normal_S4Point4McK_axioms_has_T.
Print Assumptions normal_S4Point4McK_axioms_has_Four.
Print Assumptions normal_S4Point4McK_axioms_has_McK.
Print Assumptions normal_S4Point4McK_axioms_has_Point4.
Print Assumptions normal_S4Point4McK_entailment.
Print Assumptions normal_K4McK_weaker_than_normal_S4Point4McK.
(** K5 and S5 remain constructive raw systems with closed witnesses and
    structural bundles. *)
Print Assumptions normal_K5_axioms_has_K.
Print Assumptions normal_K5_axioms_has_Five.
Print Assumptions normal_K5_entailment.
Print Assumptions normal_S5_axioms_has_K.
Print Assumptions normal_S5_axioms_has_T.
Print Assumptions normal_S5_axioms_has_Five.
Print Assumptions normal_S5_entailment.
(** Both rule calculi, including their raw-template adapters and concrete
    structural bundles, are constructive. *)
Print Assumptions with_henkin_axm_substituted.
Print Assumptions with_henkin_axm.
Print Assumptions with_henkin_lukasiewicz.
Print Assumptions with_henkin_necessitation.
Print Assumptions with_henkin_henkin_rule.
Print Assumptions with_henkin_proves_substitute.
Print Assumptions with_henkin_proves_fold.
Print Assumptions with_henkin_weaker_of_provable_axioms.
Print Assumptions with_henkin_weaker_of_subset_axioms.
Print Assumptions with_henkin_instantiate_unary.
Print Assumptions with_henkin_instantiate_binary.
Print Assumptions with_henkin_has_K.
Print Assumptions with_henkin_has_Four.
Print Assumptions with_henkin_identity.
Print Assumptions with_henkin_and_intro.
Print Assumptions with_henkin_has_DiaDuality.
Print Assumptions with_henkin_K4_axioms_has_K.
Print Assumptions with_henkin_K4_axioms_has_Four.
Print Assumptions with_henkin_K4_entailment.
Print Assumptions with_loeb_axm_substituted.
Print Assumptions with_loeb_axm.
Print Assumptions with_loeb_lukasiewicz.
Print Assumptions with_loeb_necessitation.
Print Assumptions with_loeb_loeb_rule.
Print Assumptions with_loeb_proves_substitute.
Print Assumptions with_loeb_proves_fold.
Print Assumptions with_loeb_weaker_of_provable_axioms.
Print Assumptions with_loeb_weaker_of_subset_axioms.
Print Assumptions with_loeb_has_K.
Print Assumptions with_loeb_has_Four.
Print Assumptions with_loeb_K4_axioms_has_K.
Print Assumptions with_loeb_K4_axioms_has_Four.
Print Assumptions with_loeb_K4Loeb_entailment.
Print Assumptions with_re_lukasiewicz.
Print Assumptions with_re_proves_substitute.
Print Assumptions with_re_proves_dependent_fold.
Print Assumptions with_re_weaker_of_provable_axioms.
Print Assumptions with_re_e_entailment.
Print Assumptions with_re_has_M.
Print Assumptions with_re_has_D.
Print Assumptions with_re_has_B.
Print Assumptions with_re_has_Five.
Print Assumptions with_re_empty_classical_complete.
Print Assumptions with_re_classical_complete_weaken.
Print Assumptions with_re_e_entailment_from_basis.
Print Assumptions with_re_EMCN_entailment.
Print Assumptions with_re_EMCNT_emc_entailment.
Print Assumptions with_re_EMCNT_en_entailment.
Print Assumptions with_re_EMCNT4_emc_entailment.
Print Assumptions with_re_EMCNT4_en_entailment.
Print Assumptions with_re_EM_entailment.
Print Assumptions with_re_EC_entailment.
Print Assumptions with_re_EN_entailment.
Print Assumptions with_re_EMC_entailment.
Print Assumptions with_re_EMN_entailment.
Print Assumptions with_re_ECN_entailment.
Print Assumptions with_re_EK_entailment.
Print Assumptions with_re_E4_e4_entailment.
Print Assumptions with_re_EN4_en_entailment.
Print Assumptions with_re_E4_weaker_than_EN4.
Print Assumptions with_re_ET4_et_entailment.
Print Assumptions with_re_ENT4_e4_entailment.
Print Assumptions with_re_ED_has_D.
Print Assumptions with_re_END_entailment.
Print Assumptions with_re_END4_source_END_entailment.
Print Assumptions with_re_EMND4_em_entailment.
Print Assumptions with_re_EP_has_P.
Print Assumptions with_re_EB_entailment.
Print Assumptions with_re_ETB_entailment.
Print Assumptions with_re_ETB_en_entailment.
Print Assumptions with_re_ENTB_en_entailment.
Print Assumptions with_re_ETB_equiv_ENTB.
Print Assumptions with_re_E5_entailment.
Print Assumptions with_re_ET5_entailment.
Print Assumptions with_re_ET_entailment.
Print Assumptions with_re_EMT_entailment.
Print Assumptions with_re_EMK_entailment.
Print Assumptions with_re_EMK_equiv_EMCK.
Print Assumptions with_re_EMC_equiv_EMCK.
Print Assumptions with_re_EMT4_entailment.
Print Assumptions with_re_EMNT4_em_entailment.
Print Assumptions with_re_EMNT4_en_entailment.
Print Assumptions with_re_EMNT4_et_entailment.
Print Assumptions with_re_EMNT4_e4_entailment.
Print Assumptions with_re_EMC4_entailment.
Print Assumptions with_re_EMCN4_emc_entailment.
Print Assumptions with_re_normal_equiv_of_provable_generators.
Print Assumptions with_re_EMCN_equiv_K.
Print Assumptions with_re_EMCNT_equiv_KT.
Print Assumptions with_re_EMCNT4_equiv_S4.
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
(** Canonical finite ranks inherit only the explicit classical height and
    finite-subtype selection boundaries audited below.  Algebraic rank
    uniqueness and the direct extension laws add no project-local axiom; in
    particular, Foundation's point-generated rank axiom is a theorem here. *)
Print Assumptions frame_rank_spec_converse_well_founded.
Print Assumptions finite_cwf_frame_rank_spec.
Print Assumptions frame_rank_spec_unique.
Print Assumptions point_generated_finite_enumeration.
Print Assumptions point_generated_frame_is_tree.
Print Assumptions finite_cwf_point_generated_rank_original.
Print Assumptions extend_root_finite_enumeration.
Print Assumptions finite_cwf_extend_root_rank_original.
Print Assumptions extend_root_algebraic_rank_spec.
Print Assumptions finite_cwf_extend_root_rank_eq_algebraic.
Print Assumptions finite_cwf_extend_root_height_eq.
Print Assumptions finite_cwf_one_root_height_successor.
Print Assumptions finite_cwf_extend_root_eq_base_height_iff.
Print Assumptions balloon_covers_envelope.
Print Assumptions farthest_counterexample_of_not_box.
Print Assumptions balloon_validates_Z_of_cwf.

Print Assumptions valid_WeakPoint2_atoms_iff_piecewise_convergent.
Print Assumptions valid_WeakPoint3_atoms_iff_piecewise_connected.

(** The complete elementary relation layer is constructive. *)
Print Assumptions rel_iter_prefix_transitive_positive.
Print Assumptions relation_refl_gen_partial_order.
Print Assumptions relation_trans_gen_remove_iterate.
Print Assumptions relation_refl_trans_gen_remove_iterate.
Print Assumptions relation_irreflexive_generator_strict_order.
Print Assumptions relation_equality_piecewise_strongly_connected.
Print Assumptions relation_reflexive_of_symmetric_transitive_serial.
Print Assumptions relation_transitive_of_reflexive_right_euclidean.
Print Assumptions relation_piecewise_strongly_convergent_of_reflexive_connected.
Print Assumptions relation_isolated_transitive.
Print Assumptions relation_universal_right_euclidean.

(** Maximality and finite CWF use excluded middle.  The noncomputable height
    additionally uses definite description to filter an explicit finite
    cover; no proof irrelevance or functional extensionality is inherited. *)
Print Assumptions converse_well_founded.
Print Assumptions is_converse_well_founded.
Print Assumptions converse_well_founded_iff_has_max.
Print Assumptions converse_well_founded_has_max.
Print Assumptions finite_converse_well_founded_of_transitive_irreflexive.
Print Assumptions finite_transitive_irreflexive_is_converse_well_founded.
Print Assumptions cwf_height.
Print Assumptions cwf_height_eq.
Print Assumptions cwf_height_gt_of.
Print Assumptions cwf_height_eq_zero_iff.
Print Assumptions cwf_height_le.
Print Assumptions lt_cwf_height.
Print Assumptions cwf_height_eq_of_lt_of_le.
Print Assumptions cwf_height_eq_succ.
Print Assumptions cwf_height_eq_succ_cwf_height.
Print Assumptions cwf_height_lt.
Print Assumptions cwf_height_congr.

(** Choice is confined to the exact source chain-construction helper.  The
    other nonconstructive WCWF results use only excluded middle. *)
Print Assumptions weakly_converse_well_founded.
Print Assumptions is_weakly_converse_well_founded.
Print Assumptions wcwf_dependent_choice.
Print Assumptions finite_exists_ne_map_eq_of_infinite_lt.
Print Assumptions antisymmetric_of_weakly_converse_well_founded.
Print Assumptions weakly_converse_well_founded_is_antisymmetric.
Print Assumptions weakly_converse_well_founded_of_finite_transitive_antisymmetric.
Print Assumptions finite_transitive_antisymmetric_is_weakly_converse_well_founded.

(** The doubled-frame p-morphism is constructive.  Boxdot itself uses the
    classically encoded derived conjunction, so its semantic truth laws expose
    excluded middle.  The atom-polymorphic Hilbert translation additionally
    inherits the definite-description boundary of local K completeness.
    Reverse
    reflexivization and the logical SBDP argument also use excluded middle.
    GL/Grz and GL.3 completeness are now checked above.  The remaining Grz.3
    argument stays visible in its theorem type.  Jeřábek's discharged bridge
    uses the global-consequence and filtration boundaries audited below. *)
Print Assumptions boxdot_reflexive_closure_truth.
Print Assumptions boxdot_translate_idempotent_truth.
Print Assumptions boxdot_translate_list_conj2.
Print Assumptions boxdot_translate_box_iter_foundation_truth.
Print Assumptions normal_proves_boxdot_translation.
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
