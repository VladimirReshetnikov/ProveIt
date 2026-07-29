(** Public surface and kernel-assumption audit for the generic Foundation port. *)

From Foundation.Syntax.Predicate Require Import Language Term Quantifier.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.Syntax.Predicate Require Import Rew.
From Foundation.Syntax.Predicate Require Import Relational.

Check language.
Check language_relational.
Check language_is_constant.
Check empty_language.
Check graph_language.
Check binary_language.
Check equality_language.
Check oring_language.
Check constant_language.
Check language_add.
Check language_sigma.
Check language_oring.
Check oring_language_structure.
Check language_hom.
Check language_hom_id.
Check language_hom_comp.
Check language_hom_add_left.
Check language_hom_add_right.
Check language_hom_sigma.
Check language_hom_add_left_func.
Check language_hom_add_left_rel.
Check language_hom_add_right_func.
Check language_hom_add_right_rel.
Check language_hom_sigma_func.
Check language_hom_sigma_rel.
Check language_hom_ext.
Check language_hom_comp_id_left.
Check language_hom_comp_id_right.
Check language_hom_comp_assoc.
Check oring_embedding.
Check language_decidable_eq.
Check equality_language_decidable_eq.
Check oring_language_decidable_eq.
Check encoding.
Check equality_language_encodable.
Check oring_language_encodable.
Check finite_cover.
Check language_finite.
Check oring_language_finite.

Check semiterm.
Check term.
Check closed_semiterm.
Check syntactic_term.
Check semiterm_from_free_default.
Check semiterm_from_constant.
Check fin_pointwise_eq_dec.
Check fin_function_eq_dec.
Check fin_function_pointwise_eq_dec.
Check semiterm_eq_dec.
Check semiterm_complexity.
Check semiterm_complexity_func_lt.
Check semiterm_bound_occurs.
Check semiterm_positive.
Check semiterm_positive_func.
Check semiterm_no_bound_occurs_of_positive_one.
Check semiterm_free_occurs.
Check semiterm_language_map.
Check semiterm_language_map_positive.
Check semiterm_language_map_free_occurs.
Check semiterm_language_map_id.
Check semiterm_language_map_comp.
Check semiterm_free_variable_list.
Check semiterm_free_variable_list_spec.
Check semiterm_index_of_free_variable.
Check semiterm_enumerate_free_variable.
Check semiterm_enumerate_index_of_free_variable.

Check polarity_alt_involutive.
Check sigma_pi_delta_alt_involutive.
Check sigma_pi_delta_alt_polarity.
Check first_universal_quantifier.
Check first_existential_quantifier.
Check first_quantifiers.
Check first_connectives_with_quantifiers.
Check first_all_closure.
Check first_all_iter.
Check first_exists_closure.
Check first_exists_iter.
Check first_bounded_all.
Check first_bounded_exists.
Check second_universal_quantifier.
Check second_existential_quantifier.
Check second_quantifiers.
Check second_connectives_with_quantifiers.
Check second_all_closure.
Check second_all_iter.
Check second_exists_closure.
Check second_exists_iter.
Check second_bounded_all.
Check second_bounded_exists.

Check semiformula.
Check semiformula_connectives.
Check semiformula_lcwq.
Check semiformula_neg_involutive.
Check semiformula_neg_all_closure.
Check semiformula_neg_exists_closure.
Check semiformula_neg_bounded_all.
Check semiformula_all_closure_injective.
Check semiformula_all_iter_injective.
Check semiformula_complexity.
Check semiformula_quantifier_rank.
Check semiformula_open.
Check semiformula_eq_dec.
Check semiformula_free_occurs.
Check semiformula_free_variable_list_spec.
Check semiformula_fv_sup_fresh.
Check semiformula_language_map.
Check semiformula_language_connective_hom.
Check semiformula_language_map_free_occurs.
Check semiformula_language_map_id.
Check semiformula_language_map_comp.
Check semiformula_language_map_all_iter.
Check semiformula_language_map_free_variable_list.
Check semiformula_enumerate_index_of_free_variable.
Check theory_language_map.

Check rew.
Check rew_equiv.
Check rew_id.
Check rew_comp.
Check rew_comp_assoc.
Check rew_bind.
Check rew_eta.
Check rew_equiv_of_variables.
Check rew_rewrite.
Check rew_rewrite_map.
Check rew_map.
Check rew_subst.
Check rew_emb.
Check rew_emb_substs.
Check rew_cast.
Check fin_cast_refl.
Check fin_cast_L_zero.
Check fin_cast_le.
Check fin_cast_le_refl.
Check rew_cast_le.
Check rew_cast_refl.
Check rew_cast_le_refl.
Check rew_subst_comp_subst.
Check rew_subst_comp_emb_substs.
Check rew_emb_substs_variables.
Check rew_rewrite_comp_rewrite.
Check rew_bshift.
Check rew_bshift_add.
Check rew_bshift_add_zero_cast.
Check rew_bshift_comp_subst.
Check rew_shift_comp_subst.
Check rew_rewrite_comp_emb.
Check rew_shift_comp_emb.
Check rew_comp_emb_empty.
Check rew_subst_bound_occurs.
Check rew_subst_positive.
Check rew_emb_substs_bound_occurs.
Check rew_emb_substs_positive.
Check rew_q.
Check rew_q_bshift_apply.
Check rew_q_comp_apply.
Check rew_q_respects_equiv.
Check rew_qpow.
Check rew_shift.
Check rew_free.
Check rew_fix.
Check rew_shift_injective.
Check rew_free_comp_fix.
Check rew_fix_comp_free.
Check rew_free_bshift_eq_shift.
Check rew_bshift_positive.
Check rew_bshift_free_occurs.
Check rew_free_occurs_sources.
Check semiterm_language_map_rew_bind.
Check semiterm_language_map_rew_bshift.
Check semiterm_language_map_rew_shift.
Check semiterm_language_map_rew_free.
Check semiterm_language_map_rew_fix.
Check rew_q_shift.
Check rew_fix_iter.
Check rew_fix_iter_zero.
Check rew_fix_iter_succ.
Check rew_fix_iter_bvar.
Check rew_fix_iter_fvar_ge.
Check rew_fix_iter_fvar_lt.
Check semiterm_to_closed.
Check semiterm_emb_to_closed.
Check semiterm_emb_no_free_occurs.
Check semiterm_to_closed_emb.
Check semiformula_rewrite.
Check semiformula_rewrite_connective_hom.
Check semiformula_rewrite_all.
Check semiformula_rewrite_ext.
Check semiformula_rewrite_id.
Check semiformula_rewrite_comp.
Check semiformula_rewrite_all_iter.
Check semiformula_rewrite_exists_iter.
Check semiformula_rewrite_bounded_all.
Check semiformula_rewrite_complexity.
Check semiformula_rewrite_quantifier_rank.
Check semiformula_rewrite_open.
Check semiformula_rewrite_free_occurs_sources.
Check semiformula_substitute.
Check semiformula_substitute_id.
Check semiformula_substitute_comp.
Check semiformula_shift_injective.
Check semiformula_free_fix.
Check semiformula_fix_free.
Check rew_q_emb.
Check semiformula_to_closed.
Check semiformula_emb_to_closed.
Check semiformula_emb_no_free_occurs.
Check semiformula_free_bound.
Check semiformula_fix_all_free.
Check semiformula_fix_all_free_no_free.
Check semiformula_universal_closure_open.
Check semiformula_universal_closure_open_no_free.
Check semiformula_universal_closure.
Check semiformula_emb_universal_closure.
Check semiformula_universal_closure_open_id.

Check semiterm_bvar_or_fvar_relational.
Check term_fvar_relational.
Check fin_cons.
Check semiterm_relational_val.
Check semiterm_relational_val_bvar.
Check semiterm_relational_val_fvar.
Check semiterm_relational_val_rew.
Check semiterm_relational_val_bshift.

Print Assumptions language_hom_ext.
Print Assumptions language_hom_comp_assoc.
Print Assumptions oring_function_symbols_complete.
Print Assumptions oring_language_finite.
Print Assumptions fin_function_pointwise_eq_dec.
Print Assumptions semiterm_eq_dec.
Print Assumptions semiterm_complexity_func_lt.
Print Assumptions semiterm_language_map_positive.
Print Assumptions semiterm_language_map_comp.
Print Assumptions semiterm_free_variable_list_spec.
Print Assumptions semiterm_enumerate_index_of_free_variable.
Print Assumptions semiterm_language_map_free_variable_list.
Print Assumptions polarity_alt_involutive.
Print Assumptions first_all_iter_succ.
Print Assumptions first_exists_iter_succ.
Print Assumptions second_all_iter_succ.
Print Assumptions second_exists_iter_succ.
Print Assumptions semiformula_neg_involutive.
Print Assumptions semiformula_neg_all_closure.
Print Assumptions semiformula_all_iter_injective.
Print Assumptions semiformula_eq_dec.
Print Assumptions semiformula_fv_sup_fresh.
Print Assumptions semiformula_language_connective_hom.
Print Assumptions semiformula_language_map_free_occurs.
Print Assumptions semiformula_language_map_id.
Print Assumptions semiformula_language_map_comp.
Print Assumptions semiformula_enumerate_index_of_free_variable.
Print Assumptions rew_comp_assoc.
Print Assumptions rew_eta.
Print Assumptions rew_equiv_of_variables.
Print Assumptions rew_subst_comp_subst.
Print Assumptions rew_subst_comp_emb_substs.
Print Assumptions rew_emb_substs_variables.
Print Assumptions rew_cast_refl.
Print Assumptions rew_cast_le_refl.
Print Assumptions rew_bshift_add_zero_cast.
Print Assumptions rew_bshift_comp_subst.
Print Assumptions rew_shift_comp_subst.
Print Assumptions rew_rewrite_comp_emb.
Print Assumptions rew_comp_emb_empty.
Print Assumptions rew_subst_bound_occurs.
Print Assumptions rew_subst_positive.
Print Assumptions rew_emb_substs_bound_occurs.
Print Assumptions rew_emb_substs_positive.
Print Assumptions rew_q_bshift_apply.
Print Assumptions rew_q_comp_apply.
Print Assumptions rew_fix_iter_zero.
Print Assumptions rew_fix_iter_bvar.
Print Assumptions rew_fix_iter_fvar_ge.
Print Assumptions rew_fix_iter_fvar_lt.
Print Assumptions semiterm_emb_to_closed.
Print Assumptions semiterm_emb_no_free_occurs.
Print Assumptions semiterm_to_closed_emb.
Print Assumptions rew_shift_injective.
Print Assumptions rew_free_comp_fix.
Print Assumptions rew_fix_comp_free.
Print Assumptions rew_bshift_positive.
Print Assumptions rew_free_occurs_sources.
Print Assumptions semiterm_language_map_rew_bind.
Print Assumptions semiformula_rewrite_connective_hom.
Print Assumptions semiformula_rewrite_ext.
Print Assumptions semiformula_rewrite_id.
Print Assumptions semiformula_rewrite_comp.
Print Assumptions semiformula_rewrite_all_iter.
Print Assumptions semiformula_rewrite_complexity.
Print Assumptions semiformula_rewrite_quantifier_rank.
Print Assumptions semiformula_rewrite_open.
Print Assumptions semiformula_rewrite_free_occurs_sources.
Print Assumptions semiformula_substitute_comp.
Print Assumptions semiformula_shift_injective.
Print Assumptions semiformula_free_fix.
Print Assumptions semiformula_fix_free.
Print Assumptions rew_q_emb.
Print Assumptions semiformula_emb_to_closed.
Print Assumptions semiformula_emb_no_free_occurs.
Print Assumptions semiformula_fix_all_free_no_free.
Print Assumptions semiformula_universal_closure_open_no_free.
Print Assumptions semiformula_emb_universal_closure.
Print Assumptions semiformula_universal_closure_open_id.
Print Assumptions semiterm_bvar_or_fvar_relational.
Print Assumptions term_fvar_relational.
Print Assumptions semiterm_relational_val_rew.
Print Assumptions semiterm_relational_val_bshift.
