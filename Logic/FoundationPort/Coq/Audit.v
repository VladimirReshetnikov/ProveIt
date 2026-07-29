(** Public surface and kernel-assumption audit for the generic Foundation port. *)

From Foundation.Syntax.Predicate Require Import Language Term.

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

Print Assumptions language_hom_ext.
Print Assumptions language_hom_comp_assoc.
Print Assumptions oring_function_symbols_complete.
Print Assumptions oring_language_finite.
Print Assumptions semiterm_complexity_func_lt.
Print Assumptions semiterm_language_map_positive.
Print Assumptions semiterm_language_map_comp.
Print Assumptions semiterm_free_variable_list_spec.
Print Assumptions semiterm_enumerate_index_of_free_variable.
