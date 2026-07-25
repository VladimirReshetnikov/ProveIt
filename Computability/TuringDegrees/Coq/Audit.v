From TuringDegrees Require Import ComputablyEnumerable Core DegreeNotions Join
  Jump Limit PostProblem PostTheorem Structure.

(** This file is deliberately executable documentation: compiling it checks
    the public surface and [Print Assumptions] reports any global axioms on
    which the proofs depend.  EPF, encodings, Markov's principle, restricted
    excluded middle, definiteness, and the Post-problem principle occur as
    theorem parameters rather than hidden axioms. *)

Check turing_reducible_PreOrder.
Check turing_equiv_Equivalence.
Check turing_degree_PartialOrder.
Check empty_set_least.
Check zero_degree_iff_decidable.

Check turing_join_spec.
Check turing_join_is_lub.
Check turing_join_commutative.
Check turing_join_associative.

Check turing_jump_monotone.
Check turing_jump_strict.
Check zero_jump_nonzero.

Check kleene_post_incomparable.
Check kleene_post_from_epf.
Check turing_degrees_not_linear.

Check is_minimal_degree.
Check minimal_degree_not_dense.
Check is_greatest_lower_bound.
Check is_ce_greatest_lower_bound.
Check is_sequence_lub.
Check is_exact_pair.
Check exact_pair_no_sequence_lub.
Check eventually_approximates.
Check has_change_bound.
Check has_change_bound_mono.
Check is_n_computably_enumerable.
Check is_n_computably_enumerable_mono.

Check ce_iff_many_one_zero_jump.
Check ce_degree_turing_reducible_zero_jump.
Check zero_jump_ce_complete.
Check complement_zero_jump_not_computably_enumerable.

Check shoenfield_limit_lemma.
Check standard_iterated_jump_sigma.
Check posts_theorem_sigma_many_one_complete.
Check posts_theorem_oracle_ce.
Check solves_posts_problem.
Check posts_problem_conditional.
Check posts_problem_solution.

Print Assumptions empty_set_least.
Print Assumptions turing_degree_PartialOrder.
Print Assumptions zero_degree_iff_decidable.
Print Assumptions turing_join_spec.
Print Assumptions turing_join_is_lub.
Print Assumptions turing_join_commutative.
Print Assumptions turing_join_associative.
Print Assumptions turing_jump_monotone.
Print Assumptions turing_jump_strict.
Print Assumptions zero_jump_nonzero.
Print Assumptions kleene_post_incomparable.
Print Assumptions kleene_post_from_epf.
Print Assumptions turing_degrees_not_linear.
Print Assumptions minimal_degree_not_dense.
Print Assumptions exact_pair_no_sequence_lub.
Print Assumptions is_n_computably_enumerable_mono.
Print Assumptions ce_iff_many_one_zero_jump.
Print Assumptions ce_degree_turing_reducible_zero_jump.
Print Assumptions zero_jump_ce_complete.
Print Assumptions complement_zero_jump_not_computably_enumerable.
Print Assumptions shoenfield_limit_lemma.
Print Assumptions standard_iterated_jump_sigma.
Print Assumptions posts_theorem_sigma_many_one_complete.
Print Assumptions posts_theorem_oracle_ce.
Print Assumptions posts_problem_conditional.
Print Assumptions posts_problem_solution.
