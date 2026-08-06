(** Public surface and kernel-assumption audit for the generic Foundation port. *)

From Foundation.Vorspiel Require Import ExistsUnique.
From Foundation.Vorspiel Require Import Basic.
From Foundation.Vorspiel Require Import NotationClass.
From Foundation.Vorspiel Require Import Quotient.
From Foundation.Vorspiel Require Import Small.
From Foundation.Vorspiel Require Import String.
From Foundation.Vorspiel Require Import Fintype.
From Foundation.Vorspiel Require Import Denumerable.
From Foundation.Vorspiel Require Import Graph.
From Foundation.Vorspiel Require Import Part.
From Foundation.Vorspiel Require Import Computability.
From Foundation.Vorspiel Require Import ENat.
From Foundation.Vorspiel Require Import DMatrix.
From Foundation.Vorspiel Require Import Matrix.
From Foundation.Vorspiel Require Import Arithmetic.
From Foundation.Vorspiel Require Import BetaEncoding.
From Foundation.FirstOrder.Incompleteness Require Import ProvabilityAbstraction.
From Foundation.FirstOrder.Incompleteness Require Import Height.
From Foundation.FirstOrder.Incompleteness Require Import Tarski.
From Foundation.FirstOrder.Incompleteness Require Import Dense.
From Foundation.FirstOrder.Incompleteness Require Import First.
From Foundation.FirstOrder.Incompleteness Require Import Halting.
From Foundation.FirstOrder.Incompleteness Require Import WitnessComparison.
From Foundation.FirstOrder.Incompleteness Require Import RosserProvability.
From Foundation.FirstOrder.Incompleteness Require Import Jeroslow.
From Foundation.FirstOrder.Incompleteness Require Import Consistency.
From Foundation.FirstOrder.Incompleteness Require Import RestrictedProvability.
From Foundation.FirstOrder.Incompleteness Require Import StandardProvability.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Language.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Functions.
From Foundation.FirstOrder.Bootstrapping.Syntax.Term Require Import Typed Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Functions.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Typed Coding.
From Foundation.FirstOrder.Bootstrapping.Syntax.Formula Require Import Iteration.
From Foundation.FirstOrder.Bootstrapping.Syntax Require Import Theory.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Basic.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Typed.
From Foundation.FirstOrder.Bootstrapping.Syntax.Proof Require Import Coding.
From Foundation.FirstOrder.Bootstrapping Require Import Syntax.
From Foundation.FirstOrder.Bootstrapping Require Import FixedPoint.
From Foundation.FirstOrder.Bootstrapping.DerivabilityCondition Require Import
  D1 D2 D3 EquationalTheory PeanoMinus.
From Foundation.FirstOrder.Basic Require Import BinderNotation.
From Foundation.FirstOrder Require Import Basic.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic Coding Seq SeqChoice BigOps Relation PRF FixedPoint Raw.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Vec.
From Foundation.FirstOrder.Arithmetic Require Import HFS.
From Foundation.FirstOrder.Arithmetic.Exponential Require Import
  Pow2 PPow2 Exp Bit Log.
From Foundation.FirstOrder.Arithmetic Require Import Exponential.
From Foundation.FirstOrder.Arithmetic.Omega1 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Omega1 Require Import Nuon.
From Foundation.FirstOrder.Arithmetic Require Import Induction.
From Foundation.FirstOrder.SetTheory Require Import Basic TransitiveModel Z Function Ordinal Universe.
From Foundation.FirstOrder.Skolemization Require Import Hull.
From Foundation.FirstOrder.SetTheory Require Import LoewenheimSkolem.
From Foundation.FirstOrder Require Import Interpretation.
From Foundation.Vorspiel.Fin Require Import Basic.
From Foundation.Vorspiel.Fin Require Import Matrix.
From Foundation.Vorspiel.Finset Require Import Card.
From Foundation.Vorspiel.Finset Require Import Basic.
From Foundation.Vorspiel.List Require Import Basic.
From Foundation.Vorspiel.List Require Import Chain.
From Foundation.Vorspiel.List Require Import ChainI.
From Foundation.Vorspiel.List Require Import Perm.
From Foundation.Vorspiel.Nat Require Import Basic.
From Foundation.Vorspiel.Nat Require Import Matrix.
From Foundation.Vorspiel.Set Require Import Basic.
From Foundation.Vorspiel.Set Require Import Cofinite.
From Foundation.Vorspiel.Set Require Import Fin.
From Foundation.Vorspiel.Order Require Import Heyting.
From Foundation.Vorspiel.Order Require Import Zorn.
From Foundation.Vorspiel.Order Require Import Lattice.
From Foundation.Vorspiel.Order Require Import Dense.
From Foundation.Vorspiel.Order Require Import Ideal.
From Foundation.Vorspiel.Order Require Import LowerSet.
From Foundation.Vorspiel.Order Require Import Regular.
From Foundation.Modal Require Import
  MaximalConsistentSet MaximalCanonical Tableau ComplementClosedConsistentList.

Check partial_order_laws.
Check order_chain.
Check order_maximal.
Check zorn_maximal_element.
Print Assumptions zorn_maximal_element.
Check abstract_formula_theory.
Check abstract_theory_included.
Check abstract_theory_insert.
Check abstract_context_derives.
Check abstract_context_consistent.
Check abstract_context_derives_weaken.
Check abstract_context_derives_imply_intro.
Check abstract_context_derives_under_mp.
Print Assumptions abstract_context_deduction.
Check abstract_context_undeduction.
Check abstract_context_dne.
Print Assumptions abstract_insert_consistent_iff.
Print Assumptions abstract_insert_neg_consistent_iff.
Print Assumptions abstract_either_insert_consistent.
Check abstract_consistent_extension.
Check abstract_extension_carrier.
Check abstract_extension_included.
Print Assumptions abstract_extension_included_order.
Check abstract_base_extension.
Check abstract_chain_with_base.
Print Assumptions abstract_chain_with_base_ordered.
Check abstract_chain_union.
Print Assumptions abstract_chain_union_derivation_stage.
Print Assumptions abstract_chain_union_consistent.
Check abstract_chain_union_extension.
Print Assumptions abstract_extension_chain_upper_bound.
Print Assumptions abstract_maximal_extension_complete.
Print Assumptions abstract_maximal_extension_derivable_mem.
Check abstract_maximal_extension_classical.
Check abstract_maximal_extension_as_generic.
Print Assumptions abstract_lindenbaum_extension.
Check abstract_normal_mct.
Check anmct_generic.
Check anmct_mem.
Print Assumptions anmct_context_consistent.
Print Assumptions anmct_derivable_iff.
Print Assumptions anmct_theorem_mem.
Print Assumptions abstract_normal_lindenbaum_extension.
Check abstract_canonical_relation_iter.
Check abstract_canonical_relation.
Print Assumptions abstract_context_derives_box_iter_from_preboxed.
Print Assumptions abstract_canonical_successor_of_neg_box_iter.
Print Assumptions abstract_canonical_successor_of_neg_box.
Print Assumptions anmct_box_iter_relation_iff.
Print Assumptions anmct_box_relation_iff.
Print Assumptions anmct_box_iter_negneg_iff.
Print Assumptions anmct_box_negneg_iff.
Print Assumptions anmct_box_iter_dual.
Print Assumptions anmct_box_dual.
Print Assumptions anmct_dia_iter_dual.
Print Assumptions anmct_dia_dual.
Print Assumptions anmct_dia_iter_relation_iff.
Print Assumptions anmct_dia_relation_iff.
Print Assumptions abstract_canonical_relation_iter_iff_dia_iter.
Print Assumptions abstract_canonical_relation_iter_iff_neg_box_iter.
Print Assumptions abstract_canonical_relation_iter_iff_neg_dia_iter.
Print Assumptions abstract_canonical_relation_iff_dia.
Print Assumptions abstract_canonical_relation_iff_neg_box.
Print Assumptions abstract_canonical_relation_iff_neg_dia.
Print Assumptions anmct_box_iter_list_conj_iff.
Print Assumptions anmct_box_list_conj_iff.
Check abstract_tableau.
Check at_positive.
Check at_negative.
Check abstract_tableau_subset.
Check abstract_tableau_seed.
Check abstract_tableau_consistent.
Check abstract_tableau_inconsistent.
Check abstract_tableau_insert_positive.
Check abstract_tableau_insert_negative.
Check abstract_empty_tableau.
Check abstract_singleton_negative_tableau.
Check abstract_maximal_tableau.
Check amt_positive.
Check amt_negative.
Check amt_as_tableau.
Print Assumptions abstract_context_derives_empty_iff_classical.
Print Assumptions abstract_singleton_negative_seed.
Print Assumptions abstract_tableau_insert_positive_seed.
Print Assumptions abstract_tableau_insert_negative_seed.
Print Assumptions abstract_tableau_insert_positive_consistent_iff.
Print Assumptions abstract_tableau_insert_negative_consistent_iff.
Print Assumptions abstract_tableau_either_expand_consistent.
Print Assumptions abstract_singleton_negative_consistent_iff.
Print Assumptions abstract_empty_tableau_consistent_iff.
Print Assumptions abstract_tableau_lindenbaum.
Print Assumptions amt_neither.
Print Assumptions amt_saturated.
Print Assumptions amt_not_positive_iff_negative.
Print Assumptions amt_not_negative_iff_positive.
Print Assumptions anmct_extensional.
Print Assumptions amt_positive_extensional.
Print Assumptions amt_negative_extensional.
Print Assumptions amt_inclusion_extensional.
Print Assumptions amt_context_derivable_iff.
Print Assumptions amt_theorem_iff.
Print Assumptions amt_positive_bottom_absent.
Print Assumptions amt_negative_bottom.
Print Assumptions amt_positive_top.
Print Assumptions amt_negative_top_absent.
Print Assumptions amt_positive_neg_iff.
Print Assumptions amt_negative_neg_iff.
Print Assumptions amt_positive_imp_iff.
Print Assumptions amt_positive_imp_function_iff.
Print Assumptions amt_negative_imp_iff.
Print Assumptions amt_positive_and_iff.
Print Assumptions amt_negative_and_iff.
Print Assumptions amt_positive_or_iff.
Print Assumptions amt_negative_or_iff.
Print Assumptions amt_positive_mdp.
Print Assumptions amt_negative_contravariant_mdp.
Print Assumptions amt_positive_list_conj_iff.
Print Assumptions amt_negative_list_conj_iff.
Print Assumptions amt_positive_list_disj_iff.
Print Assumptions amt_negative_list_disj_iff.
Check amt_relation_iter.
Check amt_relation.
Print Assumptions amt_positive_box_iter_iff.
Print Assumptions amt_negative_box_iter_iff.
Print Assumptions amt_positive_dia_iter_iff.
Print Assumptions amt_negative_dia_iter_iff.
Print Assumptions amt_positive_box_iff.
Print Assumptions amt_negative_box_iff.
Print Assumptions amt_positive_dia_iff.
Print Assumptions amt_negative_dia_iff.
Print Assumptions amt_positive_difference_of_neq.
Print Assumptions amt_negative_difference_of_neq.
Check abstract_list_subset.
Check abstract_finite_theory.
Check abstract_finite_consistent.
Check abstract_finite_inconsistent.
Print Assumptions abstract_context_derives_extensional.
Print Assumptions abstract_context_consistent_extensional.
Print Assumptions abstract_finite_theory_cons_insert.
Print Assumptions abstract_finite_derives_empty_iff.
Print Assumptions abstract_finite_empty_consistent.
Print Assumptions abstract_finite_consistent_insert_iff.
Print Assumptions abstract_finite_consistent_insert_neg_iff.
Print Assumptions abstract_finite_provable_iff_insert_neg_inconsistent.
Print Assumptions abstract_finite_neg_provable_iff_insert_inconsistent.
Print Assumptions abstract_finite_singleton_neg_consistent_iff.
Print Assumptions abstract_finite_singleton_consistent_iff_neg_unprovable.
Print Assumptions abstract_finite_singleton_complement_consistent_iff.
Print Assumptions abstract_finite_singleton_complement_inconsistent_iff.
Print Assumptions abstract_finite_union_consistent_intro.
Print Assumptions abstract_derives_complement_bottom.
Print Assumptions abstract_derives_neg_complement_bottom.
Print Assumptions abstract_derives_of_neg_complement.
Print Assumptions abstract_derives_neg_of_complement.
Check abstract_finite_next.
Check abstract_finite_enumerate.
Print Assumptions abstract_finite_next_consistent.
Print Assumptions abstract_finite_enumerate_consistent.
Print Assumptions abstract_finite_next_includes.
Print Assumptions abstract_finite_enumerate_includes.
Print Assumptions abstract_finite_enumerate_either.
Print Assumptions abstract_finite_enumerate_origin.
Print Assumptions abstract_exists_consistent_complementary_closed.
Check abstract_predicate_complementary_closed.
Check abstract_finite_maximal_context.
Check afmc_carrier.
Check afmc_finite.
Check afmc_consistent.
Check afmc_closed.
Check afmc_mem.
Print Assumptions afmc_mem_complement_of_not_mem.
Print Assumptions afmc_mem_of_not_mem_complement.
Print Assumptions afmc_equality_def.
Print Assumptions abstract_finite_context_lindenbaum.
Print Assumptions abstract_finite_maximal_context_inhabited.
Print Assumptions afmc_membership_iff_derivable.
Print Assumptions afmc_mem_top.
Print Assumptions afmc_bottom_absent.
Print Assumptions afmc_mem_iff_not_mem_complement.
Print Assumptions afmc_not_mem_iff_mem_complement.
Print Assumptions afmc_mem_imp_iff.
Print Assumptions afmc_not_mem_imp_iff.
Check abstract_finite_powerset.
Print Assumptions abstract_finite_powerset_contains_filter.
Check afmc_mem_dec.
Check afmc_selector.
Check afmc_representative.
Print Assumptions afmc_representative_spec.
Check abstract_option_list.
Check afmc_candidate.
Check afmc_explicit_cover.
Print Assumptions afmc_candidate_complete.
Print Assumptions afmc_explicit_cover_complete.
From Foundation.Syntax.Predicate Require Import Language Term Quantifier.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Intuitionistic Require Import Formula Rew Deduction.
From Foundation.FirstOrder.NegationTranslation Require Import GoedelGentzen.
From Foundation.FirstOrder.Kripke Require Import Basic Intuitionistic WeakForcing.
From Foundation.FirstOrder Require Import Hauptsatz.
From Foundation.FirstOrder Require Import Ultraproduct.
From Foundation.Vorspiel.Set Require Import Ultrafilter.
From Foundation.FirstOrder.Completeness Require Import CountableSublanguage.
From Foundation.FirstOrder.Completeness Require Import CanonicalModel.
From Foundation.FirstOrder.Completeness Require Import CounterModel.
From Foundation.FirstOrder.Order Require Import Le.
From Foundation.SecondOrder.Syntax Require Import Formula Rew.
From Foundation.SecondOrder Require Import Semantics.
From Foundation.SecondOrder Require Import Derivation.
From Foundation.Syntax.Predicate Require Import Rew.
From Foundation.FirstOrder.Basic Require Import Operator.
From Foundation.FirstOrder.Basic Require Import Model.
From Foundation.FirstOrder.Basic Require Import Definability.
From Foundation.FirstOrder.Basic Require Import Calculus.
From Foundation.FirstOrder.Basic Require Import Calculus2.
From Foundation.FirstOrder.Basic Require Import Padding.
From Foundation.FirstOrder.Basic Require Import Eq.
From Foundation.FirstOrder.Basic Require Import Coding.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Syntax.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Model.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Hierarchy.
From Foundation.FirstOrder.Arithmetic.R0 Require Import
  Basic CodeGraph CodeGraphSemantics Representation
  RepresentationCompleteness Semidecidability CertifiedSigmaOne.
From Foundation.FirstOrder.Arithmetic.Q Require Import Basic.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Theory.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Q.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Functions.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Definability.
From Foundation.FirstOrder.Arithmetic Require Import Schemata.
From Foundation.FirstOrder.Arithmetic.IOpen Require Import Basic Definability.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Hierarchy.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Definable.
From Foundation.FirstOrder.Arithmetic.Definability Require Import BoundedDefinable.
From Foundation.FirstOrder.Arithmetic.Definability Require Import Absoluteness.
From Foundation.FirstOrder.Arithmetic.TA Require Import Basic.
From Foundation.FirstOrder.Arithmetic.TA Require Import Nonstandard.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Monotone.
From Foundation.FirstOrder.Basic Require Import Soundness.
From Foundation.FirstOrder.Basic Require Import CutFree.
From Foundation.FirstOrder.Basic.Semantics Require Import Semantics.
From Foundation.FirstOrder.Basic.Semantics Require Import RewriteClosure.
From Foundation.FirstOrder.Basic.Semantics Require Import OperatorSemantics.
From Foundation.FirstOrder.Basic.Semantics Require Import ModelTheory.
From Foundation.FirstOrder.Basic.Semantics Require Import Elementary.
From Foundation.FirstOrder Require Import Polarity.
From Foundation.Syntax.Predicate Require Import Relational.
From Foundation.LinearLogic Require Import LogicSymbol MLL MELL.
From Foundation.LinearLogic.FirstOrder Require Import
  Formula Rew Calculus ClassicalEmbedding.

Check ifo_semiformula.
Check ifo_formula.
Check ifo_sentence.
Check ifo_semisentence.
Check ifo_semiproposition.
Check ifo_proposition.
Check ifo_neg.
Check ifo_verum.
Check ifo_connectives.
Print Assumptions ifo_and_injective.
Print Assumptions ifo_or_injective.
Print Assumptions ifo_imp_injective.
Print Assumptions ifo_all_injective.
Print Assumptions ifo_exs_injective.
Check ifo_universal_quantifier.
Check ifo_existential_quantifier.
Check ifo_quantifiers.
Check ifo_lcwq.
Print Assumptions ifo_all_closure_injective.
Print Assumptions ifo_exs_closure_injective.
Print Assumptions ifo_all_iter_injective.
Print Assumptions ifo_exs_iter_injective.
Check ifo_complexity.
Print Assumptions ifo_complexity_verum.
Print Assumptions ifo_complexity_neg.
Check ifo_semiformula_eq_dec.
Check ifo_negative.
Print Assumptions ifo_negative_and_iff.
Print Assumptions ifo_negative_imp_iff.
Print Assumptions ifo_negative_all_iff.
Print Assumptions ifo_negative_verum.
Print Assumptions ifo_negative_neg.
Print Assumptions ifo_negative_not_or.
Print Assumptions ifo_negative_not_exs.
Print Assumptions ifo_negative_not_rel.
Check ifo_negative_dec.
Check ifo_rewrite.
Print Assumptions ifo_rewrite_falsum.
Print Assumptions ifo_rewrite_rel.
Print Assumptions ifo_rewrite_and.
Print Assumptions ifo_rewrite_or.
Print Assumptions ifo_rewrite_imp.
Print Assumptions ifo_rewrite_all.
Print Assumptions ifo_rewrite_exs.
Print Assumptions ifo_rewrite_neg.
Print Assumptions ifo_rewrite_verum.
Print Assumptions ifo_rewrite_ext.
Print Assumptions ifo_rewrite_id.
Print Assumptions ifo_rewrite_comp.
Check ifo_map.
Check ifo_bshift.
Check ifo_emb.
Check ifo_shift.
Check ifo_free.
Check ifo_substitute.
Print Assumptions ifo_free_bshift.
Print Assumptions ifo_free_imp_bshift.
Print Assumptions ifo_shift_all.
Print Assumptions ifo_shift_double_neg_all.
Print Assumptions ifo_substitute_shift_one_eq_free.
Print Assumptions ifo_rewrite_under_free_free.
Print Assumptions ifo_rewrite_substitute_one.
Print Assumptions ifo_rewrite_q_bshift.
Print Assumptions ifo_rewrite_all1_shape.
Print Assumptions ifo_rewrite_all2_shape.
Print Assumptions ifo_rewrite_ex1_shape.
Print Assumptions ifo_rewrite_ex2_shape.
Print Assumptions ifo_map_injective.
Print Assumptions ifo_complexity_rewrite.
Print Assumptions ifo_negative_rewrite_iff.
Check ifo_hilbert.
Check ifo_hilbert_le.
Check ifo_hilbert_minimal.
Check ifo_hilbert_intuitionistic.
Check ifo_hilbert_classical.
Print Assumptions ifo_hilbert_minimal_le.
Print Assumptions ifo_hilbert_intuitionistic_le_classical.
Check ifo_hilbert_proof.
Check ifo_hilbert_entailment.
Check ifo_hilbert_proof_cast.
Check ifo_hilbert_proof_depth.
Print Assumptions ifo_hilbert_proof_depth_cast.
Check ifo_hilbert_modus_ponens.
Check ifo_hilbert_identity.
Print Assumptions ifo_hilbert_neg_equiv.
Check ifo_hilbert_minimal_capability.
Check ifo_context_derivation.
Check ifo_context_assumption.
Check ifo_context_theorem.
Check ifo_context_cast.
Check ifo_context_mdp.
Check ifo_context_weaken.
Check ifo_context_deduct.
Check ifo_context_deduct_inverse.
Print Assumptions ifo_hilbert_specialize.
Print Assumptions ifo_hilbert_imply_all.
Print Assumptions ifo_context_generalize.
Print Assumptions ifo_context_specialize.
Print Assumptions ifo_hilbert_all_imply_all_of_all_imply.
Print Assumptions ifo_hilbert_all_iff_all_of_free_iff.
Print Assumptions ifo_hilbert_dne_negative_rewrite.
Print Assumptions ifo_hilbert_dne_negative.
Check ifo_context_of_double_neg_negative.
Print Assumptions ifo_hilbert_double_neg_iff_negative.
Print Assumptions ifo_hilbert_efq_negative_rewrite.
Print Assumptions ifo_hilbert_efq_negative.
Print Assumptions ifo_hilbert_iff_neg_of_neg_iff.
Print Assumptions ifo_hilbert_proof_rewrite.
Print Assumptions ifo_hilbert_proof_depth_rewrite.
Check ifo_hilbert_proof_weaken.
Check ifo_sentence_embed.
Print Assumptions ifo_sentence_embed_imp.
Check ifo_theory.
Check ifo_theory_le.
Check ifo_theory_empty.
Check ifo_theory_adjoin_axiom.
Check ifo_theory_adjoin.
Check ifo_theory_formula_context.
Check ifo_theory_proof.
Check ifo_theory_entailment.
Check ifo_theory_proof_cast.
Print Assumptions ifo_theory_proof_weaken.
Check ifo_theory_assumption.
Check ifo_theory_of_hilbert.
Print Assumptions ifo_theory_adjoin_context_forward.
Print Assumptions ifo_theory_adjoin_context_backward.
Print Assumptions ifo_theory_deduct.
Print Assumptions ifo_theory_deduct_inverse.
Check ifo_theory_modus_ponens.
Check ifo_theory_minimal_capability.
Check ifo_hilbert_intuitionistic_capability.
Check ifo_hilbert_intuitionistic_system_capability.
Check ifo_theory_intuitionistic_capability.
Check ifo_theory_classical_capability.
Check ifo_hilbert_classical_lem_capability.
Check ifo_hilbert_classical_efq_capability.
Print Assumptions ifo_hilbert_classical_system_capability.
Check ifo_double_negation_translation.
Print Assumptions ifo_double_negation_rel.
Print Assumptions ifo_double_negation_nrel.
Print Assumptions ifo_double_negation_verum.
Print Assumptions ifo_double_negation_falsum.
Print Assumptions ifo_double_negation_and.
Print Assumptions ifo_double_negation_or.
Print Assumptions ifo_double_negation_all.
Print Assumptions ifo_double_negation_exists.
Print Assumptions ifo_double_negation_imp.
Print Assumptions ifo_double_negation_negative.
Check semiformula_list_conj2.
Check ifo_list_conj2.
Print Assumptions ifo_double_negation_list_conj2.
Print Assumptions ifo_rewrite_double_negation.
Print Assumptions ifo_substitute_double_negation.
Print Assumptions ifo_emb_double_negation.
Check ifo_double_negation_sequent.
Print Assumptions ifo_double_negation_sequent_nil.
Print Assumptions ifo_double_negation_sequent_cons.
Print Assumptions ifo_double_negation_sequent_append.
Print Assumptions ifo_shift_double_negation_sequent.
Check ifo_double_negation_theory.
Print Assumptions ifo_double_negation_theory_axiom_eq.
Check ifo_double_negation_theory_intro.
Check ifo_double_negation_theory_source.
Print Assumptions ifo_hilbert_neg_double_negation_rewrite.
Print Assumptions ifo_hilbert_neg_double_negation.
Print Assumptions ifo_hilbert_neg_neg_double_negation.
Print Assumptions ifo_hilbert_imp_iff_neg_and_negative.
Print Assumptions ifo_hilbert_imp_double_negation.
Check ifo_goedel_gentzen_formula.
Check ifo_goedel_gentzen_context.
Print Assumptions ifo_goedel_gentzen_context_nil.
Print Assumptions ifo_goedel_gentzen_context_cons.
Print Assumptions ifo_goedel_gentzen_context_append.
Print Assumptions ifo_free_double_negation.
Print Assumptions ifo_shift_goedel_gentzen_formula.
Print Assumptions ifo_shift_goedel_gentzen_context.
Check ifo_context_cast_context.
Check ifo_raw_member_of_member_dec.
Check ifo_member_of_raw_member.
Check ifo_raw_map_member_preimage.
Check ifo_raw_member_cast.
Check ifo_goedel_gentzen_context_subset.
Print Assumptions ifo_goedel_gentzen.
Print Assumptions ifo_goedel_gentzen_provable.
Check ifo_kripke_model.
Check ifo_kripke_domain.
Print Assumptions ifo_kripke_domain_nonempty.
Print Assumptions ifo_kripke_domain_antimonotone.
Check ifo_kripke_rel.
Print Assumptions ifo_kripke_rel_monotone.
Check ifo_kripke_constant_domain.
Check ifo_kripke_forcing_exists.
Print Assumptions ifo_kripke_domain_nonempty_forces.
Print Assumptions ifo_kripke_domain_persistent.
Print Assumptions ifo_kripke_constant_domain_forces.
Check ifo_kripke_filter_carrier.
Check ifo_kripke_filter_val.
Check ifo_kripke_filter_witness.
Print Assumptions ifo_kripke_filter_witness_member.
Print Assumptions ifo_kripke_filter_witness_domain.
Print Assumptions ifo_kripke_filter_finite_colimit.
Print Assumptions ifo_kripke_filter_domain_list_colimit.
Print Assumptions ifo_kripke_filter_finite_family_domain.
Check ifo_kripke_filter_structure.
Print Assumptions ifo_kripke_filter_structure_rel_iff.
Check ifo_kripke_forces.
Print Assumptions ifo_kripke_forces_falsum.
Print Assumptions ifo_kripke_forces_rel.
Print Assumptions ifo_kripke_forces_and.
Print Assumptions ifo_kripke_forces_or.
Print Assumptions ifo_kripke_forces_imp.
Print Assumptions ifo_kripke_forces_neg.
Print Assumptions ifo_kripke_forces_verum.
Print Assumptions ifo_kripke_forces_all.
Print Assumptions ifo_kripke_forces_exs.
Print Assumptions ifo_kripke_forces_iff.
Check ifo_kripke_list_conj.
Check ifo_kripke_list_disj.
Print Assumptions ifo_kripke_forces_list_conj.
Print Assumptions ifo_kripke_forces_list_disj.
Print Assumptions ifo_kripke_forces_rewrite.
Check ifo_nat_env_cons.
Check ifo_fin_env_snoc.
Print Assumptions ifo_kripke_forces_free.
Print Assumptions ifo_kripke_forces_substitute.
Print Assumptions ifo_kripke_forces_emb.
Print Assumptions ifo_kripke_forces_bshift.
Print Assumptions ifo_kripke_forces_monotone.
Print Assumptions ifo_kripke_triple_negation_elim.
Print Assumptions ifo_kripke_forces_all_constant_domain.
Print Assumptions ifo_kripke_forces_exs_constant_domain.
Print Assumptions ifo_kripke_intuitionistic_sound.
Check ifo_kripke_sentence_forces.
Check ifo_kripke_sentence_forcing_relation.
Print Assumptions ifo_kripke_sentence_forces_monotone.
Print Assumptions ifo_kripke_sentence_int_kripke.
Print Assumptions ifo_kripke_type_context_sound.
Check ifo_kripke_world_forces_theory.
Check ifo_kripke_globally_forces_theory.
Print Assumptions ifo_kripke_intuitionistic_theory_sound_at.
Print Assumptions ifo_kripke_intuitionistic_theory_sound.
Check ifo_kripke_weakly_forces.
Print Assumptions ifo_preorder_exists_below.
Print Assumptions ifo_kripke_weakly_forces_rel.
Print Assumptions ifo_kripke_weakly_forces_nrel.
Print Assumptions ifo_kripke_weakly_forces_verum.
Print Assumptions ifo_kripke_weakly_forces_falsum.
Print Assumptions ifo_kripke_weakly_forces_and.
Print Assumptions ifo_kripke_weakly_forces_or.
Print Assumptions ifo_kripke_weakly_forces_all.
Print Assumptions ifo_kripke_weakly_forces_exs.
Print Assumptions ifo_kripke_weakly_forces_rewrite.
Print Assumptions ifo_kripke_weakly_forces_emb.
Print Assumptions ifo_kripke_weakly_forces_monotone.
Print Assumptions ifo_kripke_weakly_forces_all_constant_domain.
Print Assumptions ifo_kripke_weakly_forces_exs_constant_domain.
Print Assumptions ifo_kripke_weakly_forces_generic.
Print Assumptions ifo_kripke_weakly_forces_generic_iff.
Print Assumptions ifo_kripke_weakly_forces_generic_iff_not.
Print Assumptions ifo_kripke_weakly_forces_neg.
Print Assumptions ifo_kripke_weakly_forces_generic_iff_not_forces_neg.
Print Assumptions ifo_kripke_weakly_forces_imp.
Print Assumptions ifo_kripke_weakly_forces_iff.
Check ifo_kripke_sentence_weakly_forces.
Check ifo_kripke_sentence_weak_forcing_relation.
Print Assumptions ifo_kripke_sentence_weakly_forces_iff_forces.
Print Assumptions ifo_kripke_sentence_weakly_forces_monotone.
Print Assumptions ifo_kripke_sentence_weakly_forces_generic.
Print Assumptions ifo_kripke_sentence_classical_kripke.
Print Assumptions ifo_kripke_weakly_forces_lk_sound.
Print Assumptions ifo_kripke_sentence_weakly_forces_lk_sound.
Check first_order_positive_derivation_from.
Check first_order_positive_derivation_of_subset.
Check first_order_positive_derivation_trans.
Check first_order_positive_derivation_cons.
Check first_order_positive_derivation_append.
Check first_order_positive_derivation_add.
Check first_order_positive_derivation_graft.
Check first_order_consistent_sequent.
Check first_order_consistent_sequent_order.

Check choose_unique.
Print Assumptions choose_unique_spec.
Print Assumptions choose_unique_uniq.
Print Assumptions choose_unique_eq_iff_right.
Print Assumptions choose_unique_eq_iff_left.
Print Assumptions exists_unique_extend.
Check extended_choose_unique.
Print Assumptions extended_choose_unique_spec.
Print Assumptions extended_choose_unique_spec_not.
Print Assumptions extended_choose_unique_uniq.
Print Assumptions extended_choose_unique_eq_iff.
Print Assumptions empty_function_unique.
Check type_is_empty.
Check empty_type_elim.
Print Assumptions empty_type_function_unique.
Check lo_tilde.
Check lo_arrow.
Check lo_wedge.
Check lo_vee.
Check lo_box.
Check lo_dia.
Check lo_rhd.
Check lo_tensor.
Check lo_par.
Check lo_with.
Check lo_plus.
Check lo_lolli.
Check lo_bang.
Check lo_quest.
Check lo_exp.
Check lo_smash.
Check lo_length.
Check lo_godel_quote.
Check lo_sigma_symbol.
Check lo_pi_symbol.
Check lo_delta_symbol.
Check explicit_quotient.
Check quotient_vec_mk.
Print Assumptions quotient_vec_induction.
Check quotient_vec_lift.
Print Assumptions quotient_vec_lift_zero.
Print Assumptions quotient_vec_lift_mk.
Print Assumptions quotient_vec_lift_mk_one.
Print Assumptions quotient_vec_lift_mk_two.
Print Assumptions option_return_eq_some.
Check option_to_list.
Print Assumptions option_to_list_singleton_iff.
Check function_equal_on.
Print Assumptions function_equal_on_subset.
Check predicate_small.
Check predicate_preimage.
Print Assumptions small_preimage_of_injective.
Check fin_string_join.
Check fin_vec_to_string.
Print Assumptions fin_string_join_zero.
Print Assumptions fin_string_join_one.
Print Assumptions fin_string_join_many.
Print Assumptions fin_vec_to_string_zero.
Print Assumptions fin_vec_to_string_one.
Print Assumptions fin_vec_to_string_many.
Check finite_cover_data.
Check finite_cover_sup.
Print Assumptions finite_cover_elem_le_sup.
Print Assumptions finite_cover_sup_le_iff.
Print Assumptions finite_cover_sup_empty.
Check list_dependent_eq_dec.
Print Assumptions finite_cover_dependent_eq_dec.
Print Assumptions cantor_of_nat_components_le.
Check denumerable_nat_list_fuel.
Check denumerable_nat_list.
Print Assumptions denumerable_nat_list_fuel_member_lt.
Print Assumptions denumerable_nat_list_member_lt.
Check function_graph_vector.
Check function_graph.
Check function_graph2.
Check function_graph3.
Check function_graph4.
Check function_graph5.
Print Assumptions function_graph_eq.
Print Assumptions function_graph_iff_left.
Print Assumptions function_graph_iff_right.
Print Assumptions function_graph2_eq.
Print Assumptions function_graph2_iff_left.
Print Assumptions function_graph2_iff_right.
Print Assumptions function_graph3_eq.
Print Assumptions function_graph3_iff_left.
Print Assumptions function_graph3_iff_right.
Check partial_value.
Check partial_dom.
Check partial_some.
Check partial_none.
Check partial_bind.
Check partial_map.
Print Assumptions partial_bind_some.
Print Assumptions partial_map_member_iff.
Check partial_find_zero.
Print Assumptions partial_find_zero_member_iff.
Check fin_partial_product.
Print Assumptions fin_partial_product_member_iff.
Print Assumptions partial_unit_dom_iff.
Check enumerable_decoder.
Check nat_enumerable_decoder.
Check partial_computable.
Check partial_projection.
Print Assumptions partial_projection_member_iff.
Print Assumptions partial_computable_projection.
Check semidecidable.
Print Assumptions semidecidable_true.
Print Assumptions semidecidable_false.
Print Assumptions semidecidable_const.
Print Assumptions semidecidable_iff_partial_computable_unit.
Print Assumptions semidecidable_and.
Print Assumptions semidecidable_or.
Print Assumptions semidecidable_projection.
Print Assumptions semidecidable_comp.
Check decidable_predicate.
Print Assumptions decidable_predicate_semidecidable.
Print Assumptions decidable_predicate_const.
Print Assumptions decidable_predicate_and.
Print Assumptions decidable_predicate_or.
Check enat.
Check enat_top.
Check enat_le.
Check enat_lt.
Check enat_find.
Print Assumptions enat_find_exists_spec.
Print Assumptions enat_lt_find.
Print Assumptions enat_exists_of_find_le.
Print Assumptions enat_find_eq_top_iff.
Print Assumptions enat_find_le.
Print Assumptions enat_lt_succ_of_le.
Print Assumptions enat_find_eq_zero.
Check dvec_empty.
Check dvec_cons.
Print Assumptions dvec_cons_zero.
Print Assumptions dvec_cons_succ.
Print Assumptions dvec_eta.
Print Assumptions dvec_cons_ext_iff.
Check fin_cover_data.
Print Assumptions dvec_eq_dec.
Check matrix_vec_empty.
Check matrix_vec_cons.
Check matrix_vec_head.
Check matrix_vec_tail.
Print Assumptions matrix_vec_cons_zero.
Print Assumptions matrix_vec_cons_succ.
Print Assumptions matrix_vec_eta.
Print Assumptions matrix_vec_cons_ext_iff.
Check matrix_vec_eq_dec.
Check matrix_vec_map.
Print Assumptions matrix_vec_map_cons.
Print Assumptions matrix_vec_map_comp.
Check matrix_vec_to_list.
Print Assumptions matrix_vec_to_list_length.
Print Assumptions matrix_vec_to_list_member_iff.
Check matrix_vec_foldr.
Check matrix_vec_foldl.
Print Assumptions matrix_vec_foldr_succ.
Print Assumptions matrix_vec_foldl_succ.
Print Assumptions matrix_vec_forall_iff.
Print Assumptions matrix_vec_exists_iff.
Check matrix_vec_option_sequence.
Print Assumptions matrix_vec_option_sequence_some.
Print Assumptions matrix_vec_cons_injective.
Check matrix_vec_append.
Print Assumptions matrix_vec_append_zero.
Print Assumptions matrix_vec_append_cons.
Print Assumptions matrix_vec_append_left.
Print Assumptions matrix_vec_append_right.
Check matrix_vec_singleton.
Check matrix_vec_snoc.
Print Assumptions matrix_vec_snoc_left.
Print Assumptions matrix_vec_snoc_last.
Print Assumptions matrix_vec_snoc_cons.
Print Assumptions matrix_vec_map_append.
Check matrix_vec_to_nat.
Print Assumptions matrix_vec_to_nat_empty.
Print Assumptions matrix_vec_to_nat_cons.
Check fin_vec_pointwise.
Print Assumptions fin_vec_forall_bounded_iff.
Print Assumptions fin_vec_exists_bounded_iff.
Print Assumptions fin_vec_forall_iff.
Print Assumptions fin_vec_exists_iff.
Check nat_to_matrix_vec.
Print Assumptions nat_to_matrix_vec_encode.
Print Assumptions nat_to_matrix_vec_member_lt.
Check nat_truth_eq.
Check nat_truth_lt.
Check nat_truth_le.
Check nat_truth_dvd.
Print Assumptions nat_truth_eq_positive_iff.
Print Assumptions nat_truth_lt_positive_iff.
Print Assumptions nat_truth_le_positive_iff.
Print Assumptions nat_truth_dvd_positive_iff.
Check nat_truth_inv.
Check nat_truth_pos.
Check nat_truth_and.
Check nat_truth_or.
Print Assumptions nat_truth_inv_eq_zero_iff.
Print Assumptions nat_truth_and_positive_iff.
Print Assumptions nat_truth_or_positive_iff.
Check nat_bounded_all.
Print Assumptions nat_bounded_all_positive_iff.
Print Assumptions nat_bounded_all_eq_zero_iff.
Print Assumptions nat_bounded_all_eq_one_iff_positive.
Check arith_partial_function.
Check arith_partial_comp.
Check arith_find_on.
Check arith_part1.
Check arithmetic1.
Print Assumptions arith_find_on_member_iff.
Print Assumptions arith_partial_comp_some_member_iff.
Print Assumptions arithmetic1_zero.
Print Assumptions arithmetic1_one.
Print Assumptions arithmetic1_add.
Print Assumptions arithmetic1_mul.
Print Assumptions arithmetic1_proj.
Print Assumptions arithmetic1_equal.
Print Assumptions arithmetic1_lt.
Print Assumptions arithmetic1_comp.
Check arithmetic1_unary.
Check arithmetic1_binary.
Print Assumptions arithmetic1_comp1.
Print Assumptions arithmetic1_comp2.
Print Assumptions arithmetic1_succ.
Print Assumptions arithmetic1_const.
Print Assumptions arithmetic1_inv.
Print Assumptions arithmetic1_pos.
Print Assumptions arithmetic1_and.
Print Assumptions arithmetic1_or.
Print Assumptions nat_truth_le_as_or.
Print Assumptions arithmetic1_le.
Print Assumptions nat_truth_if_positive.
Print Assumptions arithmetic1_if_positive.
Check arith_find_positive_on.
Print Assumptions arith_part1_find_positive.
Print Assumptions arith_find_positive_on_member_iff.
Check nat_sub_test.
Print Assumptions nat_sub_test_positive_iff.
Print Assumptions nat_sub_least_test.
Print Assumptions arithmetic1_sub_test.
Print Assumptions arithmetic1_sub.
Check nat_pair.
Print Assumptions nat_le_pair_left.
Print Assumptions nat_le_pair_right.
Print Assumptions nat_pair_monotone.
Print Assumptions nat_pair_strict_monotone_left.
Print Assumptions nat_pair_strict_monotone_right.
Print Assumptions nat_truth_lt_branch.
Print Assumptions arithmetic1_pair.
Check nat_sqrt_test.
Print Assumptions nat_sqrt_test_positive_iff.
Print Assumptions nat_sqrt_least_test.
Print Assumptions arithmetic1_sqrt_test.
Print Assumptions arithmetic1_sqrt.
Print Assumptions arithmetic1_if_lt.
Check nat_square_remainder.
Print Assumptions arithmetic1_square_remainder.
Check nat_unpair.
Print Assumptions nat_unpair_pair.
Print Assumptions nat_unpair1_pair.
Print Assumptions nat_unpair2_pair.
Print Assumptions nat_pair_unpair.
Print Assumptions arithmetic1_unpair1.
Print Assumptions arithmetic1_unpair2.
Check arith_partial_cons.
Print Assumptions arith_part1_partial_cons.
Print Assumptions arith_part1_map_total.
Print Assumptions nat_least_decidable_bound.
Check nat_dvd_witness_test.
Print Assumptions nat_dvd_witness_test_positive_iff.
Print Assumptions nat_truth_le_boolean.
Print Assumptions nat_truth_dvd_boolean.
Print Assumptions nat_dvd_witness_least_iff.
Print Assumptions nat_dvd_witness_least_value.
Print Assumptions nat_dvd_witness_least_exists.
Print Assumptions arithmetic1_dvd_witness_test.
Print Assumptions arithmetic1_dvd.
Check nat_rem_test.
Print Assumptions nat_rem_test_positive_iff.
Print Assumptions nat_divides_sub_mod.
Print Assumptions nat_rem_is_least.
Print Assumptions nat_rem_least_test.
Print Assumptions arithmetic1_rem_test.
Print Assumptions arithmetic1_rem.
Check nat_beta.
Print Assumptions nat_beta_pair.
Print Assumptions arithmetic1_beta.
Print Assumptions arithmetic1_tail.
Check nat_bounded_all_search.
Print Assumptions nat_bounded_all_search_positive_iff.
Print Assumptions nat_bounded_all_search_least_exists.
Print Assumptions nat_bounded_all_search_least_value.
Print Assumptions arithmetic1_bounded_all.
Check nat_primitive_recursion.
Check beta_sequence_encoder.
Print Assumptions beta_encoded_recursion_eq.
Print Assumptions beta_eq_primitive_recursion.
Print Assumptions beta_recursion_code_exists.
Check arithmetic_primitive_recursion.
Print Assumptions beta_eq_arithmetic_primitive_recursion.
Print Assumptions beta_arithmetic_recursion_code_exists.
Check nat_recursion_code_test.
Print Assumptions nat_recursion_code_test_positive_iff.
Print Assumptions nat_recursion_code_least_exists.
Print Assumptions nat_recursion_code_value.
Check arithmetic_recursion_code_test.
Print Assumptions arithmetic1_recursion_code_test.
Print Assumptions arithmetic1_primitive_recursion.
Check primitive_recursive1.
Print Assumptions arithmetic1_of_primitive_recursive1.
Check partial_recursive1.
Print Assumptions arith_part1_of_partial_recursive1.
Print Assumptions partial_recursive1_of_arith_part1.
Print Assumptions arith_part1_iff_partial_recursive1.
Check arith_code.
Check arith_code_evaluates.
Print Assumptions fin_indexed_choice.
Print Assumptions arith_part1_has_code.
Print Assumptions beta_bezout_identity.
Print Assumptions mathcomp_modn_eq_nat_modulo.
Print Assumptions beta_factorial_divides.
Print Assumptions beta_prefix_bound_gt.
Print Assumptions beta_stride_divides_difference.
Print Assumptions beta_moduli_coprime.
Print Assumptions beta_modulus_divides_product.
Print Assumptions beta_modulus_product_coprime_later.
Print Assumptions beta_crt_prefix_correct.
Print Assumptions concrete_beta_encode_correct.
Check concrete_beta_sequence_encoder.
Print Assumptions arithmetic1_primitive_recursion_concrete.
Print Assumptions arithmetic1_of_primitive_recursive1_concrete.
Print Assumptions arith_part1_iff_partial_recursive1_concrete.
Check mll_formula.
Check mll_neg.
Print Assumptions mll_neg_involutive.
Check mll_lolli.
Check mll_derivation.
Check mll_id.
Check mll_cut.
Check mll_exchange.
Check mll_tensor_rule.
Check mll_par_rule.
Print Assumptions mll_rotate.
Print Assumptions mll_identity.
Print Assumptions mll_identity_proof.
Print Assumptions mll_modus_ponens.
Print Assumptions mll_excluded_middle.
Check mell_formula.
Check mell_neg.
Print Assumptions mell_neg_involutive.
Check mell_lolli.
Check mell_formula_is_quest.
Print Assumptions mell_formula_is_quest_not_atom.
Print Assumptions mell_formula_is_quest_not_natom.
Print Assumptions mell_formula_is_quest_not_tensor.
Print Assumptions mell_formula_is_quest_not_par.
Print Assumptions mell_formula_is_quest_not_bang.
Print Assumptions mell_formula_is_quest_quest.
Check mell_sequent_is_quest.
Print Assumptions mell_sequent_is_quest_nil.
Print Assumptions mell_sequent_is_quest_cons.
Check mell_derivation.
Check mell_id.
Check mell_cut.
Check mell_exchange.
Check mell_tensor_rule.
Check mell_par_rule.
Check mell_bang_rule.
Check mell_dereliction.
Print Assumptions mell_rotate.
Print Assumptions mell_eta.
Print Assumptions mell_identity_proof.
Print Assumptions mell_modus_ponens.
Check multiplicative_connective.
Check multiplicative_neutral.
Check additive_connective.
Check additive_neutral.
Check exponential_connective.
Check multiplicative_de_morgan.
Check multiplicative_neutral_de_morgan.
Check additive_de_morgan.
Check additive_neutral_de_morgan.
Check exponential_de_morgan.
Check linear_lolli.
Print Assumptions linear_lolli_def.
Print Assumptions linear_tensor_eq_iff.
Print Assumptions linear_par_eq_iff.
Print Assumptions involutive_injective.
Print Assumptions linear_lolli_eq_iff.
Print Assumptions linear_with_eq_iff.
Print Assumptions linear_plus_eq_iff.
Print Assumptions linear_bang_eq_iff.
Print Assumptions linear_quest_eq_iff.
Check linear_list_quest.
Print Assumptions linear_list_quest_def.
Print Assumptions linear_list_quest_nil.
Print Assumptions linear_list_quest_cons.
Print Assumptions linear_list_quest_append.
Check llfo_semiformula.
Check LLRel.
Check LLNRel.
Check LLOne.
Check LLFalsum.
Check LLTensor.
Check LLPar.
Check LLVerum.
Check LLZero.
Check LLWith.
Check LLPlus.
Check LLBang.
Check LLQuest.
Check LLAll.
Check LLExs.
Check llfo_multiplicative_connective.
Check llfo_multiplicative_neutral.
Check llfo_additive_connective.
Check llfo_additive_neutral.
Check llfo_exponential_connective.
Print Assumptions llfo_all_injective.
Print Assumptions llfo_exs_injective.
Check llfo_neg.
Print Assumptions llfo_neg_rel.
Print Assumptions llfo_neg_nrel.
Print Assumptions llfo_neg_all.
Print Assumptions llfo_neg_exs.
Print Assumptions llfo_neg_involutive.
Print Assumptions llfo_neg_eq_iff.
Check llfo_lolli.
Check llfo_wedge.
Check llfo_vee.
Check llfo_imply.
Check llfo_complexity.
Print Assumptions llfo_complexity_neg.
Check llfo_rel_payload.
Check llfo_outer_rel_payload.
Check llfo_outer_nrel_payload.
Print Assumptions llfo_rel_injective_same_arity.
Print Assumptions llfo_nrel_injective_same_arity.
Check llfo_semiformula_eq_dec.
Check llfo_proposition_eq_dec.
Check llfo_is_quest.
Print Assumptions llfo_is_quest_quest.
Print Assumptions llfo_is_quest_not_bang.
Print Assumptions llfo_is_quest_not_tensor.
Print Assumptions llfo_is_quest_not_par.
Print Assumptions llfo_is_quest_not_all.
Print Assumptions llfo_is_quest_not_exs.
Print Assumptions llfo_is_quest_not_rel.
Print Assumptions llfo_is_quest_not_nrel.
Print Assumptions llfo_is_quest_not_one.
Print Assumptions llfo_is_quest_not_falsum.
Print Assumptions llfo_is_quest_not_verum.
Print Assumptions llfo_is_quest_not_zero.
Print Assumptions llfo_is_quest_not_with.
Print Assumptions llfo_is_quest_not_plus.
Check llfo_negative.
Check LLNegativeQuest.
Check LLNegativeVerum.
Check LLNegativeFalsum.
Check LLNegativePar.
Check LLNegativeWith.
Check LLNegativeAll.
Check llfo_positive.
Check LLPositiveBang.
Check LLPositiveZero.
Check LLPositiveOne.
Check LLPositiveTensor.
Check LLPositivePlus.
Check LLPositiveExs.
Print Assumptions llfo_negative_par_iff.
Print Assumptions llfo_negative_with_iff.
Print Assumptions llfo_negative_all_iff.
Print Assumptions llfo_positive_tensor_iff.
Print Assumptions llfo_positive_plus_iff.
Print Assumptions llfo_positive_exs_iff.
Check llfo_negative_dec.
Check llfo_positive_dec.
Print Assumptions llfo_neg_positive_iff_negative.
Print Assumptions llfo_neg_negative_iff_positive.
Print Assumptions llfo_positive_negative_disjoint.
Check llfo_rewrite.
Print Assumptions llfo_rewrite_rel.
Print Assumptions llfo_rewrite_nrel.
Print Assumptions llfo_rewrite_one.
Print Assumptions llfo_rewrite_falsum.
Print Assumptions llfo_rewrite_tensor.
Print Assumptions llfo_rewrite_par.
Print Assumptions llfo_rewrite_verum.
Print Assumptions llfo_rewrite_zero.
Print Assumptions llfo_rewrite_with.
Print Assumptions llfo_rewrite_plus.
Print Assumptions llfo_rewrite_bang.
Print Assumptions llfo_rewrite_quest.
Print Assumptions llfo_rewrite_all.
Print Assumptions llfo_rewrite_exs.
Print Assumptions llfo_rewrite_neg.
Print Assumptions llfo_rewrite_ext.
Print Assumptions llfo_rewrite_id.
Print Assumptions llfo_rewrite_comp.
Print Assumptions llfo_complexity_rewrite.
Print Assumptions llfo_negative_rewrite_iff.
Print Assumptions llfo_positive_rewrite_iff.
Print Assumptions llfo_is_quest_rewrite_iff.
Print Assumptions llfo_rewrite_lolli.
Check llfo_map.
Check llfo_lift_bound_map.
Print Assumptions llfo_lift_bound_map_injective.
Print Assumptions llfo_rew_q_map_equiv.
Print Assumptions llfo_map_injective.
Check llfo_emb.
Check llfo_shift.
Check llfo_free.
Check llfo_substitute.
Print Assumptions llfo_substitute_shift_one_eq_free.
Print Assumptions llfo_substitute_neg_shift_one_eq_neg_free.
Print Assumptions llfo_free_neg.
Print Assumptions llfo_shift_neg.
Print Assumptions llfo_shift_exs.
Check llfo_sequent.
Check llfo_sequent_is_quest.
Check llfo_sequent_negative.
Print Assumptions llfo_sequent_is_quest_nil.
Print Assumptions llfo_sequent_is_quest_cons.
Print Assumptions llfo_sequent_negative_nil.
Print Assumptions llfo_sequent_negative_cons.
Print Assumptions llfo_quest_sequent_is_quest.
Check llfo_derivation.
Check LLDIdentity.
Check LLDCut.
Check LLDExchange.
Check LLDOne.
Check LLDFalsum.
Check LLDTensor.
Check LLDPar.
Check LLDVerum.
Check LLDWith.
Check LLDPlusLeft.
Check LLDPlusRight.
Check LLDOfCourse.
Check LLDWeakening.
Check LLDDereliction.
Check LLDContraction.
Check LLDAll.
Check LLDExs.
Check llfo_derivation_height.
Print Assumptions llfo_height_identity.
Print Assumptions llfo_height_cut.
Print Assumptions llfo_height_exchange.
Print Assumptions llfo_height_one.
Print Assumptions llfo_height_falsum.
Print Assumptions llfo_height_tensor.
Print Assumptions llfo_height_par.
Print Assumptions llfo_height_verum.
Print Assumptions llfo_height_with.
Print Assumptions llfo_height_plus_left.
Print Assumptions llfo_height_plus_right.
Print Assumptions llfo_height_of_course.
Print Assumptions llfo_height_weakening.
Print Assumptions llfo_height_dereliction.
Print Assumptions llfo_height_contraction.
Print Assumptions llfo_height_all.
Print Assumptions llfo_height_exs.
Print Assumptions llfo_height_cast.
Check llfo_eta.
Check llfo_identity_proof.
Print Assumptions llfo_modus_ponens.
Print Assumptions llfo_excluded_middle.
Print Assumptions llfo_exp_comm.
Print Assumptions llfo_add_quest_append_right.
Print Assumptions llfo_add_quest_tail.
Print Assumptions llfo_sequent_is_quest_singleton.
Print Assumptions llfo_of_negative_par_step.
Print Assumptions llfo_of_negative_with_step.
Print Assumptions llfo_of_negative_all_step.
Print Assumptions llfo_of_negative_rewrite.
Print Assumptions llfo_of_negative.
Print Assumptions llfo_remove_quest.
Print Assumptions llfo_negative_weakening.
Print Assumptions llfo_negative_contraction.
Print Assumptions llfo_remove_quest_append_right.
Print Assumptions llfo_remove_quest_tail.
Print Assumptions llfo_negative_of_course.
Print Assumptions llfo_negative_comp_subset.
Print Assumptions llfo_negative_wk.
Check llfo_forget.
Print Assumptions llfo_forget_rel.
Print Assumptions llfo_forget_nrel.
Print Assumptions llfo_forget_one.
Print Assumptions llfo_forget_verum.
Print Assumptions llfo_forget_falsum.
Print Assumptions llfo_forget_zero.
Print Assumptions llfo_forget_tensor.
Print Assumptions llfo_forget_with.
Print Assumptions llfo_forget_par.
Print Assumptions llfo_forget_plus.
Print Assumptions llfo_forget_bang.
Print Assumptions llfo_forget_quest.
Print Assumptions llfo_forget_all.
Print Assumptions llfo_forget_exs.
Print Assumptions llfo_forget_neg.
Print Assumptions llfo_forget_rewrite.
Check llfo_girard.
Print Assumptions llfo_girard_rel.
Print Assumptions llfo_girard_nrel.
Print Assumptions llfo_girard_verum.
Print Assumptions llfo_girard_falsum.
Print Assumptions llfo_girard_neg.
Print Assumptions llfo_girard_rewrite.
Check llfo_Girard.
Print Assumptions llfo_Girard_rewrite.
Print Assumptions llfo_Girard_eq_quest.
Print Assumptions llfo_Girard_eq_raw.
Print Assumptions llfo_Girard_all_of_positive.
Print Assumptions llfo_Girard_all_of_negative.
Print Assumptions llfo_Girard_exs_of_positive.
Print Assumptions llfo_Girard_exs_of_negative.
Print Assumptions llfo_girard_negative.
Print Assumptions llfo_girard_positive.
Print Assumptions llfo_girard_negative_iff.
Print Assumptions llfo_girard_positive_iff.
Print Assumptions llfo_Girard_negative.
Check llfo_girard_sequent.
Print Assumptions llfo_girard_sequent_negative.
Print Assumptions llfo_girard_sequent_shift.
Print Assumptions llfo_girard_sequent_app.
Print Assumptions llfo_girard_sequent_incl.
Print Assumptions list_in_of_generic_list_member.
Print Assumptions llfo_girard_identity.
Print Assumptions llfo_girard_cut_step.
Print Assumptions llfo_girard_contraction_step.
Print Assumptions llfo_girard_verum_step.
Print Assumptions llfo_move_middle_to_front.
Print Assumptions llfo_swap_app.
Print Assumptions llfo_girard_duplicated_context_incl.
Print Assumptions llfo_girard_collapse_duplicated_context.
Print Assumptions llfo_girard_and_step.
Print Assumptions llfo_girard_or_step.
Print Assumptions llfo_girard_all_step.
Print Assumptions llfo_girard_exs_step.
Print Assumptions llfo_derivation_girard.
Print Assumptions llfo_proof_girard.
Print Assumptions llfo_forget_girard.
Print Assumptions llfo_forget_Girard.
Check llfo_forget_sequent.
Print Assumptions llfo_forget_sequent_shift.
Print Assumptions llfo_forget_permutation_subset.
Check llfo_derivation_forget.
Print Assumptions llfo_proof_forget.
Print Assumptions llfo_proof_forget_Girard.
Print Assumptions llfo_girard_faithful.
Print Assumptions llfo_proof_girard_decidable.
Print Assumptions llfo_girard_faithful_decidable.
Print Assumptions list_permutation_two_iff.
Check list_comp_subset.
Print Assumptions list_permutation_normalize.
Print Assumptions list_comp_subset_contract.
Print Assumptions list_comp_subset_trans.
Print Assumptions list_comp_subset_cons.
Print Assumptions list_incl_to_comp_subset.
Check list_chainI.
Print Assumptions list_chainI_not_nil.
Print Assumptions list_chainI_singleton_iff.
Print Assumptions list_chainI_head_eq.
Print Assumptions list_chainI_cons_cons_iff.
Print Assumptions list_chainI_tail_exists.
Print Assumptions list_chainI_suffix_exists.
Print Assumptions list_chainI_prefix_suffix.
Print Assumptions list_chainI_last_eq.
Print Assumptions list_chainI_endpoints_unique.
Print Assumptions list_chainI_not_mem_predecessor.
Print Assumptions list_chainI_nodup.
Print Assumptions chainI_lists_explicit_finite_cover.
Print Assumptions list_chainI_predecessor_exists.
Print Assumptions list_chainI_append_point_iff.
Print Assumptions list_chainI_relation_of_adjacent_infix.
Print Assumptions list_chainI_infix_of_prefixed_suffix.
Check list_strict_inclusion.
Print Assumptions list_strict_inclusion_of_incl_lt_length.
Print Assumptions list_length_eq_of_eq.
Check list_nat_sum.
Print Assumptions list_nat_sum_le_length_mul.
Print Assumptions list_doubleton_incl_iff.
Print Assumptions list_strict_inclusion_length_lt.
Print Assumptions no_list_strict_descending_chain.
Check finite_range.
Print Assumptions finite_range_member_iff.
Check list_image.
Print Assumptions list_image_member_iff.
Print Assumptions list_image_member.
Print Assumptions set_remove_union_equiv.
Check explicit_equiv.
Check finite_cover_transport.
Print Assumptions finite_cover_transport_member.
Print Assumptions finite_cover_sup_reindex_equiv.
Print Assumptions list_flat_map_empty_iff.
Print Assumptions fin_zero_eta.
Print Assumptions nat_sub_one_lt_nonzero.
Print Assumptions vorspiel_fin_enum_complete.
Print Assumptions vorspiel_fin_enum_nodup.
Print Assumptions no_fin_embedding_to_smaller.
Print Assumptions nat_lt_next_fin_last.
Print Assumptions vorspiel_fin_le_last_nonzero.
Print Assumptions vorspiel_fin_positive_of_value_nonzero.
Print Assumptions vorspiel_fin_of_nat_positive.
Print Assumptions fin_forall_succ_iff.
Print Assumptions fin_exists_succ_iff.
Print Assumptions fin_add_cast_value.
Print Assumptions fin_one_eq_zero.
Print Assumptions fin_one_not_positive.
Print Assumptions list_subset_bool_true_iff.
Print Assumptions list_member_lt_upper.
Print Assumptions list_nth_map_seq.
Print Assumptions list_member_le_join.
Print Assumptions list_of_fin_length.
Print Assumptions list_of_fin_member_iff.
Print Assumptions list_of_fin_map.
Print Assumptions list_fin_member_le_join.
Print Assumptions list_remove_all_member_iff.
Print Assumptions list_remove_all_mono.
Print Assumptions list_remove_all_map_incl.
Print Assumptions list_induction_with_singleton.
Check list_rec_with_singleton.
Print Assumptions list_boundary_of_not_suffix.
Print Assumptions list_suffix_eq_or_cons.
Print Assumptions list_suffix_trichotomy.
Print Assumptions list_exists_of_map_seq.
Print Assumptions list_nodup_iff_indexed_distinct.
Print Assumptions list_words_up_to_complete.
Print Assumptions nodup_lists_explicit_finite_cover.
Print Assumptions list_singleton_suffix_unique.
Check list_chain.
Print Assumptions list_member_index.
Print Assumptions list_member_indices_distinct.
Print Assumptions list_chain_map.
Print Assumptions list_chain_range_strict_mono.
Print Assumptions list_chain_range_strict_anti.
Print Assumptions list_chain_seq.
Print Assumptions fin_value_FS.
Print Assumptions fin_enum_nth_error_value.
Print Assumptions list_chain_fin_enum.
Print Assumptions list_chain_fin_enum_strict_mono.
Print Assumptions list_chain_fin_enum_strict_anti.
Print Assumptions list_chain_connected.
Print Assumptions list_chain_nodup.
Print Assumptions chain_lists_explicit_finite_cover.
Print Assumptions list_chain_rev.
Print Assumptions list_chain_fin_enum_rev.
Print Assumptions list_chain_app_singleton_iff.
Print Assumptions list_chain_head_relation.
Print Assumptions list_chain_head_lower.
Print Assumptions list_chain_last_relation.
Print Assumptions list_chain_last_upper.
Print Assumptions list_chain_app_singleton_last_iff.
Check chain_list_index.
Print Assumptions chain_list_index_member.
Print Assumptions chain_list_index_injective_of_nodup.
Check type_embedding.
Print Assumptions list_embedding_of_nodup_length.
Check nat_cases.
Print Assumptions nat_cases_zero.
Print Assumptions nat_cases_succ.
Print Assumptions nat_ne_succ_max_left.
Print Assumptions nat_ne_succ_max_right.
Print Assumptions nat_fold_ext_below.
Print Assumptions nat_least_number.
Check nat_to_fin.
Print Assumptions nat_positive_of_nonzero.
Print Assumptions nat_one_le_of_odd.
Print Assumptions nat_square_pair_monotone.
Check pred_set.
Check set_subset.
Print Assumptions set_doubleton_subset_iff.
Print Assumptions set_subset_insert_iff_remove.
Print Assumptions set_strict_subset_of_subset_not_equiv.
Print Assumptions finite_list_subset_chain_union.
Print Assumptions finite_family_subset_chain_union.
Check pointed_set_enumeration.
Check set_finite_approximation.
Print Assumptions set_finite_approximation_member_iff.
Print Assumptions set_finite_approximation_nodup.
Print Assumptions set_finite_approximation_strict.
Print Assumptions set_finite_approximation_subset.
Print Assumptions set_finite_approximation_complete.
Print Assumptions infinitely_finite_approximate.
Check set_finitely_covered.
Check set_cofinite.
Check set_coinfinite.
Print Assumptions set_finitely_covered_subset.
Print Assumptions set_coinfinite_iff_not_cofinite.
Print Assumptions set_cofinite_iff_not_coinfinite.
Print Assumptions set_cofinite_subset.
Print Assumptions set_coinfinite_subset.
Print Assumptions set_full_cofinite.
Print Assumptions set_cofinite_union_left.
Print Assumptions set_cofinite_union_right.
Print Assumptions fin1_full_equiv_singleton.
Print Assumptions fin1_set_cases.
Print Assumptions fin1_powerset_iff.
Print Assumptions fin2_full_equiv_pair.
Print Assumptions fin2_singleton_not_full.
Print Assumptions fin2_set_cases.
Print Assumptions fin2_powerset_iff.
Print Assumptions fin2_complement_one_equiv_zero.
Print Assumptions fin2_complement_zero_equiv_one.
Print Assumptions fin3_full_equiv_triple.
Check heyting_algebra_data.
Print Assumptions ha_inf_mono.
Print Assumptions ha_himp_himp_inf_himp_inf_le.
Print Assumptions ha_himp_inf_himp_inf_sup_le.
Print Assumptions ha_complement_of_sup_equiv_inf_complements.
Check finite_fold.
Print Assumptions finite_fold_filter_all.
Print Assumptions finite_sup_filter_all.
Print Assumptions finite_inf_filter_all.
Check join_order_data.
Check order_ideal.
Print Assumptions principal_ideal_member_iff.
Print Assumptions bottom_ideal_member_eq_iff.
Print Assumptions principal_ideal_least.
Print Assumptions ideal_join_list_member_bound.
Print Assumptions ideal_join_list_least_upper.
Print Assumptions ideal_join_list_member.
Print Assumptions principal_ideal_join_list_least.
Print Assumptions ideal_join_list_app_left.
Print Assumptions ideal_join_list_app_right.
Check generated_ideal.
Print Assumptions generated_principal_list_member_iff.
Check ideal_family_sup.
Print Assumptions ideal_family_sup_member_iff.
Print Assumptions ideal_family_sup_contains.
Print Assumptions ideal_family_sup_least.
Print Assumptions ideal_supremum_member_downward.
Print Assumptions ideal_proper_iff_top_not_member.
Check ideal_prime_pair.
Print Assumptions prime_pair_not_filter_iff_ideal.
Print Assumptions prime_pair_not_ideal_iff_filter.
Check boolean_order_data.
Check boolean_prime_ideal.
Print Assumptions boolean_prime_pair_ideal_or_compl.
Print Assumptions boolean_prime_pair_filter_or_compl.
Print Assumptions boolean_prime_pair_compl_ideal_iff_filter.
Print Assumptions boolean_prime_pair_compl_filter_iff_ideal.
Print Assumptions boolean_prime_pair_meet_ideal_iff.
Print Assumptions boolean_prime_pair_join_filter_iff.
Print Assumptions boolean_prime_pair_himp_filter_iff.
Check preorder_data.
Check directed_on.
Print Assumptions directed_list_colimit.
Print Assumptions directed_finite_family_colimit.
Check order_compatible.
Print Assumptions order_compatible_sym_iff.
Print Assumptions order_incompatible_iff.
Print Assumptions order_incompatible_lower.
Check order_dense.
Check order_dense_below.
Check dense_set.
Check dense_choose.
Print Assumptions dense_choose_le.
Print Assumptions dense_choose_member.
Check order_pfilter.
Check principal_pfilter.
Check descending_chain.
Check pfilter_of_descending_chain.
Print Assumptions pfilter_of_descending_chain_member_iff.
Check pfilter_generic.
Check dense_family_countable.
Print Assumptions nat_relation_of_successors.
Print Assumptions generic_descending_chain_is_descending.
Print Assumptions exists_generic_pfilter_of_countable.
Check lower_set.
Check lower_empty.
Check lower_full.
Check lower_union.
Check lower_family_union.
Check lower_family_intersection.
Print Assumptions lower_disjoint_iff_incompatible.
Print Assumptions lower_dual_member_iff.
Print Assumptions lower_dual_greatest_disjoint.
Print Assumptions lower_himp_member_iff.
Print Assumptions lower_himp_greatest.
Print Assumptions lower_set_heyting_algebra.
Check lower_regular.
Print Assumptions lower_dual_antitone.
Print Assumptions lower_double_dual_extensive.
Print Assumptions lower_double_dual_monotone.
Print Assumptions lower_triple_dual_equiv.
Print Assumptions lower_regularize_regular.
Print Assumptions lower_dual_regular.
Print Assumptions lower_intersection_regular.
Print Assumptions lower_family_intersection_regular.
Check regular_lower_set.
Check regular_bottom.
Check regular_top.
Check regular_meet.
Check regular_join.
Check regular_compl.
Check regular_family_sup.
Check regular_family_inf.
Print Assumptions regular_meet_greatest.
Print Assumptions regular_join_least.
Print Assumptions Foundation.Vorspiel.Order.LowerSet.regular_family_sup_least.
Print Assumptions Foundation.Vorspiel.Order.LowerSet.regular_family_inf_greatest.
Print Assumptions regular_meet_compl_bottom.
Print Assumptions regular_join_compl_top.
Print Assumptions regular_compl_involutive.
Check Foundation.Vorspiel.Order.Regular.closure_order_data.
Check Foundation.Vorspiel.Order.Regular.regular_element.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_value_equiv_closure.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_family_sup_value.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_family_sup_contains.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_family_sup_universal.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_family_inf_value.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_family_inf_below.
Print Assumptions Foundation.Vorspiel.Order.Regular.regular_family_inf_universal.

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
Check fin_forall_exists_choice.
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
Print Assumptions rew_map_injective.
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
Check rew_comp_emb_substs.
Check rew_emb_substs_variables.
Check rew_emb_substs_variables_empty.
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
Check rew_lift_bound_map.
Print Assumptions rew_lift_bound_map_injective.
Print Assumptions rew_q_map_equiv.
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
Check rew_bshift_positive_iff_exists.
Check rew_bshift_not_bvar_zero.
Check rew_q_bvar_zero_iff.
Check rew_q_positive.
Check rew_q_positive_iff.
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
Check semiterm_rew_apply_ext_on_free.
Check semiformula_rewrite_ext_on_free.
Check rew_language_map.
Check semiterm_language_map_rew_apply.
Check rew_language_map_q.
Check semiformula_language_map_rewrite.
Check rew_language_map_subst.
Check rew_language_map_shift.
Check rew_language_map_free.
Check semiformula_language_map_substitute.
Check semiformula_language_map_shift.
Check semiformula_language_map_free.
Check semiformula_rewrite_id.
Check semiformula_rewrite_comp.
Check semiformula_rewrite_all_iter.
Check semiformula_rewrite_exists_iter.
Check semiformula_rewrite_bounded_all.
Check semiformula_rewrite_complexity.
Check semiformula_rewrite_quantifier_rank.
Check semiformula_rewrite_open.
Check semiformula_rewrite_free_occurs_sources.
Check rew_rewrite_under_free.
Check rew_rewrite_under_free_comp_shift.
Check rew_rewrite_under_free_comp_free.
Check semiformula_rewrite_under_free_shift.
Check semiformula_rewrite_under_free_free.
Check rew_subst_bshift_zero.
Check rew_rewrite_comp_substitute_one.
Check semiformula_rewrite_substitute_one.
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

Check semiterm_operator.
Check semiterm_operator_fn.
Check semiterm_operator_apply.
Check semiterm_operator_const_apply.
Check semiterm_operator_fn_apply.
Check rew_semiterm_operator_apply.
Check semiterm_operator_comp.
Check semiterm_operator_comp_apply.
Check semiterm_operator_bvar.
Check semiterm_operator_bvar_apply.
Check semiterm_operator_comp_bvar_left.
Check semiterm_operator_comp_bvar_right.
Check semiterm_operator_comp_assoc.
Check semiterm_operator_apply_bound_occurs.
Check semiterm_operator_apply_positive.
Check semiterm_const_operator_positive.
Check semiterm_operator_foldr.
Check semiterm_operator_foldr_cons_apply.
Check fin_to_list.
Check semiterm_operator_iterr.
Check semiterm_operator_iterr_zero.
Check semiterm_operator_iterr_succ.
Check semiterm_has_zero_operator.
Check semiterm_has_one_operator.
Check semiterm_has_add_operator.
Check semiterm_has_mul_operator.
Check semiterm_has_exp_operator.
Check semiterm_has_sub_operator.
Check semiterm_has_div_operator.
Check semiterm_has_star_operator.
Check semiterm_godel_number_operator.
Check semiterm_zero_operator_of_language.
Check semiterm_one_operator_of_language.
Check semiterm_add_operator_of_language.
Check semiterm_mul_operator_of_language.
Check semiterm_exp_operator_of_language.
Check semiterm_star_operator_of_language.
Check semiterm_add_operator_positive.
Check semiterm_mul_operator_positive.
Check semiterm_exp_operator_positive.
Check semiterm_operator_numeral.
Check semiterm_operator_numeral_zero.
Check semiterm_operator_numeral_one.
Check semiterm_operator_numeral_succ_nonzero.
Check semiterm_operator_numeral_succ_succ.
Check semiterm_godel_number_of_encoding.
Check semiterm_operator_npow.
Check semiterm_operator_npow_zero.
Check semiterm_operator_npow_succ.
Check semiterm_operator_npow_positive.
Check fin_max_two.
Check semiterm_zero_operator_complexity.
Check semiterm_one_operator_complexity.
Check semiterm_add_operator_complexity.
Check semiterm_mul_operator_complexity.
Check semiformula_operator.
Check semiformula_operator_apply.
Check rew_semiformula_operator_apply.
Check semiformula_rewrite_and_preimage.
Check semiformula_rewrite_or_preimage.
Check semiformula_rewrite_all_preimage.
Check semiformula_rewrite_exists_preimage.
Check semiformula_operator_comp.
Check semiformula_operator_comp_apply.
Check semiformula_operator_comp_bvar_right.
Check semiformula_operator_comp_assoc.
Check semiformula_operator_and.
Check semiformula_operator_or.
Check semiformula_operator_and_apply.
Check semiformula_operator_or_apply.
Check semiformula_has_eq_operator.
Check semiformula_has_lt_operator.
Check semiformula_has_le_operator.
Check semiformula_has_mem_operator.
Check semiformula_eq_operator_of_language.
Check semiformula_lt_operator_of_language.
Check semiformula_mem_operator_of_language.
Check semiformula_le_operator_of_eq_lt.
Check semiformula_le_operator_of_language.
Check semiformula_eq_operator_apply.
Check semiformula_lt_operator_apply.
Check semiformula_mem_operator_apply.
Check semiformula_le_operator_apply.
Check semiformula_rel_arity_injective.
Check semiformula_rewrite_binary_relation_preimage.
Check semiformula_rewrite_eq_operator_preimage.
Check semiformula_rewrite_lt_operator_preimage.
Check semiformula_rewrite_mem_operator_preimage.
Check semiformula_binary_relation_injective.
Check semiformula_eq_operator_injective.
Check semiformula_lt_operator_injective.
Check semiformula_mem_operator_injective.
Check semiformula_le_operator_injective.
Check semiformula_eq_operator_open.
Check semiformula_lt_operator_open.
Check semiformula_mem_operator_open.
Check semiformula_le_operator_open.
Check semiformula_ball_lt.
Check semiformula_bex_lt.
Check semiformula_ball_le.
Check semiformula_bex_le.
Check semiformula_ball_mem.
Check semiformula_bex_mem.

Check first_order_structure.
Check unit_first_order_structure.
Check first_order_structure_language_map.
Check carrier_equiv.
Check first_order_structure_transport.
Check fin_env_cons.
Check carrier_equiv_from_fin_env_cons.
Check semiterm_val.
Check closed_semiterm_val.
Check semiterm_val_rewrite.
Check semiterm_val_rewrite_free.
Check semiterm_val_rewrite_map.
Check semiterm_val_substitute.
Check semiterm_val_map.
Check semiterm_val_bshift.
Check semiterm_val_emb_substs.
Check semiterm_val_language_map.
Check semiterm_val_transport.
Check semiterm_val_free_ext.
Check semiterm_val_rew_emb_bvars.
Check semiterm_val_rew_emb_fvars.
Check semiterm_val_to_closed.
Check nat_env_cons.
Check fin_env_snoc.
Check fin_env_append.
Check fin_env_append_left.
Check fin_env_append_right.
Check fin_env_append_left_eta.
Check fin_env_append_right_eta.
Check semiterm_val_shift.
Check semiterm_val_rew_free_bvars.
Check semiterm_val_rew_free_fvars.
Check semiterm_val_rew_fix_bvars.
Check semiterm_val_rew_fix_fvars.
Check semiterm_val_free.
Check semiterm_val_fix.
Check semiformula_eval.
Check formula_eval.
Check sentence_realize.
Check semiformula_eval_neg.
Check semiformula_eval_imp.
Check semiformula_eval_iff.
Check semiformula_eval_bounded_all.
Check semiformula_eval_bounded_exists.
Check semiterm_val_rew_q_bvars.
Check semiterm_val_rew_q_fvars.
Check semiformula_eval_rewrite.
Check semiformula_eval_map.
Check semiformula_eval_substitute.
Check semiformula_eval_bshift.
Check semiformula_eval_emb_substs.
Check semiformula_eval_free_ext.
Check semiformula_eval_bound_ext.
Check semiformula_eval_to_closed.
Check semiformula_eval_enumerate_index_of_free_variable.
Check semiformula_eval_language_map.
Check semiformula_eval_transport.
Check semiformula_eval_free.
Check semiformula_eval_shift.
Check semiformula_eval_all_iter.
Check semiformula_eval_exists_iter.
Check semiformula_eval_all_closure.
Check semiformula_eval_exists_closure.
Check rew_fix_iter_free_env.
Check semiformula_eval_fix_all_free.
Check formula_eval_universal_closure_open.
Check sentence_realize_universal_closure.
Check semiterm_operator_val.
Check semiterm_val_operator_apply.
Check semiterm_operator_val_comp.
Check semiterm_operator_val_bvar.
Check semiterm_operator_val_fn.
Check semiterm_operator_val_transport.
Check semiformula_operator_eval.
Check semiformula_eval_operator_apply.
Check semiformula_operator_eval_comp.
Check semiformula_operator_eval_and.
Check semiformula_operator_eval_or.
Check semiformula_operator_eval_transport.
Check semiformula_eq_operator_eval_of_language.
Check semiformula_lt_operator_eval_of_language.
Check semiformula_mem_operator_eval_of_language.
Check structure_interprets_zero.
Check structure_interprets_one.
Check structure_interprets_add.
Check structure_interprets_mul.
Check structure_interprets_exp.
Check structure_interprets_eq.
Check structure_interprets_relation.
Check structure_interprets_lt.
Check structure_interprets_le.
Check structure_interprets_mem.
Check structure_interprets_le_of_eq_lt.
Check structure_interprets_le_of_eq_lt_spec.
Check semiterm_val_binary_bound.
Check semiformula_eval_bounded_operator_all.
Check semiformula_eval_bounded_operator_exists.
Check semiformula_eval_ball_lt.
Check semiformula_eval_bex_lt.
Check semiformula_eval_ball_le.
Check semiformula_eval_bex_le.
Check semiformula_eval_ball_mem.
Check semiformula_eval_bex_mem.
Check semiformula_eval_ball_relation.
Check semiformula_eval_bex_relation.
Check first_order_model.
Check first_order_model_of_structure.
Check first_order_model_realize.
Check first_order_semantics.
Check sentence_connectives.
Check first_order_tarski.
Check first_order_models_theory.
Check first_order_valid.
Check first_order_satisfiable.
Check first_order_consequence.
Check first_order_models_theory_iff.
Check first_order_models_of_member.
Check first_order_models_of_subset.
Check first_order_models_union_iff.
Check first_order_valid_iff.
Check first_order_satisfiable_iff.
Check first_order_unsatisfiable_iff.
Check first_order_satisfiable_intro.
Check first_order_consequence_iff.
Check first_order_consequence_iff_unsatisfiable.
Check first_order_consequence_weakening.
Check first_order_consequence_of_member.
Check first_order_model_theory.
Check first_order_model_theory_spec.
Check first_order_model_models_own_theory.
Check first_order_model_theory_satisfiable.
Check first_order_theory_subset_model_theory_iff.
Check first_order_model_language_pullback.
Check first_order_model_realize_language_map.
Check first_order_consequence_language_map.
Check first_order_hom.
Check first_order_embedding.
Check first_order_iso.
Check first_order_embedding_to_hom.
Check first_order_hom_semiterm_val.
Check first_order_embedding_semiterm_val.
Check first_order_embedding_eval_open.
Check first_order_embedding_eval_all_closure_open.
Check first_order_closed_subset.
Check first_order_closed_subset_structure.
Check first_order_closed_subset_inclusion.
Check semiformula_eval_carrier_equiv.
Check first_order_elementary_equiv.
Check first_order_elementary_equiv_refl.
Check first_order_elementary_equiv_sym.
Check first_order_elementary_equiv_trans.
Check first_order_elementary_equiv_models_theory.
Check first_order_elementary_equiv_of_carrier_equiv.
Check structure_model.
Check structure_model_equiv.
Check structure_model_structure.
Check structure_model_elementary_equiv.
Check structure_model_nullary.
Check structure_model_unary.
Check structure_model_binary.
Check structure_model_relation.
Check structure_model_interprets_zero.
Check structure_model_interprets_one.
Check structure_model_interprets_add.
Check structure_model_interprets_mul.
Check structure_model_interprets_exp.
Check structure_model_interprets_eq.
Check structure_model_interprets_lt.
Check structure_model_interprets_mem.
Check function_only_structure.
Check first_order_structure_add.
Check first_order_structure_add_language_map_left.
Check first_order_structure_add_language_map_right.
Check semiterm_val_language_add_left.
Check semiformula_eval_language_add_left.
Check first_order_structure_sigma.
Check semiterm_val_language_sigma.
Check semiformula_eval_language_sigma.
Check structure_lift.
Check structure_lift_structure.
Check semiterm_val_structure_lift.
Check semiformula_eval_structure_lift.
Check structure_lift_elementary_equiv.
Check first_order_is_defined_by.
Check first_order_defined.
Check first_order_is_defined_by_with_params.
Check first_order_definable.
Check first_order_defined_function.
Check first_order_defined_predicate.
Check first_order_defined_relation.
Check first_order_defined_relation3.
Check first_order_defined_relation4.
Check first_order_defined_constant.
Check first_order_defined_unary_function.
Check first_order_defined_binary_function.
Check first_order_defined_ternary_function.
Check first_order_defined_quaternary_function.
Check first_order_defined_quinary_function.
Check first_order_definable_function.
Check first_order_definable_predicate.
Check first_order_definable_relation.
Check first_order_definable_relation3.
Check first_order_definable_relation4.
Check first_order_definable_relation5.
Check first_order_definable_relation6.
Check semiformula_embed_empty.
Check semiformula_eval_embed_empty.
Check first_order_defined_to_definable.
Check first_order_definable_of_iff.
Check first_order_definable_const.
Check first_order_definable_and.
Check first_order_definable_or.
Check first_order_definable_imp.
Check first_order_definable_not.
Check first_order_definable_iff.
Check first_order_definable_all.
Check first_order_definable_exists.
Check first_order_definable_all_vector.
Check first_order_definable_exists_vector.
Check semiformula_list_conj.
Check semiformula_list_disj.
Check semiformula_eval_list_conj.
Check semiformula_eval_list_disj.
Check first_order_definable_list_all.
Check first_order_definable_list_exists.
Check first_order_definable_finite_all.
Check first_order_definable_finite_exists.
Check fin_t_finite_cover.
Check first_order_definable_retraction.
Check fin_graph_retraction.
Check fin_graph_retraction_head.
Check fin_graph_retraction_tail.
Check fin_graph_retraction_map.
Check fin_graph_retraction_map_head.
Check fin_graph_retraction_map_tail.
Check first_order_definable_graph_family_map.
Check first_order_definable_graph_family.
Check first_order_definable_substitution_witness.
Check first_order_definable_substitution.
Check fin_function_graph_retraction.
Check fin_function_graph_retraction_head.
Check fin_function_graph_retraction_tail.
Check first_order_definable_function_substitution_witness.
Check first_order_definable_function_substitution.
Check first_order_definable_unary_function.
Check first_order_definable_binary_function.
Check first_order_definable_constant.
Check first_order_definable_ternary_function.
Check first_order_definable_quaternary_function.
Check first_order_definable_quinary_function.
Check definability_fin_three.
Check definability_fin_four.
Check definability_fin_five.
Check first_order_definable_function_family_cons.
Check first_order_definable_function_family_three.
Check first_order_definable_function_family_four.
Check first_order_definable_function_family_five.
Check fin_two_definable_function_family.
Check first_order_definable_predicate_comp.
Check first_order_definable_relation_comp.
Check first_order_definable_relation3_comp.
Check first_order_definable_relation4_comp.
Check first_order_definable_relation5_comp.
Check first_order_definable_unary_function_graph.
Check first_order_definable_binary_function_graph.
Check first_order_definable_ternary_function_graph.
Check first_order_definable_unary_function_comp.
Check first_order_definable_binary_function_comp.
Check first_order_definable_ternary_function_comp.
Check first_order_definable_quaternary_function_comp.
Check first_order_definable_quinary_function_comp.
Check first_order_definable_operator_relation.
Check first_order_definable_operator_relation_terms.
Check first_order_definable_eq.
Check first_order_definable_eq_terms.
Check first_order_definable_term_graph.
Check first_order_definable_projection.
Check first_order_definable_parameter_const.
Check first_order_definable_lt.
Check first_order_definable_mem.
Check first_order_sequent.
Check first_order_sequent_shift.
Check first_order_sequent_language_map.
Check first_order_sequent_language_map_shift.
Check first_order_sequent_rewrite.
Check first_order_sequent_rewrite_under_free_shift.
Check first_order_derivation.
Check FODIdentity.
Check FODCut.
Check FODContraction.
Check FODVerum.
Check FODOr.
Check FODAnd.
Check FODAll.
Check FODExists.
Check first_order_derivation_height.
Check first_order_derivation_cast.
Check first_order_derivation_height_cast.
Check first_order_derivation_contra.
Check first_order_derivation_top.
Check first_order_derivation_atomic_identity.
Check first_order_derivation_rotate.
Check first_order_derivation_tensor.
Check first_order_derivation_eta_rewrite.
Check first_order_derivation_eta.
Check first_order_one_sided_lk.
Check first_order_one_sided_lk_cut.
Check first_order_sequent_is_closed.
Check first_order_derivation_close.
Check first_order_derivation_of_is_closed.
Check first_order_lk.
Check first_order_lk_entailment.
Check first_order_lk_principal.
Check first_order_lk_provable.
Check first_order_lk_provable_iff.
Check first_order_lk_provable_cast.
Check first_order_lk_classical.
Check first_order_lk_all.
Check first_order_lk_provable_all_fix_iter.
Check first_order_lk_provable_universal_closure_open.
Check first_order_sentence_embed.
Check first_order_closed_term_embed.
Check first_order_sentence_embed_substitute.
Check first_order_sentence_embed_lk_hom.
Check first_order_sentence_one_sided_lk.
Check first_order_sentence_one_sided_lk_cut.
Check first_order_sentence_lk_entailment.
Check first_order_sentence_lk_system.
Check first_order_sentence_lk_principal.
Check first_order_theory_proof.
Check first_order_theory_entailment.
Check first_order_theory_contextual.
Check first_order_theory_provable.
Check first_order_theory_provable_iff.
Check first_order_theory_inconsistent_iff.
Check first_order_empty_theory_provable_iff.
Check first_order_theory_of_lk_provable.
Check first_order_theory_axiomatized.
Check first_order_theory_compact.
Check first_order_theory_weaker_of_subset.
Check first_order_theory_classical.
Check first_order_theory_deduction.
Check first_order_theory_specialize.
Check first_order_theory_closure.
Check first_order_theory_closure_spec.
Check first_order_derivation2.
Check FOD2Closed.
Check FOD2Axiom.
Check FOD2Verum.
Check FOD2And.
Check FOD2Or.
Check FOD2All.
Check FOD2Exists.
Check FOD2Weakening.
Check FOD2Shift.
Check FOD2Cut.
Check first_order_derivable2.
Check first_order_derivation2_cast.
Check first_order_derivation_to_derivation2.
Check first_order_derivation2_proof_data.
Check first_order_derivation2_axioms.
Check first_order_derivation2_axioms_member.
Check first_order_derivation2_lk.
Check first_order_axiom_suffix.
Check first_order_axiom_suffix_app.
Check first_order_sentence_embed_shift.
Check first_order_axiom_suffix_shift.
Check first_order_sequent_shift_with_axiom_suffix.
Check first_order_derivation_extend_axiom_suffix_right.
Check first_order_derivation_extend_axiom_suffix_left.
Check first_order_derivation_contract_member.
Check first_order_derivation2_proof_data_weaken.
Check first_order_derivation2_proof_data_extend_right.
Check first_order_derivation2_proof_data_extend_left.
Check first_order_derivation2_to_proof_data.
Check first_order_derivation2_to_proof.
Check first_order_derivation2_cut_axioms.
Check first_order_derivable2_cut_axioms.
Check first_order_sentence_embed_neg.
Check first_order_sentence_embed_neg_map.
Check first_order_theory_proof2.
Check first_order_theory_provable2.
Check first_order_theory_proof_to_proof2.
Check first_order_theory_proof2_to_proof.
Check first_order_theory_provable_iff_derivable2.
Check semiformula_repeated_verum.
Check semiformula_padding.
Check semiformula_get_padding_aux.
Check semiformula_get_padding.
Check semiformula_get_padding_formula.
Check semiformula_get_padding_aux_repeated_verum.
Check semiformula_get_padding_padding.
Check semiformula_get_padding_formula_padding.
Check semiformula_padding_injective_iff.
Check semiformula_rewrite_repeated_verum.
Check semiformula_rewrite_padding.
Check semiformula_repeated_verum_raw.
Check semiformula_padding_iff_raw.
Check semiformula_padding_iff_provable.
Check encoding_injective.
Check fin_nat_code.
Check fin_nat_code_injective.
Check fin_nat_decode.
Check fin_nat_decode_code.
Check fin_nat_code_component_le.
Check fin_option_sequence.
Check fin_option_sequence_some.
Check semiterm_code.
Check semiterm_code_bvar.
Check semiterm_code_fvar.
Check semiterm_code_func.
Check semiterm_code_injective.
Check semiterm_decode_fuel.
Check semiterm_decode.
Check semiterm_decode_fuel_code.
Check semiterm_decode_code.
Check semiformula_code.
Check semiformula_code_verum.
Check semiformula_code_falsum.
Check semiformula_code_rel.
Check semiformula_code_nrel.
Check semiformula_code_and.
Check semiformula_code_or.
Check semiformula_code_all.
Check semiformula_code_exists.
Check semiformula_code_injective.
Check semiformula_decode_fuel.
Check semiformula_decode.
Check cantor_payload_lt_fuel.
Check cantor_pair_components_lt_fuel.
Check semiformula_decode_fuel_code.
Check semiformula_decode_code.
Check semiterm_code_emb.
Check semiformula_code_emb.
Check semiformula_code_closed_injection.
Check semiformula_code_closed_injection_rev.
Check semiterm_encoding.
Check semiformula_encoding.
Check semiterm_encoding_encode.
Check semiformula_encoding_encode.
Check oring_carrier.
Check oring_numeral.
Check nat_oring_carrier.
Check nat_oring_numeral.
Check arithmetic_semiterm.
Check arithmetic_sentence.
Check semiterm_godel_number_term.
Check semiterm_godel_number_term_eq.
Check rew_semiterm_godel_number_term.
Check semiterm_one_term.
Check semiterm_add_term.
Check semiterm_add_one.
Check semiterm_val_fin_zero.
Check semiterm_val_fin_two.
Check semiterm_val_one_term.
Check semiterm_val_add_term.
Check semiterm_val_add_one.
Check structure_interprets_oring.
Check semiterm_operator_val_numeral.
Check semiformula_ball_lt_succ.
Check semiformula_bex_lt_succ.
Check semiformula_eval_ball_lt_succ.
Check semiformula_eval_bex_lt_succ.
Check oring_standard_structure.
Check oring_standard_structure_zero.
Check oring_standard_structure_one.
Check oring_standard_structure_add.
Check oring_standard_structure_mul.
Check oring_standard_structure_eq.
Check oring_standard_structure_lt.
Check oring_standard_structure_interprets.
Check first_order_structure_ext.
Check fin_zero_eta.
Check oring_standard_structure_unique.
Check oring_carrier_of_structure.
Check oring_language_eq_operator.
Check structure_interprets_oring_of_structure.
Check nat_standard_structure.
Check nat_standard_structure_interprets.
Check nat_standard_model.
Check arithmetic_theory_proof_complete.
Check arithmetic_theory_weaker_of_models.
Check arithmetic_theory_sound_on.
Check arithmetic_theory_sound_on_elim.
Check arithmetic_theory_sound_on_of_models.
Check arithmetic_theory_consistent_of_sound_on.
Check arithmetic_sigma.
Check arithmetic_pi.
Check arithmetic_polarity_alt.
Check arithmetic_lt_operator.
Check arithmetic_eq_operator.
Check arithmetic_le_operator.
Check arithmetic_lt_guard.
Check arithmetic_bounded_all.
Check arithmetic_bounded_exists.
Check arithmetic_hierarchy.
Check arithmetic_delta_zero.
Check arithmetic_hierarchy_eq.
Check arithmetic_hierarchy_lt.
Check arithmetic_hierarchy_le.
Check arithmetic_lt_guard_rewrite.
Check arithmetic_lt_guard_rewrite_preimage.
Check arithmetic_bounded_all_rewrite_preimage.
Check arithmetic_bounded_exists_rewrite_preimage.
Check arithmetic_hierarchy_rewrite.
Check arithmetic_hierarchy_rewrite_reflect.
Check arithmetic_hierarchy_rewrite_iff.
Check arithmetic_hierarchy_accum.
Check arithmetic_hierarchy_accum_iter.
Check arithmetic_hierarchy_strict_mono.
Check arithmetic_hierarchy_mono.
Check arithmetic_hierarchy_of_zero.
Check arithmetic_hierarchy_zero_alt.
Check arithmetic_hierarchy_zero_iff.
Check arithmetic_hierarchy_and_iff.
Check arithmetic_hierarchy_or_iff.
Check arithmetic_hierarchy_neg.
Check arithmetic_hierarchy_neg_iff.
Check arithmetic_hierarchy_imp_iff.
Check arithmetic_hierarchy_iff_iff.
Check arithmetic_hierarchy_zero_iff_iff.
Check arithmetic_hierarchy_of_open.
Check arithmetic_lt_guard_open.
Check arithmetic_hierarchy_remove_all.
Check arithmetic_hierarchy_remove_exists.
Check arithmetic_hierarchy_bounded_all_iff.
Check arithmetic_hierarchy_bounded_exists_iff.
Check arithmetic_hierarchy_ball_lt_iff.
Check arithmetic_hierarchy_bex_lt_iff.
Check arithmetic_hierarchy_ball_lt_succ_iff.
Check arithmetic_hierarchy_bex_lt_succ_iff.
Check arithmetic_hierarchy_all_iff.
Check arithmetic_hierarchy_exists_iff.
Check arithmetic_hierarchy_all_iter_iff.
Check arithmetic_hierarchy_exists_iter_iff.
Check arithmetic_hierarchy_exists_closure.
Check arithmetic_hierarchy_all_closure.
Check arithmetic_hierarchy_repeated_verum.
Check arithmetic_hierarchy_padding_iff.
Check arithmetic_hierarchy_matrix_conj_iff.
Check arithmetic_hierarchy_matrix_disj_iff.
Check arithmetic_hierarchy_list_conj_iff.
Check arithmetic_hierarchy_list_disj_iff.
Check arithmetic_hierarchy_list_conj_map_iff.
Check arithmetic_hierarchy_list_disj_map_iff.
Check arithmetic_hierarchy_finite_conj_iff.
Check arithmetic_hierarchy_finite_disj_iff.
Check arithmetic_hierarchy_sigma_one_of_base.
Check arithmetic_sigma_one_induction.
Check arithmetic_theory_sound_on_hierarchy.
Check arithmetic_theory_sound_on_hierarchy_elim.
Check arithmetic_theory_consistent_of_sigma_one_sound.
Check arithmetic_theory_consistent_of_pi_two_sound.

Check arithmetic_hierarchy_class.
Check arithmetic_hierarchy_symbol.
Check arithmetic_sigma_symbol.
Check arithmetic_pi_symbol.
Check arithmetic_delta_symbol.
Check arithmetic_sorted_polar_formula.
Check arithmetic_sorted_formula.
Check arithmetic_sorted_formula_val.
Check arithmetic_sorted_sigma_prop.
Check arithmetic_sorted_pi_prop.
Check arithmetic_sorted_delta_sigma.
Check arithmetic_sorted_delta_pi.
Check arithmetic_sorted_rewrite.
Check arithmetic_sorted_rewrite_val.
Check arithmetic_sorted_zero_hierarchy.
Check arithmetic_sorted_of_zero.
Check arithmetic_sorted_of_zero_val.
Check arithmetic_sorted_verum.
Check arithmetic_sorted_falsum.
Check arithmetic_sorted_and.
Check arithmetic_sorted_or.
Check arithmetic_sorted_neg_delta.
Check arithmetic_sorted_ball.
Check arithmetic_sorted_bex.
Check arithmetic_sorted_exists.
Check arithmetic_sorted_all.
Check arithmetic_sorted_and_val.
Check arithmetic_sorted_or_val.
Check arithmetic_sorted_ball_val.
Check arithmetic_sorted_bex_val.
Check first_order_true_arithmetic.
Check first_order_true_arithmetic_models.
Check first_order_true_arithmetic_provable_iff.
Check arithmetic_theory_weaker_than_true_arithmetic.
(* FirstOrder/Arithmetic/TA/Nonstandard.v: compactness nonstandard model. *)
Check nonstandard_language.
Check nonstandard_arithmetic_embedding.
Check nonstandard_star_symbol.
Check nonstandard_star_bound_sentence.
Check nonstandard_star_unbounded_theory.
Check nonstandard_bounded_theory.
Check nonstandard_union_theory.
Check nonstandard_model_structure.
Print Assumptions nonstandard_model_models_arithmetic.
Print Assumptions nonstandard_model_models_equality.
Print Assumptions nonstandard_bound_realize_iff.
Print Assumptions nonstandard_finite_satisfiable.
Print Assumptions nonstandard_union_satisfiable.
Print Assumptions nonstandard_reduct_models_true_arithmetic.
Print Assumptions nonstandard_reduct_models_peano_minus.
Print Assumptions nonstandard_star_unbounded.
Check first_order_structure_monotone.
Check structure_func_monotone.
Check semiterm_val_monotone.
Check semiterm_val_monotone_free.
Check semiterm_val_monotone_bound.
Check semiformula_polarity.
Check semiformula_positive.
Check semiformula_negative.
Check semiformula_polarity_neg.
Check semiformula_polarity_imp.
Check semiformula_rel_positive.
Check semiformula_rel_not_negative.
Check semiformula_nrel_not_positive.
Check semiformula_nrel_negative.
Check semiformula_verum_positive.
Check semiformula_verum_not_negative.
Check semiformula_falsum_not_positive.
Check semiformula_falsum_negative.
Check semiformula_and_positive_iff.
Check semiformula_and_negative_iff.
Check semiformula_or_positive_iff.
Check semiformula_or_negative_iff.
Check semiformula_exists_positive.
Check semiformula_exists_not_negative.
Check semiformula_all_not_positive.
Check semiformula_all_negative.
Check semiformula_neg_positive_iff.
Check semiformula_neg_negative_iff.
Check semiformula_polarity_rewrite.
Check first_order_eqv.
Check first_order_models_equality_axioms.
Check first_order_eqv_refl.
Check first_order_eqv_symm.
Check first_order_eqv_trans.
Check first_order_eqv_func_ext.
Check first_order_eqv_rel_ext.
Check first_order_eqv_equivalence.
Check first_order_eqv_rel_ext_iff.
Check first_order_models_equality_axioms_of_interprets_eq.
Check first_order_eqv_fin_env_cons.
Check semiterm_val_eqv.
Check semiformula_eval_eqv.
Check first_order_derivation_language_map.
Check first_order_lk_provable_language_map.
Check first_order_derivation_rewrite.
Check first_order_derivation_map.
Check first_order_derivation_shift.
Check first_order_fresh_map.
Check semiformula_rewrite_map_substitute_fresh.
Check semiformula_rewrite_map_fresh_eq_shift.
Check first_order_sequent_rewrite_map_fresh_eq_shift.
Check first_order_derivation_generalize_fresh.
Check first_order_sequent_new_variable.
Check first_order_sequent_fv_sup_le_new_variable.
Check first_order_sequent_new_variable_fresh.
Check generic_list_member_of_list_in.
Check first_order_derivation_all_new_variable.
Check generic_list_subset_contract_head.
Check generic_list_subset_weaken_head.
Check first_order_derivation_exists_of_instances.
Check first_order_derivation_exists_of_instances_present.
Check first_order_derivation_height_identity.
Check first_order_derivation_height_cut.
Check first_order_derivation_height_contraction.
Check first_order_derivation_height_or.
Check first_order_derivation_height_and.
Check first_order_derivation_height_all.
Check first_order_derivation_height_exists.
Check first_order_is_cut_free.
Check FOCFIdentity.
Check FOCFVerum.
Check FOCFOr.
Check FOCFAnd.
Check FOCFAll.
Check FOCFExists.
Check FOCFContraction.
Check first_order_is_cut_free_or_iff.
Check first_order_is_cut_free_and_iff.
Check first_order_is_cut_free_all_iff.
Check first_order_is_cut_free_exists_iff.
Check first_order_is_cut_free_contraction_iff.
Check first_order_is_cut_free_cast_iff.
Check first_order_derivation_root_is_cut.
Check first_order_is_cut_free_root_is_not_cut.
Check first_order_is_cut_free_not_cut.
Check first_order_is_cut_free_language_map_iff.
Check first_order_is_cut_free_rewrite_iff.
Check first_order_is_cut_free_map_iff.
Check first_order_is_cut_free_shift_iff.
Check first_order_is_cut_free_generalize_fresh_iff.
Check first_order_is_cut_free_exists_of_instances_iff.
Check first_order_is_cut_free_exists_of_instances_present_iff.
Check first_order_is_cut_free_all_new_variable_iff.
Check first_order_empty_env.
Check first_order_sequent_true.
Check fin_env_snoc_empty_eq_cons.
Check first_order_shifted_context_true.
Check first_order_derivation_sound.
Check first_order_derivation_nil_empty.
Check first_order_sentence_embed_eval.
Check first_order_lk_sound.
Check first_order_theory_proof_sound.
Check first_order_theory_sound.
Check first_order_theory_consistent_of_satisfiable.
Check first_order_theory_consistent_of_model.
Check first_order_theory_unprovable_of_countermodel.
Check first_order_models_of_provable.
Check first_order_models_of_weaker_theory.

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
Print Assumptions rew_comp_emb_substs.
Print Assumptions rew_emb_substs_variables.
Print Assumptions rew_emb_substs_variables_empty.
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
Print Assumptions rew_bshift_positive_iff_exists.
Print Assumptions rew_bshift_not_bvar_zero.
Print Assumptions rew_q_bvar_zero_iff.
Print Assumptions rew_q_positive_iff.
Print Assumptions rew_free_occurs_sources.
Print Assumptions semiterm_language_map_rew_bind.
Print Assumptions semiformula_rewrite_connective_hom.
Print Assumptions semiformula_rewrite_and_preimage.
Print Assumptions semiformula_rewrite_all_preimage.
Print Assumptions semiformula_rewrite_ext.
Print Assumptions semiterm_rew_apply_ext_on_free.
Print Assumptions semiformula_rewrite_ext_on_free.
Print Assumptions semiterm_language_map_rew_apply.
Print Assumptions rew_language_map_q.
Print Assumptions semiformula_language_map_rewrite.
Print Assumptions semiformula_language_map_substitute.
Print Assumptions semiformula_language_map_shift.
Print Assumptions semiformula_language_map_free.
Print Assumptions semiformula_rewrite_id.
Print Assumptions semiformula_rewrite_comp.
Print Assumptions semiformula_rewrite_all_iter.
Print Assumptions semiformula_rewrite_complexity.
Print Assumptions semiformula_rewrite_quantifier_rank.
Print Assumptions semiformula_rewrite_open.
Print Assumptions semiformula_rewrite_free_occurs_sources.
Print Assumptions rew_rewrite_under_free_comp_shift.
Print Assumptions rew_rewrite_under_free_comp_free.
Print Assumptions semiformula_rewrite_under_free_shift.
Print Assumptions semiformula_rewrite_under_free_free.
Print Assumptions rew_subst_bshift_zero.
Print Assumptions rew_rewrite_comp_substitute_one.
Print Assumptions semiformula_rewrite_substitute_one.
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
Print Assumptions semiformula_rewrite_map_injective.
Print Assumptions rew_q_cast.
Print Assumptions fin_cast_le_zero.
Print Assumptions fin_cast_le_succ.
Print Assumptions rew_q_cast_le.
Print Assumptions rew_qpow_cast_le_bvar.
Print Assumptions rew_qpow_cast_le_fvar.
Print Assumptions rew_qpow_cast_le.
Print Assumptions semiformula_rewrite_emb_injective.
Print Assumptions semiformula_rewrite_eq_verum_iff.
Print Assumptions semiformula_rewrite_eq_falsum_iff.
Print Assumptions semiformula_rewrite_eq_rel_iff.
Print Assumptions semiformula_rewrite_eq_nrel_iff.
Print Assumptions semiformula_rewrite_eq_and_iff.
Print Assumptions semiformula_rewrite_eq_or_iff.
Print Assumptions semiformula_rewrite_eq_all_iff.
Print Assumptions semiformula_rewrite_eq_exists_iff.
Print Assumptions semiformula_rewrite_eq_imp_iff.
Print Assumptions semiformula_rewrite_eq_bounded_all_iff.
Print Assumptions semiformula_rewrite_eq_bounded_exists_iff.
Print Assumptions rew_semiterm_operator_apply.
Print Assumptions semiterm_operator_comp_assoc.
Print Assumptions semiterm_operator_apply_bound_occurs.
Print Assumptions semiterm_operator_apply_positive.
Print Assumptions semiterm_const_operator_positive.
Print Assumptions semiterm_operator_foldr_cons_apply.
Print Assumptions semiterm_add_operator_positive.
Print Assumptions semiterm_mul_operator_positive.
Print Assumptions semiterm_exp_operator_positive.
Print Assumptions semiterm_operator_numeral_succ_nonzero.
Print Assumptions semiterm_operator_iterr_succ.
Print Assumptions semiterm_operator_npow_positive.
Print Assumptions semiterm_add_operator_complexity.
Print Assumptions rew_semiformula_operator_apply.
Print Assumptions semiformula_operator_comp_assoc.
Print Assumptions semiformula_rewrite_binary_relation_preimage.
Print Assumptions semiformula_rewrite_eq_operator_preimage.
Print Assumptions semiformula_binary_relation_injective.
Print Assumptions semiformula_eq_operator_injective.
Print Assumptions semiformula_le_operator_injective.
Print Assumptions semiterm_val_rewrite.
Print Assumptions semiterm_val_language_map.
Print Assumptions semiterm_val_transport.
Print Assumptions semiterm_val_free_ext.
Print Assumptions semiterm_val_rew_emb_bvars.
Print Assumptions semiterm_val_rew_emb_fvars.
Print Assumptions semiterm_val_to_closed.
Print Assumptions semiterm_val_shift.
Print Assumptions semiterm_val_free.
Print Assumptions semiterm_val_fix.
Print Assumptions semiformula_eval_neg.
Print Assumptions semiformula_eval_iff.
Print Assumptions semiformula_eval_bounded_all.
Print Assumptions semiformula_eval_rewrite.
Print Assumptions semiformula_eval_free_ext.
Print Assumptions semiformula_eval_bound_ext.
Print Assumptions semiformula_eval_to_closed.
Print Assumptions semiformula_eval_enumerate_index_of_free_variable.
Print Assumptions semiformula_eval_language_map.
Print Assumptions semiformula_eval_transport.
Print Assumptions semiformula_eval_free.
Print Assumptions semiformula_eval_shift.
Print Assumptions semiformula_eval_all_iter.
Print Assumptions semiformula_eval_exists_iter.
Print Assumptions semiformula_eval_all_closure.
Print Assumptions semiformula_eval_exists_closure.
Print Assumptions semiformula_eval_fix_all_free.
Print Assumptions formula_eval_universal_closure_open.
Print Assumptions sentence_realize_universal_closure.
Print Assumptions semiterm_val_operator_apply.
Print Assumptions semiterm_operator_val_comp.
Print Assumptions semiterm_operator_val_transport.
Print Assumptions semiformula_eval_operator_apply.
Print Assumptions semiformula_operator_eval_comp.
Print Assumptions semiformula_operator_eval_transport.
Print Assumptions structure_interprets_le_of_eq_lt.
Print Assumptions structure_interprets_le_of_eq_lt_spec.
Print Assumptions semiformula_eval_bounded_operator_all.
Print Assumptions semiformula_eval_bounded_operator_exists.
Print Assumptions semiformula_eval_ball_relation.
Print Assumptions semiformula_eval_bex_relation.
Print Assumptions first_order_tarski.
Print Assumptions first_order_models_theory_iff.
Print Assumptions first_order_satisfiable_iff.
Print Assumptions first_order_unsatisfiable_iff.
Print Assumptions first_order_consequence_iff.
Print Assumptions first_order_consequence_iff_unsatisfiable.
Print Assumptions first_order_consequence_weakening.
Print Assumptions first_order_model_theory_satisfiable.
Print Assumptions first_order_model_realize_language_map.
Print Assumptions first_order_consequence_language_map.
Print Assumptions first_order_hom_semiterm_val.
Print Assumptions first_order_embedding_eval_open.
Print Assumptions first_order_embedding_eval_all_closure_open.
Print Assumptions first_order_closed_subset_inclusion.
Print Assumptions semiformula_eval_carrier_equiv.
Print Assumptions first_order_elementary_equiv_models_theory.
Print Assumptions first_order_elementary_equiv_of_carrier_equiv.
Print Assumptions structure_model_elementary_equiv.
Print Assumptions structure_model_interprets_relation.
Print Assumptions structure_model_interprets_eq.
Print Assumptions semiterm_val_language_add_left.
Print Assumptions semiformula_eval_language_add_left.
Print Assumptions semiterm_val_language_sigma.
Print Assumptions semiformula_eval_language_sigma.
Print Assumptions semiterm_val_structure_lift.
Print Assumptions semiformula_eval_structure_lift.
Print Assumptions structure_lift_elementary_equiv.
Print Assumptions semiformula_eval_embed_empty.
Print Assumptions first_order_defined_to_definable.
Print Assumptions first_order_definable_of_iff.
Print Assumptions first_order_definable_const.
Print Assumptions first_order_definable_and.
Print Assumptions first_order_definable_all.
Print Assumptions first_order_definable_exists.
Print Assumptions first_order_definable_all_vector.
Print Assumptions first_order_definable_exists_vector.
Print Assumptions semiformula_eval_list_conj.
Print Assumptions semiformula_eval_list_disj.
Print Assumptions first_order_definable_list_all.
Print Assumptions first_order_definable_list_exists.
Print Assumptions first_order_definable_finite_all.
Print Assumptions first_order_definable_finite_exists.
Print Assumptions first_order_definable_retraction.
Print Assumptions fin_env_append_left.
Print Assumptions fin_env_append_right.
Print Assumptions fin_env_append_left_eta.
Print Assumptions fin_env_append_right_eta.
Print Assumptions first_order_definable_graph_family.
Print Assumptions first_order_definable_graph_family_map.
Print Assumptions first_order_definable_substitution_witness.
Print Assumptions first_order_definable_substitution.
Print Assumptions first_order_definable_function_substitution_witness.
Print Assumptions first_order_definable_function_substitution.
Print Assumptions first_order_definable_function_family_cons.
Print Assumptions first_order_definable_function_family_three.
Print Assumptions first_order_definable_function_family_four.
Print Assumptions first_order_definable_function_family_five.
Print Assumptions fin_two_definable_function_family.
Print Assumptions first_order_definable_predicate_comp.
Print Assumptions first_order_definable_relation_comp.
Print Assumptions first_order_definable_relation3_comp.
Print Assumptions first_order_definable_relation4_comp.
Print Assumptions first_order_definable_relation5_comp.
Print Assumptions first_order_definable_unary_function_graph.
Print Assumptions first_order_definable_binary_function_graph.
Print Assumptions first_order_definable_ternary_function_graph.
Print Assumptions first_order_definable_unary_function_comp.
Print Assumptions first_order_definable_binary_function_comp.
Print Assumptions first_order_definable_ternary_function_comp.
Print Assumptions first_order_definable_quaternary_function_comp.
Print Assumptions first_order_definable_quinary_function_comp.
Print Assumptions first_order_definable_operator_relation.
Print Assumptions first_order_definable_operator_relation_terms.
Print Assumptions first_order_definable_eq.
Print Assumptions first_order_definable_eq_terms.
Print Assumptions first_order_definable_term_graph.
Print Assumptions first_order_definable_projection.
Print Assumptions first_order_definable_parameter_const.
Print Assumptions first_order_derivation_height_cast.
Print Assumptions first_order_derivation_top.
Print Assumptions first_order_derivation_atomic_identity.
Print Assumptions first_order_derivation_rotate.
Print Assumptions first_order_derivation_tensor.
Print Assumptions semiformula_substitute_shift_one_eq_free.
Print Assumptions semiformula_substitute_neg_shift_one_eq_neg_free.
Print Assumptions semiformula_free_neg.
Print Assumptions semiformula_shift_exists.
Print Assumptions first_order_derivation_eta_rewrite.
Print Assumptions first_order_derivation_eta.
Print Assumptions first_order_one_sided_lk.
Print Assumptions first_order_one_sided_lk_cut.
Print Assumptions first_order_derivation_close.
Print Assumptions first_order_derivation_of_is_closed.
Print Assumptions first_order_lk_principal.
Print Assumptions first_order_lk_provable_iff.
Print Assumptions first_order_lk_provable_cast.
Print Assumptions first_order_lk_classical.
Print Assumptions first_order_lk_all.
Print Assumptions rew_q_fix.
Print Assumptions semiformula_fix_all.
Print Assumptions semiformula_fix_all_closure.
Print Assumptions semiformula_all_iter_closure.
Print Assumptions semiformula_rewrite_fix_iter_zero.
Print Assumptions semiformula_fix_rewrite_fix_iter.
Print Assumptions semiformula_rewrite_cast.
Print Assumptions semiformula_all_closure_cast.
Print Assumptions semiformula_all_fix_iter_closure_step.
Print Assumptions first_order_lk_provable_all_fix_iter.
Print Assumptions first_order_lk_provable_universal_closure_open.
Print Assumptions first_order_sentence_embed_substitute.
Print Assumptions first_order_sentence_embed_lk_hom.
Print Assumptions first_order_sentence_one_sided_lk.
Print Assumptions first_order_sentence_one_sided_lk_cut.
Print Assumptions first_order_sentence_lk_principal.
Print Assumptions first_order_theory_contextual.
Print Assumptions first_order_theory_provable_iff.
Print Assumptions first_order_theory_inconsistent_iff.
Print Assumptions first_order_empty_theory_provable_iff.
Print Assumptions first_order_theory_of_lk_provable.
Print Assumptions first_order_theory_axiomatized.
Print Assumptions first_order_theory_compact.
Print Assumptions first_order_theory_weaker_of_subset.
Print Assumptions first_order_theory_classical.
Print Assumptions first_order_theory_deduction.
Print Assumptions first_order_theory_specialize.
Print Assumptions first_order_theory_closure_spec.
Print Assumptions first_order_derivation2_cast.
Print Assumptions first_order_derivation_to_derivation2.
Print Assumptions first_order_sentence_embed_shift.
Print Assumptions first_order_axiom_suffix_shift.
Print Assumptions first_order_derivation2_to_proof_data.
Print Assumptions first_order_derivation2_cut_axioms.
Print Assumptions first_order_theory_proof_to_proof2.
Print Assumptions first_order_theory_proof2_to_proof.
Print Assumptions first_order_theory_provable_iff_derivable2.
Print Assumptions semiformula_get_padding_padding.
Print Assumptions semiformula_padding_injective_iff.
Print Assumptions semiformula_rewrite_padding.
Print Assumptions semiformula_padding_iff_raw.
Print Assumptions semiformula_padding_iff_provable.
Print Assumptions fin_nat_code_injective.
Print Assumptions fin_nat_decode_code.
Print Assumptions fin_option_sequence_some.
Print Assumptions semiterm_code_injective.
Print Assumptions semiterm_decode_fuel_code.
Print Assumptions semiterm_decode_code.
Print Assumptions semiformula_code_injective.
Print Assumptions semiformula_decode_fuel_code.
Print Assumptions semiformula_decode_code.
Print Assumptions semiterm_code_emb.
Print Assumptions semiformula_code_emb.
Print Assumptions semiformula_code_closed_injection.
Print Assumptions semiterm_encoding.
Print Assumptions semiformula_encoding.
Print Assumptions nat_oring_numeral.
Print Assumptions rew_semiterm_godel_number_term.
Print Assumptions semiterm_val_add_one.
Print Assumptions semiterm_operator_val_numeral.
Print Assumptions semiformula_eval_ball_lt_succ.
Print Assumptions semiformula_eval_bex_lt_succ.
Print Assumptions oring_standard_structure_interprets.
Print Assumptions first_order_structure_ext.
Print Assumptions oring_standard_structure_unique.
Print Assumptions structure_interprets_oring_of_structure.
Print Assumptions arithmetic_theory_proof_complete.
Print Assumptions arithmetic_theory_weaker_of_models.
Print Assumptions nat_standard_structure_interprets.
Print Assumptions arithmetic_theory_sound_on_of_models.
Print Assumptions arithmetic_theory_consistent_of_sound_on.
Print Assumptions arithmetic_lt_guard_rewrite.
Print Assumptions arithmetic_lt_guard_rewrite_preimage.
Print Assumptions arithmetic_bounded_all_rewrite_preimage.
Print Assumptions arithmetic_bounded_exists_rewrite_preimage.
Print Assumptions arithmetic_hierarchy_rewrite.
Print Assumptions arithmetic_hierarchy_rewrite_reflect.
Print Assumptions arithmetic_hierarchy_rewrite_iff.
Print Assumptions arithmetic_hierarchy_accum.
Print Assumptions arithmetic_hierarchy_strict_mono.
Print Assumptions arithmetic_hierarchy_of_zero.
Print Assumptions arithmetic_hierarchy_zero_iff.
Print Assumptions arithmetic_hierarchy_and_iff.
Print Assumptions arithmetic_hierarchy_or_iff.
Print Assumptions arithmetic_hierarchy_neg.
Print Assumptions arithmetic_hierarchy_neg_iff.
Print Assumptions arithmetic_hierarchy_imp_iff.
Print Assumptions arithmetic_hierarchy_iff_iff.
Print Assumptions arithmetic_hierarchy_of_open.
Print Assumptions arithmetic_hierarchy_remove_all.
Print Assumptions arithmetic_hierarchy_remove_exists.
Print Assumptions arithmetic_hierarchy_bounded_all_iff.
Print Assumptions arithmetic_hierarchy_bounded_exists_iff.
Print Assumptions arithmetic_hierarchy_all_iter_iff.
Print Assumptions arithmetic_hierarchy_exists_iter_iff.
Print Assumptions arithmetic_hierarchy_exists_closure.
Print Assumptions arithmetic_hierarchy_all_closure.
Print Assumptions arithmetic_hierarchy_padding_iff.
Print Assumptions arithmetic_hierarchy_matrix_conj_iff.
Print Assumptions arithmetic_hierarchy_matrix_disj_iff.
Print Assumptions arithmetic_hierarchy_list_conj_iff.
Print Assumptions arithmetic_hierarchy_list_disj_iff.
Print Assumptions arithmetic_hierarchy_list_conj_map_iff.
Print Assumptions arithmetic_hierarchy_list_disj_map_iff.
Print Assumptions arithmetic_hierarchy_finite_conj_iff.
Print Assumptions arithmetic_hierarchy_finite_disj_iff.
Print Assumptions arithmetic_hierarchy_sigma_one_of_base.
Print Assumptions arithmetic_sigma_one_induction.
Print Assumptions arithmetic_theory_consistent_of_sigma_one_sound.
Print Assumptions arithmetic_theory_consistent_of_pi_two_sound.
Print Assumptions arithmetic_empty_valuation_unique.
Print Assumptions arithmetic_sigma_one_upward_absolute.
Print Assumptions arithmetic_pi_one_downward_absolute.
Print Assumptions arithmetic_sigma_zero_absolute.
Print Assumptions arithmetic_delta_one_absolute.
Print Assumptions arithmetic_sigma_one_semisentence_upward_absolute.
Print Assumptions arithmetic_pi_one_semisentence_downward_absolute.
Print Assumptions arithmetic_sigma_zero_semisentence_absolute.
Print Assumptions arithmetic_delta_one_semisentence_absolute.
Print Assumptions arithmetic_delta_one_defined_absolute.
Print Assumptions arithmetic_sigma_zero_defined_absolute.
Print Assumptions arithmetic_delta_one_defined_function_absolute.
Print Assumptions arithmetic_sigma_zero_defined_function_absolute.
Check arithmetic_numeral_instance.
Print Assumptions arithmetic_numeral_instance_hierarchy.
Print Assumptions arithmetic_numeral_instance_realize_iff_in_structure.
Print Assumptions arithmetic_numeral_instance_realize_iff.
Print Assumptions arithmetic_sigma_one_provable_iff_with_numeral_parameters.
Print Assumptions arithmetic_sigma_zero_model_iff_provable_with_numeral_parameters.
Print Assumptions arithmetic_delta_one_model_iff_provable_with_numeral_parameters.
Print Assumptions arithmetic_sorted_rewrite.
Print Assumptions arithmetic_sorted_rewrite_val.
Print Assumptions arithmetic_sorted_zero_hierarchy.
Print Assumptions arithmetic_sorted_of_zero.
Print Assumptions arithmetic_sorted_of_zero_val.
Print Assumptions arithmetic_sorted_and.
Print Assumptions arithmetic_sorted_or.
Print Assumptions arithmetic_sorted_neg_sigma.
Print Assumptions arithmetic_sorted_neg_pi.
Print Assumptions arithmetic_sorted_neg_delta.
Print Assumptions arithmetic_sorted_ball.
Print Assumptions arithmetic_sorted_bex.
Print Assumptions arithmetic_sorted_exists.
Print Assumptions arithmetic_sorted_all.
Print Assumptions arithmetic_sorted_exists_iter.
Print Assumptions arithmetic_sorted_all_iter.
Print Assumptions arithmetic_sorted_graph_uniqueness_reindex.
Print Assumptions arithmetic_sorted_graph_uniqueness_reindex_head.
Print Assumptions arithmetic_sorted_graph_uniqueness_reindex_tail.
Print Assumptions arithmetic_sorted_graph_uniqueness_body.
Print Assumptions arithmetic_sorted_graph_delta.
Print Assumptions arithmetic_sorted_graph_delta_val.
Print Assumptions arithmetic_sorted_delta_proper.
Print Assumptions arithmetic_sorted_delta_proper_on.
Print Assumptions arithmetic_sorted_delta_proper_sentence.
Print Assumptions arithmetic_sorted_delta_provably_proper.
Print Assumptions arithmetic_sorted_delta_proper_sentence_eval.
Print Assumptions arithmetic_sorted_delta_provably_proper_of_semantic.
Print Assumptions arithmetic_sorted_delta_provably_proper_on_model.
Print Assumptions arithmetic_sorted_delta_proper_with_params_on.
Print Assumptions arithmetic_sorted_delta_uniformly_proper.
Print Assumptions arithmetic_sorted_delta_pi_eval_iff.
Print Assumptions arithmetic_sorted_delta_proper_of_zero.
Print Assumptions arithmetic_sorted_delta_proper_and.
Print Assumptions arithmetic_sorted_delta_proper_or.
Print Assumptions arithmetic_sorted_delta_proper_neg.
Print Assumptions arithmetic_sorted_delta_eval_neg_iff.
Print Assumptions arithmetic_sorted_delta_proper_ball.
Print Assumptions arithmetic_sorted_delta_proper_bex.
Print Assumptions arithmetic_sorted_delta_uniformly_proper_rewrite.
Print Assumptions arithmetic_sorted_delta_proper_on_rewrite.
Print Assumptions arithmetic_sorted_delta_proper_on_rewrite_with_params.
Print Assumptions arithmetic_sorted_delta_proper_with_params_on_subst.
Print Assumptions arithmetic_sorted_formula_proper.
Print Assumptions arithmetic_sorted_is_defined_by.
Print Assumptions arithmetic_sorted_is_defined_by_with_params.
Print Assumptions arithmetic_sorted_defined.
Print Assumptions arithmetic_sorted_definable.
Print Assumptions arithmetic_sorted_defined_to_definable.
Print Assumptions arithmetic_sorted_definable_of_zero.
Print Assumptions arithmetic_sorted_definable_of_delta.
Print Assumptions arithmetic_sorted_definable_delta_of_sigma_pi.
Print Assumptions arithmetic_sorted_definable_and.
Print Assumptions arithmetic_sorted_definable_or.
Print Assumptions arithmetic_sorted_definable_not_sigma.
Print Assumptions arithmetic_sorted_definable_not_pi.
Print Assumptions arithmetic_sorted_definable_not_delta.
Print Assumptions arithmetic_sorted_definable_verum.
Print Assumptions arithmetic_sorted_definable_falsum.
Print Assumptions arithmetic_sorted_definable_imp_sigma.
Print Assumptions arithmetic_sorted_definable_imp_pi.
Print Assumptions arithmetic_sorted_definable_imp_delta.
Print Assumptions arithmetic_sorted_definable_iff_delta.
Print Assumptions arithmetic_sorted_definable_list_conj.
Print Assumptions arithmetic_sorted_definable_list_disj.
Print Assumptions arithmetic_sorted_definable_finite_conj.
Print Assumptions arithmetic_sorted_definable_finite_disj.
Print Assumptions arithmetic_sorted_eq.
Print Assumptions arithmetic_sorted_eq_val.
Print Assumptions arithmetic_sorted_definable_eq_terms.
Print Assumptions arithmetic_sorted_definable_lt_terms.
Print Assumptions arithmetic_sorted_definable_le_terms.
Print Assumptions arithmetic_sorted_definable_eq_relation.
Print Assumptions arithmetic_sorted_definable_lt_relation.
Print Assumptions arithmetic_sorted_definable_le_relation.
Print Assumptions arithmetic_sorted_definable_term_graph.
Print Assumptions arithmetic_sorted_definable_projection.
Print Assumptions arithmetic_sorted_definable_parameter_constant.
Print Assumptions arithmetic_sorted_definable_add_function.
Print Assumptions arithmetic_sorted_definable_mul_function.
Print Assumptions arithmetic_sorted_definable_substitute_bound.
Print Assumptions arithmetic_sorted_definable_retraction.
Print Assumptions arithmetic_sorted_definable_ball.
Print Assumptions arithmetic_sorted_definable_bex.
Print Assumptions arithmetic_sorted_definable_exists.
Print Assumptions arithmetic_sorted_definable_all.
Print Assumptions arithmetic_sorted_definable_exists_vector.
Print Assumptions arithmetic_sorted_definable_all_vector.
Print Assumptions arithmetic_sorted_definable_graph_family.
Print Assumptions arithmetic_sorted_definable_substitution_sigma.
Print Assumptions arithmetic_sorted_definable_substitution_pi.
Print Assumptions arithmetic_sorted_definable_substitution.
Print Assumptions arithmetic_function_graph_reindex.
Print Assumptions arithmetic_sorted_definable_function_retraction.
Print Assumptions arithmetic_function_substitution_family.
Print Assumptions arithmetic_sorted_definable_function_substitution.
Print Assumptions arithmetic_function_graph_uniqueness_reindex.
Print Assumptions arithmetic_sorted_definable_function_graph_delta_positive.
Print Assumptions arithmetic_sorted_definable_function_graph_delta.
Print Assumptions arithmetic_sorted_definable_function_of_sigma.
Print Assumptions arithmetic_bounded_function.
Print Assumptions arithmetic_bounded_variable.
Print Assumptions arithmetic_bounded_constant.
Print Assumptions arithmetic_bounded_term_function.
Print Assumptions arithmetic_bounded_substitute_bound.
Print Assumptions arithmetic_bounded_retraction.
Print Assumptions arithmetic_bounded_term_retraction.
Print Assumptions arithmetic_bounded_compose.
Print Assumptions arithmetic_bounded_compose_one.
Print Assumptions arithmetic_bounded_compose_two.
Print Assumptions fin_graph_reindex.
Print Assumptions arithmetic_definably_bounded_function.
Print Assumptions arithmetic_definably_bounded_variable.
Print Assumptions arithmetic_definably_bounded_constant.
Print Assumptions arithmetic_definably_bounded_term.
Print Assumptions arithmetic_bounded_of_pointwise_eq.
Print Assumptions arithmetic_definably_bounded_of_pointwise_eq.
Print Assumptions arithmetic_definably_bounded_retraction.
Print Assumptions arithmetic_interpreted_lt.
Print Assumptions arithmetic_sorted_definable_substitution_one_strictly_bounded.
Print Assumptions arithmetic_sorted_definable_compose_predicate_one_strictly_bounded.
Print Assumptions arithmetic_sorted_definable_bex_vector_terms.
Print Assumptions arithmetic_sorted_definable_graph_family_zero.
Print Assumptions arithmetic_sorted_definable_substitution_strictly_bounded_with_params.
Print Assumptions arithmetic_sorted_definable_substitution_strictly_bounded.
Print Assumptions arithmetic_bounded_outer_graph_reindex.
Print Assumptions arithmetic_sorted_definable_function_substitution_strictly_bounded.
Print Assumptions arithmetic_definably_bounded_lift_to_strict.
Print Assumptions arithmetic_sorted_definable_substitution_bounded.
Print Assumptions arithmetic_sorted_definable_function_substitution_bounded.
Print Assumptions arithmetic_definably_bounded_compose.
Print Assumptions arithmetic_bounded_add.
Print Assumptions arithmetic_bounded_mul.
Print Assumptions arithmetic_definably_bounded_add.
Print Assumptions arithmetic_definably_bounded_mul.
Print Assumptions peano_minus_laws.
Print Assumptions peano_minus_le_trans.
Print Assumptions peano_minus_le_lt_trans.
Print Assumptions peano_minus_lt_le_trans.
Print Assumptions peano_minus_le_antisym.
Print Assumptions peano_minus_le_total.
Print Assumptions peano_minus_add_right_cancel.
Print Assumptions peano_minus_add_left_cancel.
Print Assumptions peano_minus_lt_not_ge.
Print Assumptions peano_minus_lt_of_add_lt_add_right.
Print Assumptions peano_minus_lt_of_add_lt_add_left.
Print Assumptions peano_minus_le_of_add_le_add_right.
Print Assumptions peano_minus_le_of_add_le_add_left.
Print Assumptions peano_minus_add_mul_distr.
Print Assumptions peano_minus_zero_mul.
Print Assumptions peano_minus_one_mul.
Print Assumptions peano_minus_positive_eq_add_one.
Print Assumptions peano_minus_lt_of_not_le.
Print Assumptions peano_minus_le_of_not_lt.
Print Assumptions peano_minus_add_one_le_of_lt.
Print Assumptions peano_minus_lt_add_one.
Print Assumptions peano_minus_le_iff_lt_add_one.
Print Assumptions peano_minus_add_lt_add_left.
Print Assumptions peano_minus_add_lt_add_both.
Print Assumptions peano_minus_add_swap_middle.
Print Assumptions peano_minus_add_le_add.
Print Assumptions peano_minus_le_add_right.
Print Assumptions peano_minus_le_add_left.
Print Assumptions peano_minus_mul_le_mul.
Print Assumptions peano_minus_square_le_square.
Print Assumptions peano_minus_square_lt_square.
Print Assumptions peano_minus_square_succ.
Print Assumptions peano_minus_le_square.
Print Assumptions peano_minus_lt_square_of_one_lt.
Print Assumptions peano_minus_structure_monotone.
Print Assumptions peano_minus_not_lt_zero.
Print Assumptions peano_minus_numeral_succ.
Print Assumptions peano_minus_numeral_add.
Print Assumptions peano_minus_numeral_mul.
Print Assumptions peano_minus_numeral_lt.
Print Assumptions peano_minus_numeral_ne.
Print Assumptions peano_minus_eq_numeral_of_lt_numeral.
Print Assumptions peano_minus_lt_numeral_iff.
Print Assumptions peano_minus_le_numeral_iff.
Print Assumptions peano_minus_lt_iff_add_one_le.
Print Assumptions peano_minus_positive_iff_one_le.
Print Assumptions peano_minus_one_lt_iff_two_le.
Print Assumptions peano_minus_lt_two_iff_le_one.
Check peano_minus_pow.
Print Assumptions peano_minus_pow_zero.
Print Assumptions peano_minus_pow_succ.
Print Assumptions peano_minus_pow_one.
Print Assumptions peano_minus_pow_two.
Print Assumptions peano_minus_pow_three.
Print Assumptions peano_minus_pow_four.
Print Assumptions peano_minus_pow_four_square_square.
Print Assumptions peano_minus_pow_le_pow.
Print Assumptions peano_minus_square_le_square_iff.
Print Assumptions peano_minus_square_lt_square_iff.
Print Assumptions peano_minus_zero_lt_square_iff.
Print Assumptions peano_minus_one_lt_square_iff.
Print Assumptions peano_minus_square_eq_one_iff.
Print Assumptions peano_minus_two_mul_two.
Print Assumptions peano_minus_two_pow_two.
Print Assumptions peano_minus_lt_one_iff_zero.
Print Assumptions peano_minus_le_one_iff.
Print Assumptions peano_minus_le_two_iff.
Print Assumptions peano_minus_le_three_iff.
Print Assumptions r0_laws.
Print Assumptions r0_numeral_eq_iff.
Print Assumptions r0_numeral_lt_iff.
Print Assumptions r0_lt_numeral_fin_iff.
Print Assumptions r0_semiterm_val_numeral.
Print Assumptions r0_numeral_fin_env_cons.
Print Assumptions r0_positive_atom_transport.
Print Assumptions r0_negative_atom_transport.
Print Assumptions r0_sigma_one_eval_transport.
Print Assumptions r0_pi_one_eval_reflection.
Print Assumptions r0_sigma_one_model_complete.
Print Assumptions r0_sigma_one_semisentence_transport.
Print Assumptions r0_pi_one_model_reflection.
Print Assumptions nat_r0_laws.
Print Assumptions peano_minus_r0_laws.
Check r0_numeral_add_sentence.
Check r0_numeral_mul_sentence.
Check r0_numeral_ne_sentence.
Check r0_initial_segment_sentence.
Check r0_axiom.
Print Assumptions r0_proves_equality.
Print Assumptions r0_numeral_add_realize_iff.
Print Assumptions r0_numeral_mul_realize_iff.
Print Assumptions r0_numeral_ne_realize_iff.
Print Assumptions r0_initial_segment_realize_iff.
Print Assumptions first_order_model_models_r0_iff.
Print Assumptions nat_standard_model_models_r0.
Print Assumptions r0_consistent.
Print Assumptions r0_proof_complete.
Print Assumptions r0_sigma_one_proof_complete.
Print Assumptions r0_sigma_one_provable_iff.
Print Assumptions primitive_recursive1_constant.
Print Assumptions primitive_recursive1_compose_binary.
Print Assumptions r0_semiterm_primitive_recursive.
Check arithmetically_semidecidable.
Check r0_arith_code_domain_formula.
Print Assumptions r0_arith_code_domain_formula_sigma_one.
Print Assumptions r0_arith_code_domain_formula_eval.
Print Assumptions r0_arith_part1_graph_representation.
Print Assumptions r0_partial_recursive1_graph_representation.
Print Assumptions r0_arithmetically_semidecidable_representation.
Print Assumptions
  r0_arithmetically_semidecidable_provability_representation.
Check r0_arith_code_graph.
Check r0_arith_code_graph_open.
Check r0_arith_code_graph_semisentence.
Print Assumptions r0_arith_code_graph_sigma_one.
Print Assumptions r0_arith_code_graph_open_sigma_one.
Print Assumptions r0_arith_code_graph_semisentence_sigma_one.
Check r0_arith_code_graph_open_sorted.
Check r0_arith_code_graph_semisentence_sorted.
Print Assumptions r0_code_graph_lift_term_val.
Print Assumptions r0_code_graph_shift2_term_val.
Print Assumptions r0_code_graph_find_arguments_val.
Print Assumptions r0_arith_code_graph_eval.
Print Assumptions r0_arith_code_graph_open_eval.
Print Assumptions r0_arith_code_graph_semisentence_eval.
Print Assumptions semidecidable_ext.
Print Assumptions semidecidable_prefix_recognizer_spec.
Print Assumptions semidecidable_bounded_forall_nat.
Print Assumptions r0_semiformula_eval_ball_lt.
Print Assumptions r0_sigma_one_semidecidable.
Check r0_sigma_one_witnessed.
Print Assumptions concrete_beta_finite_choice.
Print Assumptions r0_sigma_one_witness_normal_form.
Print Assumptions arith_find_positive_on_dom_iff.
Print Assumptions r0_sigma_one_arithmetically_semidecidable.
Check r0_omega_add_one.
Check r0_omega_add_one_oring.
Print Assumptions r0_omega_add_one_numeral.
Print Assumptions r0_omega_add_one_laws.
Check r0_omega_add_one_model.
Print Assumptions r0_omega_add_one_model_models_r0.
Print Assumptions r0_omega_add_one_top_add_zero.
Check oring_language_eq_operator.
Check arithmetic_add_term.
Check arithmetic_mul_term.
Check arithmetic_numeral_term.
Check arithmetic_eq_formula.
Check arithmetic_lt_formula.
Check arithmetic_le_formula.
Check arithmetic_eq_disjunction.
Print Assumptions arithmetic_one_term_val.
Print Assumptions arithmetic_add_term_val.
Print Assumptions arithmetic_mul_term_val.
Print Assumptions arithmetic_numeral_term_val.
Print Assumptions first_order_matrix_disj_eval.
Print Assumptions arithmetic_eq_formula_eval.
Print Assumptions arithmetic_lt_formula_eval.
Print Assumptions arithmetic_le_formula_eval.
Print Assumptions arithmetic_eq_disjunction_eval.
Check robinson_q_succ_ne_zero_sentence.
Check robinson_q_succ_inj_sentence.
Check robinson_q_zero_or_succ_sentence.
Check robinson_q_add_zero_sentence.
Check robinson_q_add_succ_sentence.
Check robinson_q_mul_zero_sentence.
Check robinson_q_mul_succ_sentence.
Check robinson_q_lt_def_sentence.
Check robinson_q_axiom.
Check robinson_q_axiom_list.
Print Assumptions robinson_q_axiom_list_complete.
Print Assumptions robinson_q_axiom_finitely_covered.
Print Assumptions robinson_q_proves_equality.
Print Assumptions arithmetic_all_sentence_eval.
Print Assumptions robinson_q_succ_ne_zero_realize_iff.
Print Assumptions robinson_q_succ_inj_realize_iff.
Print Assumptions robinson_q_zero_or_succ_realize_iff.
Print Assumptions robinson_q_add_zero_realize_iff.
Print Assumptions robinson_q_add_succ_realize_iff.
Print Assumptions robinson_q_mul_zero_realize_iff.
Print Assumptions robinson_q_mul_succ_realize_iff.
Print Assumptions robinson_q_lt_def_realize_iff.
Print Assumptions robinson_q_laws.
Print Assumptions first_order_model_models_robinson_q_iff.
Print Assumptions robinson_q_exists_succ_of_ne_zero.
Print Assumptions robinson_q_exists_succ_of_ne_zero'.
Print Assumptions robinson_q_one_ne_zero.
Print Assumptions robinson_q_zero_add_one.
Print Assumptions robinson_q_eq_zero_of_add_eq_zero.
Print Assumptions robinson_q_lt_of_add_nonzero.
Print Assumptions robinson_q_lt_one_iff_eq_zero.
Print Assumptions robinson_q_numeral_succ.
Print Assumptions robinson_q_numeral_add.
Print Assumptions robinson_q_numeral_mul.
Print Assumptions robinson_q_numeral_zero_succ_ne.
Print Assumptions robinson_q_numeral_ne.
Print Assumptions robinson_q_numeral_eq_iff.
Print Assumptions robinson_q_numeral_lt.
Print Assumptions robinson_q_not_lt_zero.
Print Assumptions robinson_q_lt_numeral_iff.
Print Assumptions robinson_q_r0_laws.
Print Assumptions robinson_q_numeral_lt_iff.
Print Assumptions robinson_q_numeral_add_one.
Print Assumptions robinson_q_numeral_lt_add.
Print Assumptions robinson_q_numeral_lt_succ.
Print Assumptions nat_robinson_q_laws.
Print Assumptions nat_standard_model_models_robinson_q.
Print Assumptions robinson_q_consistent.
Print Assumptions robinson_q_proof_complete.
Print Assumptions r0_weaker_than_robinson_q.
Print Assumptions robinson_q_add_zero_provable.
Print Assumptions r0_add_zero_unprovable.
Print Assumptions r0_strictly_weaker_than_robinson_q.
Check peano_minus_add_zero_sentence.
Check peano_minus_add_assoc_sentence.
Check peano_minus_add_comm_sentence.
Check peano_minus_add_eq_of_lt_sentence.
Check peano_minus_zero_le_sentence.
Check peano_minus_zero_lt_one_sentence.
Check peano_minus_one_le_of_zero_lt_sentence.
Check peano_minus_add_lt_add_sentence.
Check peano_minus_mul_zero_sentence.
Check peano_minus_mul_one_sentence.
Check peano_minus_mul_assoc_sentence.
Check peano_minus_mul_comm_sentence.
Check peano_minus_mul_lt_mul_sentence.
Check peano_minus_mul_add_distr_sentence.
Check peano_minus_lt_irrefl_sentence.
Check peano_minus_lt_trans_sentence.
Check peano_minus_lt_trichotomy_sentence.
Check peano_minus_axiom.
Check peano_minus_axiom_list.
Print Assumptions peano_minus_axiom_list_complete.
Print Assumptions peano_minus_axiom_finitely_covered.
Print Assumptions peano_minus_proves_equality.
Print Assumptions peano_minus_add_zero_realize_iff.
Print Assumptions peano_minus_add_assoc_realize_iff.
Print Assumptions peano_minus_add_comm_realize_iff.
Print Assumptions peano_minus_add_eq_of_lt_realize_iff.
Print Assumptions peano_minus_zero_le_realize_iff.
Print Assumptions peano_minus_zero_lt_one_realize_iff.
Print Assumptions peano_minus_one_le_of_zero_lt_realize_iff.
Print Assumptions peano_minus_add_lt_add_realize_iff.
Print Assumptions peano_minus_mul_zero_realize_iff.
Print Assumptions peano_minus_mul_one_realize_iff.
Print Assumptions peano_minus_mul_assoc_realize_iff.
Print Assumptions peano_minus_mul_comm_realize_iff.
Print Assumptions peano_minus_mul_lt_mul_realize_iff.
Print Assumptions peano_minus_mul_add_distr_realize_iff.
Print Assumptions peano_minus_lt_irrefl_realize_iff.
Print Assumptions peano_minus_lt_trans_realize_iff.
Print Assumptions peano_minus_lt_trichotomy_realize_iff.
Print Assumptions first_order_model_models_peano_minus_iff.
Print Assumptions nat_standard_model_models_peano_minus.
Print Assumptions peano_minus_consistent.
Print Assumptions peano_minus_proof_complete.
Print Assumptions robinson_q_weaker_than_peano_minus.
Print Assumptions r0_weaker_than_peano_minus.
Print Assumptions r0_strictly_weaker_than_peano_minus.
Print Assumptions peano_minus_zero_or_succ.
Print Assumptions peano_minus_lt_iff_exists_add_succ.
Print Assumptions peano_minus_robinson_q_laws.
Check omega_add_one_model.
Print Assumptions omega_add_one_model_models_robinson_q.
Check peano_minus_successor_nonfixed_sentence.
Print Assumptions peano_minus_successor_nonfixed_realize_iff.
Print Assumptions peano_minus_successor_nonfixed_provable.
Print Assumptions robinson_q_successor_nonfixed_unprovable.
Print Assumptions robinson_q_strictly_weaker_than_peano_minus.
Print Assumptions omega_add_one.
Print Assumptions omega_add_one_oring.
Print Assumptions omega_add_one_numeral.
Print Assumptions omega_add_one_robinson_q_laws.
Print Assumptions omega_add_one_r0_laws.
Print Assumptions omega_add_one_successor_fixed_point.
Print Assumptions omega_add_one_top_lt_top.
Print Assumptions omega_add_one_not_peano_minus.
Print Assumptions peano_minus_sub_spec_exists.
Print Assumptions peano_minus_sub_spec_functional.
Print Assumptions peano_minus_sub_spec_exists_unique.
Print Assumptions peano_minus_sub.
Print Assumptions peano_minus_sub_specification.
Print Assumptions peano_minus_sub_spec_of_ge.
Print Assumptions peano_minus_sub_spec_of_lt.
Print Assumptions peano_minus_sub_eq_iff.
Print Assumptions peano_minus_sub_le_self.
Print Assumptions peano_minus_sub_self.
Print Assumptions peano_minus_sub_of_le.
Print Assumptions peano_minus_sub_add_self_of_le.
Print Assumptions peano_minus_add_sub_self_of_le.
Print Assumptions peano_minus_add_sub_self.
Print Assumptions peano_minus_zero_sub.
Print Assumptions peano_minus_sub_zero.
Print Assumptions peano_minus_sub_remove_left.
Print Assumptions peano_minus_sub_sub.
Print Assumptions peano_minus_pred_lt_self_of_pos.
Print Assumptions peano_minus_sub_mul.
Print Assumptions peano_minus_mul_sub.
Print Assumptions peano_minus_add_sub_of_le.
Print Assumptions peano_minus_sub_succ_add_succ.
Print Assumptions peano_minus_le_sub_one_of_lt.
Print Assumptions peano_minus_sub_le_iff_right.
Print Assumptions peano_minus_sub_lt_iff_right.
Print Assumptions peano_minus_dvd.
Print Assumptions peano_minus_le_mul_self_of_pos_left.
Print Assumptions peano_minus_le_mul_self_of_pos_right.
Print Assumptions peano_minus_dvd_iff_bounded.
Print Assumptions peano_minus_le_of_dvd.
Print Assumptions peano_minus_not_dvd_of_lt.
Print Assumptions peano_minus_dvd_antisym.
Print Assumptions peano_minus_dvd_one_iff.
Print Assumptions peano_minus_is_prime.
Print Assumptions peano_minus_prime_gt_one.
Print Assumptions peano_minus_prime_pos.
Print Assumptions peano_minus_prime_divisor.
Print Assumptions peano_minus_one_not_prime.
Print Assumptions peano_minus_prime_ne_zero.
Print Assumptions peano_minus_prime_ne_one.
Print Assumptions peano_minus_pos_sub_iff_lt.
Print Assumptions peano_minus_sub_eq_zero_iff_le.
Print Assumptions peano_minus_min.
Print Assumptions peano_minus_max.
Print Assumptions peano_minus_min_of_le.
Print Assumptions peano_minus_min_of_ge.
Print Assumptions peano_minus_max_of_le.
Print Assumptions peano_minus_max_of_ge.
Print Assumptions peano_minus_min_graph_iff.
Print Assumptions peano_minus_max_graph_iff.
Print Assumptions peano_minus_min_le_left.
Print Assumptions peano_minus_min_le_right.
Print Assumptions peano_minus_le_max_left.
Print Assumptions peano_minus_le_max_right.
Print Assumptions arithmetic_sub_graph_var.
Print Assumptions arithmetic_sub_graph_formula.
Print Assumptions arithmetic_sub_graph_formula_open.
Print Assumptions arithmetic_sub_graph_formula_hierarchy.
Print Assumptions arithmetic_sub_graph_sorted.
Print Assumptions arithmetic_sub_graph_formula_eval.
Print Assumptions peano_minus_sub_defined.
Print Assumptions peano_minus_sub_definable_zero.
Print Assumptions peano_minus_sub_definable.
Print Assumptions peano_minus_sub_bounded.
Print Assumptions peano_minus_sub_definably_bounded.
Print Assumptions arithmetic_dvd_formula.
Print Assumptions arithmetic_dvd_formula_hierarchy.
Print Assumptions arithmetic_dvd_sorted.
Print Assumptions arithmetic_dvd_formula_eval.
Print Assumptions peano_minus_dvd_defined.
Print Assumptions peano_minus_dvd_definable_zero.
Print Assumptions peano_minus_dvd_definable.
Print Assumptions arithmetic_prime_divisor_body.
Print Assumptions arithmetic_prime_bound_formula.
Print Assumptions arithmetic_prime_formula.
Print Assumptions arithmetic_prime_formula_hierarchy.
Print Assumptions arithmetic_prime_sorted.
Print Assumptions arithmetic_prime_formula_eval.
Print Assumptions peano_minus_prime_defined.
Print Assumptions peano_minus_prime_definable_zero.
Print Assumptions peano_minus_prime_definable.
Print Assumptions arithmetic_min_graph_formula.
Print Assumptions arithmetic_max_graph_formula.
Print Assumptions arithmetic_min_graph_formula_open.
Print Assumptions arithmetic_max_graph_formula_open.
Print Assumptions arithmetic_min_graph_sorted.
Print Assumptions arithmetic_max_graph_sorted.
Print Assumptions arithmetic_min_graph_formula_eval.
Print Assumptions arithmetic_max_graph_formula_eval.
Print Assumptions peano_minus_min_defined.
Print Assumptions peano_minus_max_defined.
Print Assumptions peano_minus_min_definable_zero.
Print Assumptions peano_minus_max_definable_zero.
Print Assumptions peano_minus_min_definable.
Print Assumptions peano_minus_max_definable.
Print Assumptions peano_minus_min_bounded.
Print Assumptions peano_minus_max_bounded.
Print Assumptions peano_minus_min_definably_bounded.
Print Assumptions peano_minus_max_definably_bounded.
Print Assumptions arithmetic_sub_graph_instance.
Print Assumptions arithmetic_sub_predicate_instance.
Print Assumptions arithmetic_substitution_formula.
Print Assumptions arithmetic_substitution_formula_hierarchy.
Print Assumptions arithmetic_substitution_formula_eval.
Print Assumptions arithmetic_reverse_induction_formula.
Print Assumptions arithmetic_reverse_induction_formula_hierarchy.
Print Assumptions arithmetic_reverse_induction_formula_eval.
Print Assumptions first_order_axiom_scheme.
Print Assumptions arithmetic_zero_term.
Print Assumptions arithmetic_one_term.
Print Assumptions arithmetic_add_one_term.
Print Assumptions arithmetic_predicate_instance.
Print Assumptions arithmetic_successor_induction.
Print Assumptions arithmetic_order_induction.
Print Assumptions arithmetic_least_number.
Print Assumptions arithmetic_predicate_holds.
Print Assumptions arithmetic_predecessor_formula.
Print Assumptions arithmetic_predecessor_formula_hierarchy.
Print Assumptions arithmetic_zero_term_val.
Print Assumptions arithmetic_add_one_term_val.
Print Assumptions arithmetic_predicate_instance_eval.
Print Assumptions fin_env_cons_empty_eq_constant.
Print Assumptions arithmetic_all_predicate_eval.
Print Assumptions arithmetic_successor_step_eval.
Print Assumptions arithmetic_successor_induction_eval.
Print Assumptions arithmetic_bounded_all_eval.
Print Assumptions arithmetic_predecessors_eval.
Print Assumptions arithmetic_predecessor_formula_eval.
Print Assumptions arithmetic_order_step_eval.
Print Assumptions arithmetic_order_induction_eval.
Print Assumptions arithmetic_exists_predicate_eval.
Print Assumptions arithmetic_no_predecessors_eval.
Print Assumptions arithmetic_least_witness_eval.
Print Assumptions arithmetic_least_number_eval.
Print Assumptions first_order_axiom_scheme_subset.
Print Assumptions first_order_theory_union_subset_left.
Print Assumptions first_order_theory_union_subset_right.
Print Assumptions first_order_theory_weaker_than_union_left.
Print Assumptions first_order_theory_weaker_than_union_right.
Print Assumptions first_order_scheme_union_subset.
Print Assumptions first_order_scheme_union_weaker.
Print Assumptions arithmetic_induction_scheme.
Print Assumptions arithmetic_induction_scheme_subset.
Print Assumptions arithmetic_successor_induction_scheme.
Print Assumptions arithmetic_induction_theory.
Print Assumptions arithmetic_open_induction_theory.
Print Assumptions arithmetic_hierarchy_induction_theory.
Print Assumptions arithmetic_sigma_induction_theory.
Print Assumptions arithmetic_peano_theory.
Print Assumptions arithmetic_iopen.
Print Assumptions arithmetic_induction_on_hierarchy.
Print Assumptions arithmetic_isigma.
Print Assumptions arithmetic_ipi.
Print Assumptions first_order_peano_arithmetic.
Print Assumptions arithmetic_successor_induction_scheme_intro.
Print Assumptions arithmetic_successor_induction_scheme_subset.
Print Assumptions arithmetic_induction_theory_subset.
Print Assumptions arithmetic_induction_theory_weaker.
Print Assumptions arithmetic_sigma_induction_subset_mono.
Print Assumptions arithmetic_sigma_induction_weaker_mono.
Print Assumptions arithmetic_open_induction_subset_sigma_zero.
Print Assumptions arithmetic_open_induction_subset_hierarchy.
Print Assumptions arithmetic_sigma_induction_subset_peano.
Print Assumptions peano_minus_subset_iopen.
Print Assumptions peano_minus_weaker_than_iopen.
Print Assumptions arithmetic_iopen_subset_induction_on_hierarchy.
Print Assumptions arithmetic_iopen_weaker_than_induction_on_hierarchy.
Print Assumptions arithmetic_isigma_subset_mono.
Print Assumptions arithmetic_isigma_weaker_mono.
Print Assumptions arithmetic_iopen_subset_isigma_zero.
Print Assumptions arithmetic_iopen_weaker_than_isigma_zero.
Print Assumptions arithmetic_isigma_subset_peano.
Print Assumptions arithmetic_isigma_weaker_than_peano.
Print Assumptions arithmetic_isigma_zero_weaker_than_isigma_one.
Print Assumptions arithmetic_isigma_one_weaker_than_peano.
Print Assumptions arithmetic_induction_theory_proves_equality.
Print Assumptions arithmetic_induction_on_hierarchy_proves_equality.
Print Assumptions arithmetic_iopen_proves_equality.
Print Assumptions arithmetic_equality_weaker_than_induction_on_hierarchy.
Print Assumptions arithmetic_equality_weaker_than_iopen.
Print Assumptions semiformula_universal_closure_intro.
Print Assumptions semiformula_universal_closure_elim.
Print Assumptions arithmetic_models_successor_induction.
Print Assumptions arithmetic_model_predicate_representation.
Print Assumptions arithmetic_models_induction_theory_successor.
Print Assumptions arithmetic_models_hierarchy_negative_induction.
Print Assumptions arithmetic_models_hierarchy_scheme_alt.
Print Assumptions arithmetic_models_induction_on_hierarchy_alt.
Print Assumptions arithmetic_models_isigma_iff_ipi.
Print Assumptions arithmetic_models_hierarchy_successor_induction.
Print Assumptions arithmetic_models_hierarchy_order_induction.
Print Assumptions arithmetic_models_hierarchy_least_number.
Print Assumptions arithmetic_successor_induction_principle.
Print Assumptions arithmetic_order_induction_principle.
Print Assumptions arithmetic_least_number_principle.
Print Assumptions arithmetic_order_induction_of_successor.
Print Assumptions arithmetic_least_number_of_order_induction.
Print Assumptions arithmetic_least_number_of_successor_induction.
Print Assumptions arithmetic_boundary_of_least_number.
Print Assumptions nat_standard_model_realizes_successor_induction.
Print Assumptions nat_standard_model_models_successor_induction_scheme.
Print Assumptions nat_standard_model_models_induction_theory.
Print Assumptions nat_standard_model_models_iopen.
Print Assumptions nat_standard_model_models_induction_on_hierarchy.
Print Assumptions nat_standard_model_models_isigma.
Print Assumptions nat_standard_model_models_ipi.
Print Assumptions nat_standard_model_models_peano.
Print Assumptions arithmetic_induction_on_hierarchy_consistent.
Print Assumptions first_order_peano_arithmetic_consistent.
Print Assumptions first_order_peano_weaker_than_true_arithmetic.
Print Assumptions arithmetic_models_isigma_of_le.
Print Assumptions arithmetic_models_iopen_of_isigma_zero.
Print Assumptions arithmetic_models_peano_minus_of_iopen.
Print Assumptions r0_weaker_than_of_peano_minus.
Print Assumptions peano_minus_weaker_than_of_isigma_zero.
Print Assumptions peano_minus_weaker_than_of_isigma_one.
Print Assumptions peano_minus_weaker_than_of_peano.
Print Assumptions iopen_div_pos_spec.
Print Assumptions iopen_lt_mul_add_one.
Print Assumptions iopen_div_exists_unique_pos.
Print Assumptions iopen_div_spec.
Print Assumptions iopen_div_exists_unique.
Print Assumptions iopen_div.
Print Assumptions iopen_div_specification.
Print Assumptions iopen_mul_div_le_pos.
Print Assumptions iopen_lt_mul_div_succ.
Print Assumptions iopen_div_zero.
Print Assumptions iopen_eq_mul_div_add_of_pos.
Print Assumptions iopen_div_graph.
Print Assumptions arithmetic_iopen_div_graph_formula.
Print Assumptions arithmetic_iopen_div_graph_formula_open.
Print Assumptions arithmetic_iopen_div_graph_formula_hierarchy.
Print Assumptions arithmetic_iopen_div_graph_sorted.
Print Assumptions arithmetic_iopen_div_graph_formula_eval.
Print Assumptions arithmetic_iopen_div_defined.
Print Assumptions arithmetic_iopen_div_definable_zero.
Print Assumptions arithmetic_iopen_div_definable.
Print Assumptions arithmetic_iopen_div_bounded.
Print Assumptions arithmetic_iopen_div_definably_bounded.
Print Assumptions arithmetic_iopen_rem_definably_bounded.
Print Assumptions arithmetic_iopen_rem_bounded.
Print Assumptions arithmetic_iopen_rem_definable_zero.
Print Assumptions arithmetic_iopen_rem_definable.
Print Assumptions arithmetic_iopen_sqrt_graph_formula.
Print Assumptions arithmetic_iopen_sqrt_graph_formula_open.
Print Assumptions arithmetic_iopen_sqrt_graph_formula_hierarchy.
Print Assumptions arithmetic_iopen_sqrt_graph_sorted.
Print Assumptions arithmetic_iopen_sqrt_graph_formula_eval.
Print Assumptions arithmetic_iopen_sqrt_defined.
Print Assumptions arithmetic_iopen_sqrt_definable_zero.
Print Assumptions arithmetic_iopen_sqrt_definable.
Print Assumptions arithmetic_iopen_sqrt_bounded.
Print Assumptions arithmetic_iopen_sqrt_definably_bounded.
Print Assumptions arithmetic_iopen_pair_graph_formula.
Print Assumptions arithmetic_iopen_pair_graph_formula_open.
Print Assumptions arithmetic_iopen_pair_graph_formula_hierarchy.
Print Assumptions arithmetic_iopen_pair_graph_sorted.
Print Assumptions arithmetic_iopen_pair_graph_formula_eval.
Print Assumptions arithmetic_iopen_pair_defined.
Print Assumptions arithmetic_iopen_pair_definable_zero.
Print Assumptions arithmetic_iopen_pair_definable.
Print Assumptions arithmetic_iopen_pair_bounded.
Print Assumptions arithmetic_iopen_pair_definably_bounded.
Print Assumptions arithmetic_iopen_pi1_pair_instance.
Print Assumptions arithmetic_iopen_pi2_pair_instance.
Print Assumptions arithmetic_iopen_pi1_graph_formula.
Print Assumptions arithmetic_iopen_pi2_graph_formula.
Print Assumptions arithmetic_iopen_pi1_graph_formula_hierarchy.
Print Assumptions arithmetic_iopen_pi2_graph_formula_hierarchy.
Print Assumptions arithmetic_iopen_pi1_graph_sorted.
Print Assumptions arithmetic_iopen_pi2_graph_sorted.
Print Assumptions arithmetic_iopen_pi1_pair_env.
Print Assumptions arithmetic_iopen_pi2_pair_env.
Print Assumptions arithmetic_iopen_pi1_pair_instance_eval.
Print Assumptions arithmetic_iopen_pi2_pair_instance_eval.
Print Assumptions arithmetic_iopen_pi1_graph_formula_eval.
Print Assumptions arithmetic_iopen_pi2_graph_formula_eval.
Print Assumptions arithmetic_iopen_pi1_defined.
Print Assumptions arithmetic_iopen_pi2_defined.
Print Assumptions arithmetic_iopen_pi1_definable_zero.
Print Assumptions arithmetic_iopen_pi2_definable_zero.
Print Assumptions arithmetic_iopen_pi1_definable.
Print Assumptions arithmetic_iopen_pi2_definable.
Print Assumptions arithmetic_iopen_pi1_bounded.
Print Assumptions arithmetic_iopen_pi2_bounded.
Print Assumptions arithmetic_iopen_pi1_definably_bounded.
Print Assumptions arithmetic_iopen_pi2_definably_bounded.
Print Assumptions iopen_div_eq_of.
Print Assumptions iopen_div_mul_add.
Print Assumptions iopen_div_mul_add_left.
Print Assumptions iopen_zero_div.
Print Assumptions iopen_div_one.
Print Assumptions iopen_div_eq_zero_of_lt.
Print Assumptions iopen_mul_div_le.
Print Assumptions iopen_div_mul_left.
Print Assumptions iopen_div_mul_right.
Print Assumptions iopen_div_self.
Print Assumptions iopen_rem.
Print Assumptions iopen_rem_graph.
Print Assumptions iopen_div_add_rem.
Print Assumptions iopen_rem_zero.
Print Assumptions iopen_zero_rem.
Print Assumptions iopen_rem_mul_add_of_lt.
Print Assumptions iopen_rem_eq_self_of_lt.
Print Assumptions iopen_rem_lt.
Print Assumptions iopen_rem_le.
Print Assumptions iopen_rem_mul_self_left.
Print Assumptions iopen_rem_mul_self_right.
Print Assumptions iopen_rem_self.
Print Assumptions iopen_rem_eq_zero_iff_dvd.
Print Assumptions iopen_sqrt_spec.
Print Assumptions iopen_sqrt_exists_unique.
Print Assumptions iopen_sqrt.
Print Assumptions iopen_sqrt_specification.
Print Assumptions iopen_sqrt_graph.
Print Assumptions iopen_sqrt_eq_of.
Print Assumptions iopen_sqrt_square.
Print Assumptions iopen_sqrt_zero.
Print Assumptions iopen_sqrt_one.
Print Assumptions iopen_sqrt_square_le.
Print Assumptions iopen_sqrt_lt_square_succ.
Print Assumptions iopen_sqrt_le_self.
Print Assumptions iopen_sqrt_le_of_le_square.
Print Assumptions iopen_square_lt_of_lt_sqrt.
Print Assumptions iopen_sqrt_lt_self_of_one_lt.
Print Assumptions iopen_pair.
Print Assumptions iopen_pair_graph.
Print Assumptions iopen_unpair.
Print Assumptions iopen_pair_unpair.
Print Assumptions iopen_sqrt_pair_left.
Print Assumptions iopen_sqrt_pair_right.
Print Assumptions iopen_unpair_pair.
Print Assumptions iopen_pi1.
Print Assumptions iopen_pi2.
Print Assumptions iopen_pair_pi.
Print Assumptions iopen_pi1_pair.
Print Assumptions iopen_pi2_pair.
Print Assumptions iopen_pi1_le_self.
Print Assumptions iopen_pi2_le_self.
Print Assumptions iopen_le_pair_left.
Print Assumptions iopen_le_pair_right.
Print Assumptions iopen_pair_injective.
Print Assumptions iopen_pair_eq_iff.
Print Assumptions iopen_list_pair.
Print Assumptions iopen_list_unpair.
Print Assumptions iopen_list_unpair_length.
Print Assumptions iopen_list_unpair_pair.
Print Assumptions iopen_list_unpair_pair_nth.
Print Assumptions iopen_list_pair_injective_at_length.
Print Assumptions iopen_pair_lt_pair_left.
Print Assumptions iopen_pair_le_pair_left.
Print Assumptions iopen_pair_lt_pair_right.
Print Assumptions iopen_pair_le_pair_right.
Print Assumptions iopen_pair_le_pair.
Print Assumptions iopen_pair_lt_pair.
Print Assumptions iopen_pair_polybound.
Print Assumptions iopen_div_le.
Print Assumptions iopen_div_monotone.
Print Assumptions iopen_div_lt_of_lt_mul.
Print Assumptions iopen_div_mul.
Print Assumptions iopen_div_cancel_left.
Print Assumptions iopen_div_cancel_right.
Print Assumptions iopen_div_add_mul_self.
Print Assumptions iopen_div_add_mul_self_left.
Print Assumptions iopen_div_mul_add_self.
Print Assumptions iopen_div_mul_add_self_left.
Print Assumptions iopen_rem_eq_of_decomposition.
Print Assumptions iopen_rem_add_mul_self.
Print Assumptions iopen_rem_add_mul_self_left.
Print Assumptions iopen_rem_mul_add_self.
Print Assumptions iopen_rem_mul_add_self_left.
Print Assumptions iopen_rem_add_remove_right.
Print Assumptions iopen_rem_add_remove_left.
Print Assumptions iopen_rem_div.
Print Assumptions iopen_rem_one.
Print Assumptions iopen_rem_add_congr_left.
Print Assumptions iopen_rem_add_congr_right.
Print Assumptions iopen_rem_add.
Print Assumptions iopen_rem_mul_congr_left.
Print Assumptions iopen_rem_mul_congr_right.
Print Assumptions iopen_rem_mul.
Print Assumptions iopen_rem_two.
Print Assumptions iopen_even_or_odd.
Print Assumptions iopen_even_or_odd_exact.
Print Assumptions iopen_two_dvd_mul.
Print Assumptions iopen_mul_div_self_iff_dvd.
Print Assumptions iopen_div_lt_of_pos_of_one_lt.
Print Assumptions iopen_rem_add_remove_right_of_dvd.
Print Assumptions iopen_rem_add_remove_left_of_dvd.
Print Assumptions iopen_le_two_mul_div_two_add_one.
Print Assumptions iopen_sqrt_eq_of_le_of_le.
Print Assumptions iopen_sqrt_numeral_eq.
Print Assumptions iopen_sqrt_two.
Print Assumptions iopen_sqrt_three.
Print Assumptions iopen_sqrt_four.
Print Assumptions iopen_two_ne_square.
Print Assumptions iopen_sqrt_le_add.
Print Assumptions iopen_lt_pair_left_of_pos.
Print Assumptions iopen_two_prime.
Print Assumptions iopen_polynomial_induction.
Print Assumptions peano_minus_ball_lt_succ.
Print Assumptions peano_minus_bex_lt_succ.
Print Assumptions peano_minus_eval_ball_lt_succ.
Print Assumptions peano_minus_eval_bex_lt_succ.
Print Assumptions nat_peano_minus_laws.
Print Assumptions arithmetic_peano_minus_majorant_lift.
Print Assumptions arithmetic_peano_minus_majorant_lift_spec.
Print Assumptions arithmetic_sorted_definable_substitution_peano_minus.
Print Assumptions arithmetic_sorted_definable_function_substitution_peano_minus.
Print Assumptions arithmetic_definably_bounded_compose_peano_minus.
Print Assumptions first_order_true_arithmetic_models.
Print Assumptions first_order_true_arithmetic_provable_iff.
Print Assumptions arithmetic_theory_weaker_than_true_arithmetic.
Print Assumptions semiterm_val_monotone.
Print Assumptions semiterm_val_monotone_free.
Print Assumptions semiterm_val_monotone_bound.
Print Assumptions semiformula_polarity_neg.
Print Assumptions semiformula_polarity_imp.
Print Assumptions semiformula_and_positive_iff.
Print Assumptions semiformula_or_negative_iff.
Print Assumptions semiformula_neg_positive_iff.
Print Assumptions semiformula_polarity_rewrite.
Print Assumptions first_order_eqv_equivalence.
Print Assumptions first_order_models_equality_axioms_of_interprets_eq.
Print Assumptions semiterm_val_eqv.
Print Assumptions semiformula_eval_eqv.
Print Assumptions first_order_sequent_language_map_shift.
Print Assumptions first_order_derivation_language_map.
Print Assumptions first_order_lk_provable_language_map.
Print Assumptions first_order_sequent_rewrite_under_free_shift.
Print Assumptions first_order_derivation_rewrite.
Print Assumptions first_order_derivation_map.
Print Assumptions first_order_derivation_shift.
Print Assumptions semiformula_rewrite_map_substitute_fresh.
Print Assumptions semiformula_rewrite_map_fresh_eq_shift.
Print Assumptions first_order_sequent_rewrite_map_fresh_eq_shift.
Print Assumptions first_order_derivation_generalize_fresh.
Print Assumptions first_order_sequent_fv_sup_le_new_variable.
Print Assumptions first_order_sequent_new_variable_fresh.
Print Assumptions first_order_derivation_all_new_variable.
Print Assumptions first_order_derivation_exists_of_instances.
Print Assumptions first_order_derivation_exists_of_instances_present.
Print Assumptions first_order_is_cut_free_or_iff.
Print Assumptions first_order_is_cut_free_and_iff.
Print Assumptions first_order_is_cut_free_all_iff.
Print Assumptions first_order_is_cut_free_exists_iff.
Print Assumptions first_order_is_cut_free_contraction_iff.
Print Assumptions first_order_is_cut_free_cast_iff.
Print Assumptions first_order_is_cut_free_root_is_not_cut.
Print Assumptions first_order_is_cut_free_not_cut.
Print Assumptions first_order_is_cut_free_language_map_iff.
Print Assumptions first_order_is_cut_free_rewrite_iff.
Print Assumptions first_order_is_cut_free_map_iff.
Print Assumptions first_order_is_cut_free_shift_iff.
Print Assumptions first_order_is_cut_free_generalize_fresh_iff.
Print Assumptions first_order_is_cut_free_exists_of_instances_iff.
Print Assumptions first_order_is_cut_free_exists_of_instances_present_iff.
Print Assumptions first_order_is_cut_free_all_new_variable_iff.
Print Assumptions fin_env_snoc_empty_eq_cons.
Print Assumptions first_order_shifted_context_true.
Print Assumptions first_order_derivation_sound.
Print Assumptions first_order_derivation_nil_empty.
Print Assumptions first_order_sentence_embed_eval.
Print Assumptions first_order_lk_sound.
Print Assumptions first_order_theory_proof_sound.
Print Assumptions first_order_theory_consistent_of_satisfiable.
Print Assumptions first_order_models_of_weaker_theory.
Print Assumptions semiterm_bvar_or_fvar_relational.
Print Assumptions term_fvar_relational.
Print Assumptions semiterm_relational_val_rew.
Print Assumptions semiterm_relational_val_bshift.
Check first_order_positive_derivation_graft_cut_free.
Check first_order_stronger_than.
Print Assumptions first_order_stronger_than_refl.
Print Assumptions first_order_stronger_than_trans.
Print Assumptions first_order_stronger_than_of_subset.
Check first_order_sequent_meet.
Print Assumptions first_order_stronger_than_meet_left.
Print Assumptions first_order_stronger_than_meet_right.
Print Assumptions first_order_stronger_than_and.
Print Assumptions first_order_stronger_than_and_left.
Print Assumptions first_order_stronger_than_and_right.
Print Assumptions first_order_stronger_than_all.
Print Assumptions first_order_stronger_than_meet.
Print Assumptions first_order_stronger_than_meet_with_right.
Check first_order_canonical_forces_aux.
Check first_order_canonical_forces.
Check first_order_canonical_forces_all.
Print Assumptions first_order_canonical_forces_monotone_aux.
Print Assumptions first_order_canonical_forces_monotone.
Check first_order_type_biequivalence.
Print Assumptions first_order_rew_apply_bind_comp.
Print Assumptions first_order_rew_apply_bind_bshift.
Print Assumptions first_order_rew_q_bind_bound.
Print Assumptions first_order_rew_q_bind_free.
Print Assumptions first_order_canonical_forces_rewrite.
Print Assumptions first_order_rew_apply_bind_identity.
Print Assumptions first_order_canonical_forces_substitute.
Print Assumptions first_order_canonical_forces_substitute_one.
Print Assumptions first_order_canonical_forces_bshift.
Print Assumptions ifo_rewrite_free_identity_cons.
Print Assumptions first_order_canonical_imply_of_aux.
Print Assumptions first_order_canonical_imply_of.
Print Assumptions first_order_canonical_forces_explosion_aux.
Print Assumptions first_order_canonical_forces_explosion.
Print Assumptions first_order_canonical_efq.
Print Assumptions first_order_canonical_modus_ponens.
Print Assumptions first_order_canonical_minimal_sound_bounded.
Print Assumptions first_order_canonical_minimal_sound.
Check first_order_canonical_forces_cast.
Print Assumptions first_order_canonical_rel_refl.
Print Assumptions first_order_canonical_reflect_verum.
Print Assumptions first_order_canonical_reflect_falsum.
Print Assumptions first_order_canonical_reflect_rel.
Print Assumptions first_order_canonical_reflect_nrel.
Print Assumptions first_order_canonical_reflect_and.
Print Assumptions first_order_canonical_reflect_or.
Print Assumptions first_order_canonical_reflect_all.
Print Assumptions first_order_canonical_reflect_exists.
Print Assumptions first_order_canonical_forces_conj_nonempty.
Print Assumptions first_order_canonical_forces_conj.
Print Assumptions first_order_canonical_forces_translated_conj_nonempty.
Print Assumptions first_order_canonical_forces_translated_conj.
Check first_order_semiformula_view.
Check first_order_semiformula_view_of.
Print Assumptions first_order_canonical_reflection_bounded.
Print Assumptions first_order_canonical_reflection.
Print Assumptions first_order_sequent_neg_involutive.
Print Assumptions ifo_generic_list_conj2_eq.
Print Assumptions first_order_hauptsatz.
Check first_order_canonical_world.
Check first_order_canonical_world_order.
Print Assumptions first_order_canonical_world_nil.
Print Assumptions first_order_canonical_world_le_nil.
Print Assumptions first_order_canonical_world_of_unprovable.
Check first_order_canonical_is_forced.
Check first_order_canonical_forcing_relation.
Check first_order_canonical_is_weakly_forced.
Check first_order_canonical_weak_forcing_relation.
Print Assumptions first_order_canonical_is_weakly_forced_iff_is_forced.
Print Assumptions first_order_canonical_is_weakly_forced_cast.
Print Assumptions first_order_inhabited_forall_choice.
Print Assumptions first_order_canonical_is_forced_rel.
Print Assumptions first_order_canonical_is_forced_all.
Print Assumptions first_order_canonical_is_forced_and.
Print Assumptions first_order_canonical_is_forced_or.
Print Assumptions first_order_canonical_is_forced_not_falsum.
Print Assumptions first_order_canonical_is_forced_exists.
Print Assumptions first_order_canonical_is_forced_monotone.
Print Assumptions first_order_canonical_is_forced_imp.
Print Assumptions first_order_canonical_is_forced_neg.
Print Assumptions first_order_canonical_minimal_sound_global.
Check first_order_canonical_int_kripke.
Print Assumptions first_order_canonical_is_forced_cast.
Print Assumptions first_order_canonical_weak_neg_translation.
Print Assumptions first_order_canonical_is_weakly_forced_verum.
Print Assumptions first_order_canonical_is_weakly_forced_falsum.
Print Assumptions first_order_canonical_is_weakly_forced_not.
Print Assumptions first_order_canonical_is_weakly_forced_and.
Print Assumptions first_order_canonical_is_weakly_forced_all.
Print Assumptions first_order_canonical_is_weakly_forced_monotone.
Print Assumptions first_order_canonical_is_weakly_forced_generic.
Print Assumptions first_order_canonical_is_weakly_forced_or.
Print Assumptions first_order_canonical_is_weakly_forced_exists.
Print Assumptions first_order_canonical_weak_neg_extension.
Print Assumptions first_order_canonical_is_weakly_forced_imp.
Check first_order_canonical_classical_kripke.
Print Assumptions first_order_canonical_weak_completeness.
Print Assumptions first_order_canonical_weak_reflection.
Check language_sublanguage.
Check language_sublanguage_unsub.
Print Assumptions language_sublanguage_unsub_func.
Print Assumptions language_sublanguage_unsub_rel.
Check language_hom_injective.
Print Assumptions language_sublanguage_unsub_injective.
Check indexed_singleton.
Print Assumptions indexed_singleton_same.
Check semiterm_function_symbols.
Print Assumptions semiterm_function_symbols_root.
Print Assumptions semiterm_function_symbols_child.
Check semiterm_to_sublanguage.
Print Assumptions semiterm_language_map_to_sublanguage.
Check semiformula_function_symbols.
Check semiformula_relation_symbols.
Print Assumptions semiformula_function_symbols_atom.
Print Assumptions semiformula_relation_symbols_rel.
Print Assumptions semiformula_relation_symbols_nrel.
Check semiformula_to_sublanguage.
Print Assumptions semiformula_language_map_to_sublanguage.
Check semiformula_predicate_sublanguage.
Check semiformula_to_predicate_sublanguage.
Print Assumptions semiformula_language_map_to_predicate_sublanguage.
Print Assumptions list_index_lt_length.
Check list_member_position.
Print Assumptions fin_to_nat_FS_value.
Print Assumptions chain_list_index_nth.
Print Assumptions chain_list_index_member_position.
Print Assumptions nth_error_list_index.
Check list_member_decode.
Print Assumptions sig_prop_ext.
Check list_member_encoding.
Check semiformula_predicate_sublanguage_encodable.
Check semiformula_sublanguage.
Check semiformula_sublanguage_unsub.
Check semiformula_sublanguage_number.
Check semiformula_to_own_sublanguage.
Print Assumptions semiformula_language_map_to_own_sublanguage.
Check fin_encoding.
Check semiformula_sublanguage_encodable.
Check language_sublanguage_decidable_eq.
Check semiformula_sublanguage_decidable_eq.
Check first_order_structure_extend.
Print Assumptions first_order_structure_extend_func.
Print Assumptions first_order_structure_extend_rel.
Print Assumptions semiterm_val_language_map_extend.
Print Assumptions semiformula_eval_language_map_extend.
Check first_order_model_extend.
Print Assumptions first_order_model_extend_realize_language_map.
Print Assumptions first_order_consequence_language_map_iff_injective.
Print Assumptions first_order_satisfiable_language_map.
Print Assumptions first_order_lk_provable_em.
Check first_order_decidable_points.
Print Assumptions first_order_decidable_points_member.
Check first_order_henkin_points.
Print Assumptions first_order_henkin_points_member.
Check first_order_dense_requirements.
Check nat_encoding.
Check encoding_enumerate.
Print Assumptions encoding_enumerate_encode.
Check first_order_dense_requirement_enum.
Print Assumptions first_order_dense_requirement_enum_member.
Print Assumptions first_order_dense_requirements_countable.
Print Assumptions first_order_exists_generic_pfilter.
Check first_order_generic_pfilter.
Print Assumptions first_order_generic_pfilter_generic.
Print Assumptions first_order_generic_pfilter_contains.
Check first_order_generic_forces.
Print Assumptions first_order_generic_forces_cast.
Print Assumptions first_order_generic_forces_em.
Print Assumptions first_order_generic_forces_neg.
Print Assumptions first_order_generic_forces_verum.
Print Assumptions first_order_generic_forces_not_falsum.
Print Assumptions first_order_generic_forces_nrel.
Print Assumptions first_order_generic_forces_henkin.
Print Assumptions first_order_generic_forces_exists.
Print Assumptions first_order_generic_forces_all.
Print Assumptions first_order_generic_forces_and.
Print Assumptions first_order_generic_forces_or.
Check first_order_generic_term_structure.
Print Assumptions first_order_generic_term_structure_func.
Print Assumptions first_order_generic_term_structure_rel.
Print Assumptions first_order_generic_term_val.
Print Assumptions rew_substitute_q_bind.
Print Assumptions semiformula_substitute_q_bind.
Print Assumptions first_order_generic_forcing_lemma.
Print Assumptions semiformula_rewrite_bind_identity.
Print Assumptions first_order_generic_reflection.
Check classical_language_decidable_eq.
Print Assumptions first_order_satisfiable_of_irrefutable.
Check set_intersection.
Check set_union.
Check set_complement.
Check set_universal.
Check set_void.
Check set_filter.
Check filter_included.
Print Assumptions set_filter_maximal_extension.
Print Assumptions maximal_filter_decides.
Check set_ultrafilter.
Check ultrafilter_as_filter.
Print Assumptions set_ultrafilter_extension.
Check set_list_intersection.
Print Assumptions set_list_intersection_member_iff.
Check set_family_finite_intersection_property.
Print Assumptions family_generated_filter.
Print Assumptions ultrafilter_of_finite_intersection_property.
Print Assumptions ultrafilter_member_equiv.
Print Assumptions ultrafilter_intersection_mem.
Print Assumptions ultrafilter_member_intersection_left.
Print Assumptions ultrafilter_member_intersection_right.
Print Assumptions ultrafilter_member_decides.
Check first_order_ultraproduct.
Print Assumptions first_order_ultraproduct_ext.
Check first_order_ultraproduct_structure.
Print Assumptions first_order_ultraproduct_structure_func.
Print Assumptions first_order_ultraproduct_structure_rel.
Check first_order_ultraproduct_inhabited.
Print Assumptions first_order_ultraproduct_term_value.
Print Assumptions first_order_ultraproduct_term_value_eq.
Print Assumptions first_order_ultraproduct_fin_env_cons.
Print Assumptions first_order_ultraproduct_formula_eval.
Print Assumptions first_order_ultraproduct_formula_realize.
Print Assumptions first_order_ultraproduct_sentence_realize.
Check first_order_ultraproduct_model.
Print Assumptions first_order_ultraproduct_model_realize.
Check first_order_finite_subtheory.
Check finite_subtheory_theory.
Check first_order_sentence_domain.
Print Assumptions first_order_sentence_domains_fip.
Print Assumptions first_order_ultrafilter_exists.
Print Assumptions first_order_compactness_aux.
Print Assumptions first_order_compactness.
Print Assumptions first_order_model_realize_list_conj2.
Print Assumptions first_order_raw_list_member_in.
Check first_order_theory_explosion.
Print Assumptions first_order_satisfiable_of_consistent.
Print Assumptions first_order_satisfiable_iff_consistent.
Print Assumptions first_order_theory_proof_complete.
Print Assumptions first_order_theory_proof_complete_iff.
Print Assumptions first_order_theory_proof_complete_on_model_class.
Check equivalence_class_carrier.
Check equivalence_class_mk.
Check equivalence_class_repr.
Print Assumptions equivalence_class_repr_spec.
Print Assumptions equivalence_class_repr_mk_related.
Print Assumptions equivalence_class_mk_repr.
Print Assumptions equivalence_class_mk_eq_iff.
Check equivalence_class_quotient.
Check first_order_eq_quotient.
Check first_order_eq_quotient_carrier.
Check first_order_eq_quotient_structure.
Print Assumptions first_order_eq_quotient_func_mk.
Print Assumptions first_order_eq_quotient_rel_mk.
Print Assumptions first_order_eq_quotient_term_value.
Print Assumptions first_order_eq_quotient_fin_env_cons.
Print Assumptions first_order_eq_quotient_formula_eval.
Print Assumptions first_order_eq_quotient_eq_iff.
Print Assumptions first_order_eq_quotient_interprets_eq.
Check first_order_eq_quotient_model.
Print Assumptions first_order_eq_quotient_model_interprets_eq.
Print Assumptions first_order_eq_empty_bound_env_quotient.
Print Assumptions first_order_eq_empty_free_env_quotient.
Print Assumptions first_order_eq_quotient_elementary_equiv.
Print Assumptions first_order_eq_quotient_models_theory.
Print Assumptions first_order_theory_proof_complete_on_eq_models.
Check matrix_iget.
Print Assumptions matrix_iget_in_range.
Check first_order_eq_atom.
Check first_order_eq_refl_sentence.
Check first_order_eq_symm_sentence.
Check first_order_eq_trans_sentence.
Check first_order_eq_func_ext_sentence.
Check first_order_eq_rel_ext_sentence.
Check first_order_equality_axiom.
Check first_order_equality_axiom_list.
Print Assumptions first_order_equality_axiom_list_complete.
Print Assumptions first_order_equality_axiom_finitely_covered.
Print Assumptions first_order_eq_atom_eval.
Print Assumptions first_order_eq_pair_conjunction_eval.
Print Assumptions first_order_eq_refl_realize_iff.
Print Assumptions first_order_eq_symm_realize_iff.
Print Assumptions first_order_eq_trans_realize_iff.
Print Assumptions first_order_eq_func_ext_realize_iff.
Print Assumptions first_order_eq_rel_ext_realize_iff.
Check first_order_structure_models_equality_theory.
Print Assumptions first_order_structure_models_equality_theory_iff.
Print Assumptions first_order_model_models_equality_theory_iff.
Print Assumptions first_order_model_models_equality_theory_of_interprets_eq.
Check first_order_theory_proves_equality.
Check first_order_theory_models_equality.
Print Assumptions first_order_theory_models_equality_of_proves.
Print Assumptions first_order_consequence_on_eq_models_iff.
Print Assumptions first_order_consequence_on_eq_models_of_proves_iff.
Print Assumptions first_order_satisfiable_on_eq_models_iff.
Print Assumptions first_order_satisfiable_on_eq_models_of_proves_iff.
Check first_order_exists_unique_reindex.
Check first_order_exists_unique.
Print Assumptions first_order_exists_unique_reindex_env.
Print Assumptions first_order_exists_unique_eval.
Print Assumptions first_order_theory_proof_complete_on_eq_models_of_proves.
Check first_order_order_le_operator.
Print Assumptions first_order_order_le_apply.
Check first_order_order_le_atom.
Check first_order_order_eq_or_lt_atom.
Print Assumptions first_order_order_le_atom_eq.
Check first_order_order_le_iff_sentence.
Print Assumptions first_order_order_le_iff_sentence_realize.
Print Assumptions first_order_order_le_iff_provable.
Print Assumptions first_order_order_complete.
Check second_order_semiformula.
Check second_order_formula.
Check second_order_semisentence.
Check second_order_sentence.
Check second_order_semiproposition.
Check second_order_proposition.
Check second_order_semiformula_rect.
Check second_order_semiformula_ind.
Check second_order_neg.
Check second_order_imp.
Check second_order_iff.
Print Assumptions second_order_neg_rel.
Print Assumptions second_order_neg_nrel.
Print Assumptions second_order_neg_bpred.
Print Assumptions second_order_neg_nbpred.
Print Assumptions second_order_neg_fpred.
Print Assumptions second_order_neg_nfpred.
Print Assumptions second_order_neg_verum.
Print Assumptions second_order_neg_falsum.
Print Assumptions second_order_neg_and.
Print Assumptions second_order_neg_or.
Print Assumptions second_order_neg_all0.
Print Assumptions second_order_neg_exs0.
Print Assumptions second_order_neg_all1.
Print Assumptions second_order_neg_exs1.
Print Assumptions second_order_neg_involutive.
Print Assumptions second_order_neg_injective.
Check second_order_and_left.
Check second_order_and_right.
Check second_order_or_left.
Check second_order_or_right.
Check second_order_all0_body.
Check second_order_exs0_body.
Check second_order_all1_body.
Check second_order_exs1_body.
Print Assumptions second_order_and_injective.
Print Assumptions second_order_or_injective.
Print Assumptions second_order_all0_injective.
Print Assumptions second_order_exs0_injective.
Print Assumptions second_order_all1_injective.
Print Assumptions second_order_exs1_injective.
Check second_order_complexity.
Print Assumptions second_order_complexity_rel.
Print Assumptions second_order_complexity_nrel.
Print Assumptions second_order_complexity_bpred.
Print Assumptions second_order_complexity_nbpred.
Print Assumptions second_order_complexity_fpred.
Print Assumptions second_order_complexity_nfpred.
Print Assumptions second_order_complexity_verum.
Print Assumptions second_order_complexity_falsum.
Print Assumptions second_order_complexity_and.
Print Assumptions second_order_complexity_or.
Print Assumptions second_order_complexity_all0.
Print Assumptions second_order_complexity_exs0.
Print Assumptions second_order_complexity_all1.
Print Assumptions second_order_complexity_exs1.
Print Assumptions second_order_complexity_neg.
Check fin_retrusion.
Print Assumptions fin_retrusion_zero.
Print Assumptions fin_retrusion_succ.
Print Assumptions fin_retrusion_comp_succ.
Print Assumptions fin_retrusion_id.
Print Assumptions fin_retrusion_comp.
Check second_order_rewrite_terms_aux.
Check second_order_rewrite_terms.
Print Assumptions second_order_rewrite_terms_equiv.
Print Assumptions second_order_rewrite_terms_neg.
Print Assumptions second_order_rewrite_terms_id.
Print Assumptions second_order_rewrite_terms_comp.
Check second_order_bmap_aux.
Check second_order_bmap.
Print Assumptions second_order_bmap_neg.
Print Assumptions second_order_bmap_id.
Print Assumptions second_order_bmap_comp.
Print Assumptions second_order_bmap_rewrite_terms.
Print Assumptions second_order_rewrite_terms_comp2.
Check second_order_instantiate.
Print Assumptions second_order_instantiate_neg.
Print Assumptions second_order_instantiate_rewrite.
Check second_order_predicate_rew.
Check second_order_predicate_rew_q.
Print Assumptions second_order_predicate_rew_q_bound_zero.
Print Assumptions second_order_predicate_rew_q_bound_succ.
Print Assumptions second_order_predicate_rew_q_free.
Check second_order_predicate_rew_app_aux.
Check second_order_predicate_rew_app.
Check second_order_predicate_rew_equiv.
Print Assumptions second_order_predicate_rew_q_equiv.
Print Assumptions second_order_predicate_rew_app_equiv.
Print Assumptions second_order_predicate_rew_app_neg.
Print Assumptions rew_q_fixes_free.
Print Assumptions second_order_predicate_rew_app_rewrite_terms.
Print Assumptions second_order_predicate_rew_app_subst.
Check second_order_predicate_rew_id.
Print Assumptions second_order_predicate_rew_q_id_equiv.
Print Assumptions second_order_predicate_rew_app_id.
Check second_order_predicate_rew_bLeft.
Print Assumptions second_order_predicate_rew_bLeft_q_equiv.
Print Assumptions second_order_predicate_rew_app_bmap.
Check second_order_predicate_rew_bRight.
Print Assumptions second_order_predicate_rew_bRight_q_equiv.
Print Assumptions second_order_predicate_rew_bmap_app.
Print Assumptions second_order_predicate_rew_q_bRight_succ.
Check second_order_predicate_rew_comp.
Print Assumptions second_order_predicate_rew_q_comp_equiv.
Print Assumptions second_order_predicate_rew_app_comp.
Print Assumptions second_order_instantiate_bvar.
Print Assumptions second_order_predicate_rew_comp_id_left.
Print Assumptions second_order_predicate_rew_comp_id_right.
Check second_order_predicate_rew_map.
Check second_order_predicate_rew_rename.
Print Assumptions second_order_predicate_rew_q_rename_equiv.
Check second_order_predicate_rew_shift.
Print Assumptions second_order_predicate_rew_q_shift_equiv.
Check second_order_predicate_rew_free_last.
Print Assumptions second_order_predicate_rew_free_last_old.
Print Assumptions second_order_predicate_rew_free_last_new.
Print Assumptions second_order_predicate_rew_free_last_free.
Print Assumptions second_order_predicate_rew_q_free_last_equiv.
Check second_order_predicate_rew_emb.
Print Assumptions second_order_predicate_rew_q_emb_equiv.
Check second_order_predicate_rew_subst.
Check second_order_predicate_subst_q_family.
Print Assumptions second_order_predicate_rew_q_subst_equiv.
Check second_order_substitute_predicates.
Check second_order_semiproposition_free_individual.
Check second_order_semiproposition_shift_individual.
Check second_order_semiproposition_free_predicate.
Check second_order_semiproposition_shift_predicate.
Check second_order_semiproposition_substitute_predicates.
Check second_order_semisentence_embed.
Check second_order_eval_aux.
Check second_order_eval.
Print Assumptions second_order_eval_rel.
Print Assumptions second_order_eval_nrel.
Print Assumptions second_order_eval_bpred.
Print Assumptions second_order_eval_nbpred.
Print Assumptions second_order_eval_fpred.
Print Assumptions second_order_eval_nfpred.
Print Assumptions second_order_eval_verum.
Print Assumptions second_order_eval_falsum.
Print Assumptions second_order_eval_and.
Print Assumptions second_order_eval_or.
Print Assumptions second_order_eval_all0.
Print Assumptions second_order_eval_exs0.
Print Assumptions second_order_eval_all1.
Print Assumptions second_order_eval_exs1.
Print Assumptions classical_not_forall_iff_exists_not.
Print Assumptions classical_not_guarded_all_iff.
Print Assumptions second_order_eval_neg.
Print Assumptions second_order_eval_imp.
Print Assumptions second_order_eval_iff.
Check second_order_model.
Check second_order_model_of.
Check second_order_model_realize.
Print Assumptions second_order_model_of_realize.
Print Assumptions second_order_model_realize_verum.
Print Assumptions second_order_model_realize_falsum.
Print Assumptions second_order_model_realize_neg.
Print Assumptions second_order_model_realize_and.
Print Assumptions second_order_model_realize_or.
Print Assumptions second_order_model_realize_imp.
Print Assumptions second_order_model_realize_iff.
Check second_order_sequent.
Check second_order_sequent_shift_individual.
Print Assumptions second_order_sequent_shift_individual_nil.
Print Assumptions second_order_sequent_shift_individual_cons.
Check second_order_sequent_shift_predicate.
Print Assumptions second_order_sequent_shift_predicate_nil.
Print Assumptions second_order_sequent_shift_predicate_cons.
Check second_order_sequent_neg.
Print Assumptions second_order_sequent_neg_nil.
Print Assumptions second_order_sequent_neg_cons.
Check second_order_lk_derivation.
Check SO_LK_identity.
Check SO_LK_cut.
Check SO_LK_weakening.
Check SO_LK_verum.
Check SO_LK_and.
Check SO_LK_or.
Check SO_LK_all_individual.
Check SO_LK_exists_individual.
Check SO_LK_all_predicate.
Check SO_LK_exists_predicate.
Check second_order_lk_derivation_cast.
Check second_order_sentence_as_proposition.
Check second_order_lk_proof.
Check second_order_schema.
Check second_order_schema_derivation.
Check second_order_schema_provable.
Check second_order_theory.
Check second_order_theory_provable.
Print Assumptions second_order_theory_provable_iff.
Check second_order_schema_theory.
Print Assumptions second_order_schema_theory_provable_iff.
Check pa_provability.
Check pa_hbl2.
Check pa_hbl3.
Check pa_hbl.
Check pa_mono.
Check pa_ext.
Check pa_rosser.
Check pa_formalized_complete_on.
Check pa_kreisel.
Check pa_sound_on.
Print Assumptions pa_syntactical_sound.
Print Assumptions pa_hbl3_of_formalized_complete.
Print Assumptions pa_mono_of_hbl2.
Print Assumptions pa_ext_of_hbl2.
Print Assumptions pa_bew_distribute_imply.
Print Assumptions pa_bew_distribute_and.
Print Assumptions pa_bew_distribute_and_provable.
Print Assumptions pa_bew_collect_and.
Print Assumptions pa_dia_mono.
Print Assumptions pa_mono_weaker.
Print Assumptions pa_ext_weaker.
Check pa_diagonalization.
Check pa_godel.
Print Assumptions pa_godel_spec.
Print Assumptions pa_strictly_weaker_of_unprovable.
Print Assumptions pa_unprovable_godel.
Print Assumptions pa_unrefutable_godel.
Print Assumptions pa_godel_independent.
Print Assumptions pa_first_incompleteness.
Print Assumptions pa_formalized_consistent_of_unprovable.
Print Assumptions pa_formalized_unprovable_godel.
Print Assumptions pa_godel_iff_con.
Print Assumptions pa_con_unprovable.
Print Assumptions pa_con_unrefutable.
Print Assumptions pa_con_independent.
Check pa_kreisel_sentence.
Print Assumptions pa_kreisel_spec.
Print Assumptions pa_lob_theorem.
Print Assumptions pa_formalized_lob_theorem.
Print Assumptions pa_formalized_unprovable_not_con.
Print Assumptions pa_formalized_unrefutable_godel.
Print Assumptions pa_unrefutable_rosser.
Print Assumptions pa_rosser_independent.
Print Assumptions pa_rosser_first_incompleteness.
Print Assumptions pa_kreisel_remark.
Check pa_refutability.
Print Assumptions pa_R1.
Print Assumptions pa_R1_weaker.
Check pa_jeroslow.
Print Assumptions pa_jeroslow_spec.
Print Assumptions pa_jeroslow_spec_weaker.
Check pa_refutability_sound_on.
Print Assumptions pa_unprovable_jeroslow.
Check pa_safe.
Check pa_formalized_noncontradiction.
Print Assumptions pa_jeroslow_not_safe.
Print Assumptions pa_unprovable_flon.
Check pa_iter.
Check pa_dia_iter.
Print Assumptions pa_iter_add.
Print Assumptions pa_neg_iterated_prov.
Print Assumptions pa_iterated_bottom_step.
Print Assumptions pa_box_bottom_monotone.
Print Assumptions pa_iterated_bottom_unprovable.
Check pa_height.
Print Assumptions pa_height_eq_top_iff.
Print Assumptions pa_height_le_of_iterated_bottom.
Print Assumptions pa_height_lt_pos_of_base_iterated_bottom.
Print Assumptions pa_height_le_iff_iterated_bottom.
Print Assumptions pa_height_eq_top_of_kreisel_consistent.
Print Assumptions pa_height_eq_zero_of_inconsistent.
Print Assumptions pa_not_exists_tarski_predicate.
Print Assumptions pa_undefinability_of_truth.
Check pa_adjoin.
Print Assumptions pa_consistent_adjoin_of_unprovable_neg.
Print Assumptions pa_consistent_adjoin_neg_of_unprovable.
Check pa_lindenbaum_lt.
Print Assumptions pa_dense_of_adjoin_incomplete.
Check r0_sigma_one_definable.
Check r0_sigma_one_definable_predicate.
Check r0_arithmetically_semidecidable_predicate.
Print Assumptions
  r0_arithmetically_semidecidable_iff_sigma_one_definable.
Print Assumptions r0_re_iff_sigma_one.
Print Assumptions semidecidable_iff_transport.
Check decoded_predicate.
Print Assumptions decoded_predicate_encode_iff.
Print Assumptions semidecidable_decoded_predicate_iff.
Print Assumptions decidable_predicate_decoded.
Print Assumptions decidable_predicate_of_decoded.
Print Assumptions independent_instance_of_not_cosemidecidable.
Print Assumptions incomplete_of_not_cosemidecidable.
Check halting_unary_vector.
Print Assumptions halting_unary_vector_f1.
Check halting_arithmetic_instance.
Check arithmetic_negative_instance_semidecidable.
Print Assumptions r0_independent_instance_of_not_cosemidecidable.
Print Assumptions r0_incomplete_of_not_cosemidecidable.
Check boot_provability_comparison_le.
Check boot_provability_comparison_lt.
Print Assumptions boot_provability_comparison_le_of_lt.
Print Assumptions boot_provability_comparison_le_to_provable.
Print Assumptions boot_provability_comparison_le_trans.
Print Assumptions boot_proof_conclusion_unique.
Print Assumptions boot_provability_comparison_le_antisymm.
Print Assumptions boot_provability_comparison_iff_le_refl_provable.
Print Assumptions boot_provability_comparison_lt_irrefl.
Print Assumptions boot_provability_comparison_lt_trans.
Print Assumptions boot_provability_comparison_not_lt_of_le.
Print Assumptions boot_provability_comparison_find_minimal_proof.
Print Assumptions boot_sentence_code_neg.
Check boot_rosser_provable.
Check boot_sentence_rosser_provable.
Print Assumptions boot_rosser_quote.
Print Assumptions boot_sentence_rosser_quote.
Print Assumptions boot_rosser_quote_witness_iff.
Print Assumptions boot_sentence_rosser_witness_iff.
Print Assumptions boot_rosser_provable_to_provable.
Print Assumptions boot_standard_proof_sound.
Print Assumptions boot_sentence_rosser_provable_sound.
Print Assumptions first_order_consistent_not_both.
Print Assumptions boot_rosser_internalize.
Print Assumptions boot_sentence_rosser_internalize.
Print Assumptions boot_not_rosser_provable.
Print Assumptions boot_not_sentence_rosser_provable.
Check boot_refutable.
Check boot_sentence_refutable.
Print Assumptions boot_refutable_quote.
Print Assumptions boot_sentence_refutable_quote.
Print Assumptions boot_sentence_refutable_witness_iff.
Print Assumptions boot_sentence_refutable_iff_theory.
Print Assumptions boot_internalize_refutation.
Print Assumptions boot_internalize_refutability.
Print Assumptions boot_standard_refutation_sound.
Print Assumptions boot_sentence_refutable_sound.
Print Assumptions boot_sentence_consistent_not_both.
Print Assumptions boot_sentence_provable_not_refutable.
Print Assumptions boot_sentence_refutable_not_provable.
Print Assumptions pa_exists_true_unprovable_of_incomplete.
Print Assumptions pa_incomplete_strictly_weaker_than_truth.
Print Assumptions pa_logic_consistent_iff_unprovable_bottom.
Check pa_consistent_with.
Print Assumptions pa_consistent_with_unfold.
Print Assumptions pa_consistent_with_truth_iff.
Print Assumptions pa_con_truth_iff_logic_consistent.
Check boot_consistent.
Check boot_consistent_with.
Check boot_sentence_consistent_with.
Print Assumptions boot_consistent_with_quote.
Print Assumptions boot_sentence_consistent_with_quote.
Print Assumptions boot_sentence_consistent_with_iff_theory.
Print Assumptions boot_consistent_iff_first_order_consistent.
Print Assumptions boot_sentence_consistent_with_iff_adjoin_consistent.
Print Assumptions
  boot_sentence_consistent_with_iff_union_singleton_consistent.
Print Assumptions
  boot_sentence_consistent_with_iff_boot_consistent_union_singleton.
Check boot_bounded_provable.
Check boot_restricted_provable.
Check boot_sentence_restricted_provable.
Print Assumptions boot_bounded_provable_witness_iff.
Print Assumptions boot_restricted_provable_witness_iff.
Print Assumptions boot_restricted_quote_witness_iff.
Print Assumptions boot_sentence_restricted_provable_witness_iff.
Print Assumptions boot_bounded_provable_mono.
Print Assumptions boot_restricted_provable_mono.
Print Assumptions boot_bounded_provable_to_provable.
Print Assumptions boot_restricted_provable_to_provable.
Print Assumptions boot_sentence_restricted_provable_sound.
Print Assumptions nat_lt_two_pow_succ.
Print Assumptions boot_sentence_provable_iff_exists_restricted.
Print Assumptions boot_bounded_proof_code_lower_bound.
Print Assumptions boot_restricted_proof_code_lower_bound.
Print Assumptions boot_sentence_restricted_proof_code_lower_bound.
Check boot_language_lor_definable.
Check language_func_code_valid.
Check language_rel_code_valid.
Check boot_language_is_func.
Check boot_language_is_rel.
Print Assumptions boot_func_quote_inj.
Print Assumptions boot_rel_quote_inj.
Print Assumptions boot_code_eq_delta_zero.
Print Assumptions boot_code_eq_eval.
Print Assumptions oring_func_code_valid_iff.
Print Assumptions oring_rel_code_valid_iff.
Print Assumptions boot_oring_is_func_eval.
Print Assumptions boot_oring_is_rel_eval.
Check oring_language_lor_definable.
Print Assumptions boot_oring_func_zero_index.
Print Assumptions boot_oring_func_one_index.
Print Assumptions boot_oring_func_add_index.
Print Assumptions boot_oring_func_mul_index.
Print Assumptions boot_oring_rel_eq_index.
Print Assumptions boot_oring_rel_lt_index.
Check boot_qq_bvar.
Check boot_qq_fvar.
Check boot_qq_func.
Print Assumptions boot_qq_bvar_argument_le.
Print Assumptions boot_qq_fvar_argument_le.
Print Assumptions boot_qq_func_arity_le.
Print Assumptions boot_qq_func_symbol_le.
Print Assumptions boot_qq_func_arguments_le.
Print Assumptions boot_qq_func_component_le.
Print Assumptions boot_qq_bvar_injective.
Print Assumptions boot_qq_fvar_injective.
Print Assumptions boot_qq_func_injective.
Check boot_term_code.
Check boot_is_uterm.
Check boot_is_uterm_vec.
Check boot_is_semiterm.
Check boot_is_semiterm_vec.
Print Assumptions boot_term_code_case_iff.
Print Assumptions boot_term_code_func_iff.
Print Assumptions boot_term_code_vec_cons_iff.
Print Assumptions boot_term_code_monotone.
Print Assumptions boot_is_semiterm_weaken.
Print Assumptions boot_is_uterm_case_iff.
Print Assumptions boot_is_uterm_func_iff.
Print Assumptions boot_is_semiterm_case_iff.
Print Assumptions boot_is_semiterm_func_iff.
Print Assumptions boot_term_code_induction.
Print Assumptions boot_is_uterm_induction.
Print Assumptions boot_is_semiterm_induction.
Print Assumptions semiterm_code_policy_iff.
Print Assumptions semiterm_code_is_uterm.
Print Assumptions semiterm_code_is_semiterm.
Check boot_nat_encoding.
Print Assumptions boot_is_semiterm_has_quote.
Print Assumptions boot_is_semiterm_quote_iff.
Check boot_semiterm_bv.
Print Assumptions boot_fin_max_le_iff.
Print Assumptions boot_semiterm_bv_component_le.
Print Assumptions boot_semiterm_bv_le_iff.
Print Assumptions semiterm_code_is_semiterm_iff_bv.
Check boot_rewrite_code.
Check boot_rewrite_code_total.
Print Assumptions boot_rewrite_code_quote.
Print Assumptions boot_rewrite_code_total_quote.
Print Assumptions boot_rewrite_code_some_iff.
Print Assumptions boot_is_semiterm_decode_quote.
Print Assumptions boot_rewrite_code_total_preserves.
Print Assumptions boot_rewrite_code_total_ext.
Print Assumptions boot_rewrite_code_total_comp.
Check boot_term_subst_code.
Print Assumptions boot_term_subst_code_bvar.
Print Assumptions boot_term_subst_code_fvar.
Print Assumptions boot_term_subst_code_func.
Print Assumptions boot_term_subst_code_preserves.
Print Assumptions boot_term_subst_code_comp.
Check boot_term_shift_code.
Check boot_term_bshift_code.
Print Assumptions boot_term_shift_code_bvar.
Print Assumptions boot_term_shift_code_fvar.
Print Assumptions boot_term_bshift_code_bvar.
Print Assumptions boot_term_bshift_code_fvar.
Print Assumptions boot_term_shift_code_preserves.
Print Assumptions boot_term_bshift_code_preserves.
Print Assumptions rew_bshift_shift_comm.
Print Assumptions boot_term_bshift_shift_comm.
Print Assumptions boot_term_shift_subst.
Check boot_term_fv_free.
Print Assumptions boot_term_fv_free_bvar.
Print Assumptions boot_term_fv_free_fvar.
Print Assumptions boot_term_fv_free_bshift.
Check boot_typed_semiterm.
Check boot_typed_term.
Check boot_typed_semiterm_vec.
Check boot_typed_shift.
Check boot_typed_bshift.
Check boot_typed_subst.
Check boot_typed_free.
Check boot_typed_q.
Print Assumptions boot_typed_shift_func.
Print Assumptions boot_typed_bshift_func.
Print Assumptions boot_typed_subst_func.
Print Assumptions boot_typed_free_bvar.
Print Assumptions boot_typed_q_as_rew_q.
Print Assumptions boot_typed_bshift_subst_q.
Print Assumptions boot_typed_bshift_shift_comm.
Print Assumptions boot_typed_shift_subst.
Print Assumptions boot_typed_subst_subst.
Print Assumptions boot_typed_free_bshift.
Check boot_typed_fv_free.
Print Assumptions boot_typed_fv_free_bvar.
Print Assumptions boot_typed_fv_free_fvar.
Print Assumptions boot_typed_fv_free_bshift.
Print Assumptions boot_typed_subst_code.
Print Assumptions boot_typed_shift_code.
Print Assumptions boot_typed_bshift_code.
Check boot_typed_quote.
Check boot_closed_quote.
Print Assumptions boot_typed_quote_bvar.
Print Assumptions boot_typed_quote_fvar.
Print Assumptions boot_typed_quote_func.
Print Assumptions boot_typed_quote_injective.
Print Assumptions boot_typed_quote_inj_iff.
Print Assumptions boot_typed_quote_decode.
Print Assumptions boot_closed_quote_decode.
Print Assumptions boot_typed_quote_recognized.
Print Assumptions boot_typed_quote_sound.
Print Assumptions boot_closed_quote_emb.
Print Assumptions boot_typed_quote_shift.
Print Assumptions boot_typed_quote_bshift.
Print Assumptions boot_typed_quote_subst.
Print Assumptions boot_typed_quote_q_succ.
Print Assumptions boot_typed_quote_encoding.
Print Assumptions boot_closed_quote_encoding.
Check boot_qq_verum.
Check boot_qq_falsum.
Check boot_qq_rel.
Check boot_qq_nrel.
Check boot_qq_and.
Check boot_qq_or.
Check boot_qq_all.
Check boot_qq_exists.
Print Assumptions boot_qq_rel_quote.
Print Assumptions boot_qq_nrel_quote.
Print Assumptions boot_qq_and_quote.
Print Assumptions boot_qq_or_quote.
Print Assumptions boot_qq_all_quote.
Print Assumptions boot_qq_exists_quote.
Check boot_is_semiformula.
Check boot_is_formula.
Check boot_is_uformula.
Print Assumptions boot_is_semiformula_case_iff.
Print Assumptions boot_is_semiformula_is_uformula.
Print Assumptions semiformula_code_is_semiformula.
Print Assumptions boot_is_semiformula_has_quote.
Print Assumptions boot_is_semiformula_quote_iff.
Print Assumptions boot_is_semiformula_decode_quote.
Check boot_formula_transform_code.
Check boot_formula_transform_code_total.
Print Assumptions boot_formula_transform_code_quote.
Print Assumptions boot_formula_transform_code_total_quote.
Print Assumptions boot_formula_transform_code_some_iff.
Print Assumptions boot_formula_transform_code_total_preserves.
Check boot_formula_rewrite_code.
Print Assumptions boot_formula_rewrite_code_quote.
Print Assumptions boot_formula_rewrite_code_preserves.
Print Assumptions boot_formula_rewrite_code_comp.
Check boot_formula_subst_code.
Check boot_formula_shift_code.
Check boot_formula_bshift_code.
Print Assumptions boot_formula_subst_code_quote.
Print Assumptions boot_formula_shift_code_quote.
Print Assumptions boot_formula_bshift_code_quote.
Print Assumptions boot_formula_subst_code_preserves.
Print Assumptions boot_formula_shift_code_preserves.
Print Assumptions boot_formula_bshift_code_preserves.
Print Assumptions boot_formula_subst_code_comp.
Check boot_formula_neg_code.
Print Assumptions boot_formula_neg_code_quote.
Print Assumptions boot_formula_neg_verum.
Print Assumptions boot_formula_neg_falsum.
Print Assumptions boot_formula_neg_and_quote.
Print Assumptions boot_formula_neg_or_quote.
Print Assumptions boot_formula_neg_code_preserves.
Print Assumptions boot_formula_neg_code_involutive.
Print Assumptions boot_formula_neg_rewrite.
Check boot_typed_semiformula.
Check boot_typed_formula.
Check boot_typed_formula_neg.
Check boot_typed_formula_imp.
Check boot_typed_formula_iff.
Check boot_typed_formula_shift.
Check boot_typed_formula_subst.
Check boot_typed_formula_free.
Print Assumptions boot_typed_formula_neg_involutive.
Print Assumptions boot_typed_formula_neg_inj_iff.
Print Assumptions boot_typed_formula_neg_and.
Print Assumptions boot_typed_formula_neg_all.
Print Assumptions boot_typed_formula_shift_rel.
Print Assumptions boot_typed_formula_shift_all.
Print Assumptions boot_typed_formula_shift_exists.
Print Assumptions boot_typed_formula_shift_neg.
Print Assumptions boot_typed_formula_shift_iff.
Print Assumptions boot_typed_q_subst_equiv.
Print Assumptions boot_typed_formula_subst_rel.
Print Assumptions boot_typed_formula_subst_all.
Print Assumptions boot_typed_formula_subst_exists.
Print Assumptions boot_typed_formula_subst_neg.
Print Assumptions boot_typed_formula_subst_id.
Print Assumptions boot_typed_formula_subst_subst.
Print Assumptions boot_typed_formula_shift_subst.
Print Assumptions boot_typed_formula_free_as_shift_subst.
Print Assumptions boot_typed_formula_free_neg.
Check boot_typed_formula_fv_free.
Print Assumptions boot_typed_formula_fv_free_and_iff.
Print Assumptions boot_typed_formula_fv_free_or_iff.
Print Assumptions boot_typed_formula_fv_free_neg_iff.
Print Assumptions boot_typed_formula_subst_code.
Print Assumptions boot_typed_formula_shift_code.
Print Assumptions boot_typed_formula_neg_code.
Check boot_typed_formula_quote.
Check boot_closed_formula_quote.
Print Assumptions boot_typed_formula_quote_verum.
Print Assumptions boot_typed_formula_quote_rel.
Print Assumptions boot_typed_formula_quote_nrel.
Print Assumptions boot_typed_formula_quote_and.
Print Assumptions boot_typed_formula_quote_all.
Print Assumptions boot_typed_formula_quote_neg.
Print Assumptions boot_typed_formula_quote_imp.
Print Assumptions boot_typed_formula_quote_iff.
Print Assumptions boot_typed_formula_quote_injective.
Print Assumptions boot_typed_formula_quote_inj_iff.
Print Assumptions boot_typed_formula_quote_decode.
Print Assumptions boot_closed_formula_quote_decode.
Print Assumptions boot_typed_formula_quote_recognized.
Print Assumptions boot_typed_formula_quote_sound.
Print Assumptions boot_closed_formula_quote_emb.
Print Assumptions boot_typed_formula_quote_shift.
Print Assumptions boot_typed_formula_quote_subst.
Print Assumptions boot_typed_formula_quote_free.
Print Assumptions boot_typed_formula_quote_encoding.
Print Assumptions boot_closed_formula_quote_encoding.
Check boot_theory_code_member.
Check boot_theory_formula_code_member.
Print Assumptions boot_theory_formula_code_member_iff.
Check boot_theory_encoding.
Check boot_theory_classifier.
Print Assumptions boot_theory_classifier_formula_spec.
Print Assumptions boot_theory_classifier_quote_iff.
Check boot_empty_theory.
Check boot_empty_theory_encoding.
Check boot_theory_union.
Check boot_theory_union_encoding.
Check boot_singleton_theory.
Check boot_singleton_theory_encoding.
Check boot_list_theory.
Check boot_list_theory_classifier.
Print Assumptions boot_list_theory_classifier_spec.
Check boot_list_theory_encoding.
Check boot_theory_encoding_equiv.
Check boot_nat_list_code.
Print Assumptions boot_nat_list_code_injective.
Print Assumptions boot_nat_list_code_member_le.
Check boot_sequent_quote.
Print Assumptions boot_sequent_quote_injective.
Print Assumptions boot_sequent_quote_member_iff.
Check boot_is_formula_set.
Print Assumptions boot_is_formula_set_cons_iff.
Print Assumptions boot_is_formula_set_app_iff.
Print Assumptions boot_is_formula_set_quote.
Check boot_sequent_shift_code.
Print Assumptions boot_is_formula_set_shift.
Print Assumptions boot_sequent_shift_quote.
Check boot_formula_free_code.
Print Assumptions boot_formula_free_code_quote.
Print Assumptions boot_formula_free_code_preserves.
Check boot_proof_node.
Check boot_proof_conseq.
Print Assumptions boot_proof_node_nonzero.
Print Assumptions boot_proof_conseq_node.
Check boot_axL.
Check boot_verum_intro.
Check boot_and_intro.
Check boot_or_intro.
Check boot_all_intro.
Check boot_exists_intro.
Check boot_weakening_rule.
Check boot_shift_rule.
Check boot_cut_rule.
Check boot_axiom_rule.
Print Assumptions boot_proof_conseq_axL.
Print Assumptions boot_proof_conseq_and_intro.
Print Assumptions boot_proof_conseq_exists_intro.
Print Assumptions boot_proof_conseq_cut_rule.
Check boot_derivation_code.
Check boot_derivation.
Check boot_derivation_of.
Check boot_proof.
Check boot_provable.
Print Assumptions boot_derivation_code_formula_set.
Print Assumptions boot_derivation_code_conseq.
Print Assumptions boot_derivation_code_nonzero.
Print Assumptions boot_list_in_of_generic_list_member.
Check boot_derivation2_quote.
Print Assumptions boot_derivation2_quote_conseq.
Print Assumptions boot_derivation2_quote_cast.
Print Assumptions boot_derivation2_quote_recognized.
Print Assumptions boot_derivation2_quote_derivation.
Print Assumptions boot_derivation2_quote_proof.
Print Assumptions boot_derivable2_quote_provable.
Print Assumptions boot_is_formula_set_has_quote.
Print Assumptions boot_is_formula_set_quote_iff.
Print Assumptions boot_formula_set_quote_unique.
Print Assumptions boot_formula_set_quote_member.
Check boot_sequent_decode.
Print Assumptions boot_sequent_decode_quote.
Print Assumptions boot_sequent_decode_complete.
Print Assumptions boot_sequent_decode_some_iff.
Print Assumptions boot_derivation_code_typed_consequence.
Print Assumptions boot_derivation_code_sound.
Print Assumptions boot_derivation_sound.
Print Assumptions boot_proof_sound.
Print Assumptions boot_provable_sound.
Print Assumptions boot_provable_quote_iff.
Check boot_formula_replicate.
Print Assumptions boot_formula_replicate_zero.
Print Assumptions boot_formula_replicate_succ.
Check boot_formula_list_conj.
Check boot_formula_list_disj.
Check boot_formula_weight.
Print Assumptions boot_formula_weight_zero.
Print Assumptions boot_formula_weight_succ.
Print Assumptions boot_formula_neg_list_conj.
Print Assumptions boot_formula_neg_list_disj.
Print Assumptions boot_formula_rewrite_list_conj.
Print Assumptions boot_formula_rewrite_list_disj.
Print Assumptions boot_formula_shift_list_conj.
Print Assumptions boot_formula_subst_list_disj.
Check boot_qq_conj_list.
Check boot_qq_disj_list.
Print Assumptions boot_formula_list_conj_quote.
Print Assumptions boot_formula_list_disj_quote.
Print Assumptions boot_is_semiformula_and_iff.
Print Assumptions boot_is_semiformula_or_iff.
Print Assumptions boot_qq_conj_list_recognized_iff.
Print Assumptions boot_qq_disj_list_recognized_iff.
Print Assumptions boot_qq_conj_list_length_le.
Check boot_qq_verums.
Print Assumptions boot_qq_verums_bound.
Print Assumptions boot_qq_verums_recognized.
Print Assumptions boot_formula_weight_quote.
Check boot_formula_subst_iteration.
Print Assumptions boot_formula_subst_iteration_zero.
Print Assumptions boot_formula_subst_iteration_succ.
Print Assumptions boot_formula_subst_iteration_length.
Print Assumptions boot_formula_subst_iteration_nth_error.
Print Assumptions boot_typed_subst_fin_coding_cons.
Print Assumptions boot_typed_shift_fin_coding_cons.
Print Assumptions boot_formula_subst_iteration_neg.
Print Assumptions boot_formula_subst_iteration_shift.
Print Assumptions boot_formula_subst_iteration_subst.
Check boot_formula_subst_iteration_conj.
Check boot_formula_disj_seq_subst.
Print Assumptions boot_formula_disj_seq_subst_zero.
Print Assumptions boot_formula_disj_seq_subst_succ.
Print Assumptions boot_formula_neg_conj_subst_iteration.
Print Assumptions boot_formula_neg_disj_subst_iteration.
Print Assumptions boot_formula_shift_conj_subst_iteration.
Print Assumptions boot_formula_shift_disj_subst_iteration.
Print Assumptions boot_formula_subst_conj_subst_iteration.
Print Assumptions boot_formula_subst_disj_subst_iteration.
Check boot_formula_subst_iteration_codes.
Print Assumptions boot_formula_subst_iteration_codes_quote.
Check boot_formula_disj_seq_subst_code.
Print Assumptions boot_formula_disj_seq_subst_code_zero.
Print Assumptions boot_formula_disj_seq_subst_code_succ.
Print Assumptions boot_formula_disj_seq_subst_code_quote.
Print Assumptions boot_formula_disj_seq_subst_code_recognized.
Check boot_sentence_code.
Print Assumptions boot_sentence_code_closed_quote.
Check boot_sentence_provable.
Print Assumptions boot_derivable_quote.
Print Assumptions boot_internalize_provability.
Print Assumptions boot_sentence_provable_iff_theory.
Print Assumptions boot_sentence_provable_sound.
Check boot_derivation2_one_sided_lk.
Check boot_derivation2_one_sided_lk_cut.
Check boot_derivation2_entailment.
Check boot_derivation2_principal.
Check boot_derivation2_modus_ponens.
Print Assumptions boot_derivation2_modus_ponens_raw.
Print Assumptions boot_formula_provability_modus_ponens.
Print Assumptions boot_provability_modus_ponens.
Print Assumptions boot_provability_D2.
Print Assumptions boot_r0_sigma_one_complete.
Print Assumptions boot_r0_sigma_one_complete_of_subset.
Print Assumptions boot_r0_sigma_one_provable_iff.
Check boot_subst_numeral_code.
Print Assumptions boot_subst_numeral_code_quote.
Print Assumptions boot_subst_numeral_code_quote_quote.
Print Assumptions boot_subst_numeral_code_recognized.
Check boot_subst_numerals_code.
Print Assumptions boot_subst_numerals_code_quote.
Print Assumptions boot_subst_numerals_code_quote_quote.
Print Assumptions boot_subst_numerals_code_recognized.
Print Assumptions boot_subst_numeral_code_as_numerals.
Check boot_subst_numeral_params_code.
Print Assumptions boot_subst_numeral_params_code_quote.
Print Assumptions boot_subst_numeral_params_code_quote_quote.
Print Assumptions boot_subst_numeral_params_code_recognized.
Print Assumptions boot_subst_numeral_params_zero.
Check boot_arithmetic_numeral.
Check boot_arithmetic_subst_numeral.
Check boot_arithmetic_subst_numerals.
Check boot_arithmetic_subst_numeral_params.
Print Assumptions boot_arithmetic_subst_numeral_quote.
Print Assumptions boot_arithmetic_subst_numerals_quote.
Print Assumptions boot_arithmetic_subst_numeral_params_quote.
Check semiformula_nest_argument_terms.
Check semiformula_nest_result_terms.
Check semiformula_nest_body.
Check semiformula_nest.
Print Assumptions semiformula_nest_argument_terms_eval.
Print Assumptions semiformula_nest_result_terms_eval.
Print Assumptions semiformula_eval_nest.
Check semiformula_nest_func_argument_terms.
Check semiformula_nest_func_result_terms.
Check semiformula_nest_func_body.
Check semiformula_nest_func.
Print Assumptions semiformula_nest_func_argument_terms_eval.
Print Assumptions semiformula_nest_func_result_terms_eval.
Print Assumptions semiformula_eval_nest_func.
Check nat_pow2.
Print Assumptions nat_pow2_iff_exponent.
Print Assumptions nat_pow2_power.
Print Assumptions nat_pow2_exponent_unique.
Print Assumptions nat_pow2_pos.
Print Assumptions nat_pow2_nonzero.
Print Assumptions nat_pow2_one.
Print Assumptions nat_pow2_two.
Print Assumptions nat_pow2_not_zero.
Print Assumptions nat_pow2_double_iff.
Print Assumptions nat_pow2_four_mul_iff.
Print Assumptions nat_pow2_elim.
Print Assumptions nat_pow2_elim_strict.
Print Assumptions nat_pow2_two_divides.
Print Assumptions nat_pow2_div2.
Print Assumptions nat_pow2_double_div2.
Print Assumptions nat_pow2_mul.
Print Assumptions nat_pow2_square.
Print Assumptions nat_pow2_le_iff_divide.
Print Assumptions nat_pow2_two_le.
Print Assumptions nat_pow2_le_iff_lt_double.
Print Assumptions nat_pow2_lt_iff_double_le.
Print Assumptions nat_pow2_not_three.
Print Assumptions nat_pow2_four_le.
Print Assumptions nat_pow2_square_or_double_square.
Check nat_ppow2.
Print Assumptions nat_ppow2_iff_index.
Print Assumptions nat_ppow2_power.
Print Assumptions nat_ppow2_index_unique.
Print Assumptions nat_ppow2_pow2.
Print Assumptions nat_ppow2_pos.
Print Assumptions nat_ppow2_one_lt.
Print Assumptions nat_ppow2_two.
Print Assumptions nat_ppow2_four.
Print Assumptions nat_ppow2_not_zero.
Print Assumptions nat_ppow2_not_one.
Print Assumptions nat_ppow2_not_three.
Print Assumptions nat_ppow2_square_index.
Print Assumptions nat_ppow2_square.
Print Assumptions nat_ppow2_elim.
Print Assumptions nat_ppow2_two_le.
Print Assumptions nat_ppow2_two_lt.
Print Assumptions nat_ppow2_four_le.
Print Assumptions nat_ppow2_four_lt.
Print Assumptions nat_ppow2_square_ne_two.
Print Assumptions nat_ppow2_square_ne_four.
Print Assumptions nat_ppow2_square_le_of_lt.
Print Assumptions nat_ppow2_square_interval_unique.
Print Assumptions nat_ppow2_double_square_interval_unique.
Check nat_exponential.
Check nat_exp.
Print Assumptions nat_exponential_graph.
Print Assumptions nat_exponential_zero_one.
Print Assumptions nat_exponential_one_two.
Print Assumptions nat_exponential_two_four.
Print Assumptions nat_exponential_range_pow2.
Print Assumptions nat_exponential_range_iff_pow2.
Print Assumptions nat_exponential_range_pos.
Print Assumptions nat_exponential_lt.
Print Assumptions nat_not_exponential_of_le.
Print Assumptions nat_exponential_even_intro.
Print Assumptions nat_exponential_even.
Print Assumptions nat_exponential_even_square.
Print Assumptions nat_exponential_odd_intro.
Print Assumptions nat_exponential_odd.
Print Assumptions nat_exponential_succ.
Print Assumptions nat_exponential_succ_double.
Print Assumptions nat_exponential_elim.
Print Assumptions nat_exponential_zero_unique.
Print Assumptions nat_exponential_functional.
Print Assumptions nat_exponential_injective.
Print Assumptions nat_exponential_monotone_iff.
Print Assumptions nat_exponential_monotone_le_iff.
Print Assumptions nat_exponential_add_mul.
Print Assumptions nat_exponential_exists_unique.
Print Assumptions nat_exp_spec.
Print Assumptions nat_exp_injective.
Print Assumptions nat_exp_zero.
Print Assumptions nat_exp_succ.
Print Assumptions nat_exp_even.
Print Assumptions nat_exp_odd.
Print Assumptions nat_exp_add.
Print Assumptions N_succ_le_of_lt.
Check nat_log.
Print Assumptions nat_log_zero.
Print Assumptions nat_log_one.
Print Assumptions nat_log_two.
Print Assumptions nat_log_le_self.
Print Assumptions nat_log_lt_self_of_pos.
Print Assumptions nat_log_bounds.
Print Assumptions nat_log_unique.
Print Assumptions nat_log_exp.
Print Assumptions nat_exponential_log.
Print Assumptions nat_exponential_of_pow2.
Print Assumptions nat_log_two_mul_of_pos.
Print Assumptions nat_log_two_mul_add_one_of_pos.
Print Assumptions nat_log_monotone.
Print Assumptions nat_log_mul_pow2.
Print Assumptions nat_log_mul_exp.
Print Assumptions nat_log_mul_pow2_add_of_lt.
Print Assumptions nat_log_mul_exp_add_of_lt.
Check nat_length.
Print Assumptions nat_length_zero.
Print Assumptions nat_length_one.
Print Assumptions nat_length_of_nonzero.
Print Assumptions nat_length_of_pos.
Print Assumptions nat_length_pos_iff.
Print Assumptions nat_length_eq_zero_iff.
Print Assumptions nat_length_le_self.
Print Assumptions nat_exponential_length.
Print Assumptions nat_length_exp.
Print Assumptions nat_length_two_mul_of_pos.
Print Assumptions nat_length_two_mul_add_one.
Print Assumptions nat_length_monotone.
Print Assumptions nat_pos_of_lt_length.
Print Assumptions nat_le_log_of_lt_length.
Print Assumptions nat_exp_le_iff_le_log.
Print Assumptions nat_exponential_le_iff_lt_length.
Print Assumptions nat_exponential_lt_iff_length_le.
Print Assumptions nat_lt_exp_length.
Print Assumptions nat_length_mul_exp.
Print Assumptions nat_length_mul_pow2_add_of_lt.
Print Assumptions nat_length_mul_exp_add_of_lt.
Print Assumptions nat_sq_length_le_three_mul.
Print Assumptions nat_two_mul_sqrt_le_self.
Print Assumptions nat_sqrt_pos_iff.
Check nat_bexp.
Print Assumptions nat_bexp_of_lt.
Print Assumptions nat_bexp_of_le.
Print Assumptions nat_bexp_exponential_iff.
Print Assumptions nat_bexp_le_self.
Print Assumptions nat_bexp_monotone_iff.
Print Assumptions nat_bexp_monotone_le_iff.
Print Assumptions nat_bexp_monotone_cross_iff.
Print Assumptions nat_bexp_monotone_cross_le_iff.
Print Assumptions nat_pow_four_le_pow_four.
Print Assumptions nat_bexp_four_mul.
Print Assumptions nat_bexp_eq_of_lt_length.
Print Assumptions nat_bexp_pow2.
Print Assumptions nat_bexp_pos.
Print Assumptions nat_lt_bexp.
Print Assumptions nat_log_bexp.
Print Assumptions nat_length_bexp.
Print Assumptions nat_bexp_zero.
Print Assumptions nat_bexp_pos_zero.
Print Assumptions nat_bexp_add.
Check nat_fbit.
Print Assumptions nat_fbit_le_one.
Print Assumptions nat_fbit_lt_two.
Print Assumptions nat_fbit_eq_one_iff.
Print Assumptions nat_fbit_eq_zero_iff.
Print Assumptions nat_fbit_eq_zero_of_le.
Print Assumptions nat_fbit_zero.
Print Assumptions nat_fbit_double_succ.
Print Assumptions nat_fbit_double_add_one_succ.
Print Assumptions nat_fbit_double_zero.
Print Assumptions nat_fbit_double_add_one_zero.
Check nat_omega1_holds.
Print Assumptions standard_nat_omega1.
Print Assumptions nat_exponential_square_length_exists_unique.
Check nat_smash.
Print Assumptions nat_exponential_smash.
Print Assumptions nat_smash_exists_unique.
Print Assumptions nat_exponential_smash_one.
Print Assumptions nat_smash_pow2.
Print Assumptions nat_smash_pos.
Print Assumptions nat_smash_exponent_lt.
Print Assumptions nat_length_smash.
Print Assumptions nat_smash_zero_left.
Print Assumptions nat_smash_zero_right.
Print Assumptions nat_smash_comm.
Print Assumptions nat_lt_smash_one.
Print Assumptions nat_smash_one_le_double_add_one.
Print Assumptions nat_lt_smash_iff.
Print Assumptions nat_smash_le_iff.
Print Assumptions nat_lt_smash_one_iff.
Print Assumptions nat_smash_monotone.
Print Assumptions nat_bexp_eq_smash.
Print Assumptions nat_smash_two_mul.
Print Assumptions nat_smash_two_mul_le_square.
Check positive_nuon.
Check nat_nuon.
Check nat_Nuon.
Print Assumptions positive_nuon_pos.
Print Assumptions positive_nuon_le_size.
Print Assumptions nat_nuon_zero.
Print Assumptions nat_nuon_one.
Print Assumptions nat_mul_length_lt_length_smash.
Print Assumptions nat_mul_length_lt_length_smash_length.
Check nat_polyI.
Check nat_polyL.
Check nat_polyU.
Print Assumptions nat_length_polyI.
Print Assumptions nat_polyI_le.
Print Assumptions nat_four_mul_smash_self.
Print Assumptions nat_polyI_smash_self_polybounded.
Print Assumptions nat_polyI_smash_polyL_polybounded.
Print Assumptions nat_sq_polyI_smash_polyL_polybounded.
Print Assumptions nat_nuon_double.
Print Assumptions nat_nuon_double_add_one.
Print Assumptions nat_nuon_pos_iff.
Print Assumptions nat_nuon_eq_zero_iff.
Print Assumptions nat_nuon_le_length.
Print Assumptions nat_nuon_le_self.
Print Assumptions nat_Nuon_exists_unique.
Print Assumptions nat_Nuon_functional.
Print Assumptions nat_Nuon_graph.
Print Assumptions nat_nuon_pow2.
Print Assumptions nat_nuon_under.
Print Assumptions nat_nuon_singleton.
Check membership_structure.
Check membership_carrier.
Check membership_rel.
Check set_model_subset.
Check set_model_is_empty.
Check set_model_is_nonempty.
Check set_model_strict_subset.
Check membership_extensional.
Print Assumptions set_model_subset_def.
Print Assumptions set_model_subset_refl.
Print Assumptions set_model_subset_trans.
Print Assumptions set_model_subset_antisym.
Print Assumptions set_model_empty_not_nonempty.
Print Assumptions set_model_nonempty_not_empty.
Print Assumptions set_model_not_nonempty_iff_empty.
Print Assumptions set_model_not_empty_iff_nonempty.
Print Assumptions set_model_strict_subset_def.
Print Assumptions set_model_strict_subset_irrefl.
Print Assumptions set_model_strict_subset_subset.
Print Assumptions set_model_strict_subset_asym.
Print Assumptions set_model_strict_subset_trans.
Check membership_submodel.
Print Assumptions membership_submodel_rel_iff.
Print Assumptions membership_submodel_subset_iff.
Print Assumptions membership_submodel_empty_iff.
Print Assumptions membership_submodel_nonempty_iff.
Check set_func.
Check set_func_elim.
Check set_rel.
Check set_language.
Check set_language_eq.
Check set_language_mem.
Print Assumptions set_language_relational.
Print Assumptions set_rel_arity_two.
Print Assumptions set_rel_elim.
Check set_language_decidable_eq.
Check set_rel_encode.
Check set_rel_decode.
Print Assumptions set_rel_decode_encode.
Check set_language_func_encoding.
Check set_language_rel_encoding.
Check set_language_encodable.
Check set_function_symbols.
Check set_relation_symbols.
Print Assumptions set_function_symbols_complete.
Print Assumptions set_relation_symbols_complete.
Check set_language_finite.
Check set_theory_syntax.
Check set_semiterm.
Check set_term.
Check set_semiformula.
Check set_formula.
Check set_semisentence.
Check set_sentence.
Check set_semiproposition.
Check set_proposition.
Check set_standard_func.
Check set_standard_rel.
Check set_standard_structure.
Print Assumptions set_standard_structure_eq.
Print Assumptions set_standard_structure_mem.
Print Assumptions set_standard_structure_mem_two.
Check membership_of_set_structure.
Check set_structure_equality_correct.
Check canonical_set_structure.
Print Assumptions canonical_set_structure_mem_two.
Print Assumptions canonical_set_structure_func.
Print Assumptions canonical_set_structure_mem.
Print Assumptions canonical_set_structure_eq.
Print Assumptions canonical_set_structure_rel.
Print Assumptions set_standard_structure_equality_correct.
Check set_model_successor.
Check set_axiom_code.
Check set_axiom_holds.
Check set_axiom_family.
Check set_axiom_family_subset.
Check set_axiom_family_union.
Check set_theory_model.
Print Assumptions set_axiom_family_subset_refl.
Print Assumptions set_axiom_family_subset_trans.
Print Assumptions set_theory_model_of_subset.
Print Assumptions set_theory_model_union_iff.
Check zermelo_axiom.
Check zf_axiom.
Check choice_axiom.
Check zermelo_choice_axiom.
Check zfc_axiom.
Print Assumptions zermelo_axiom_subset_zf.
Print Assumptions zermelo_axiom_subset_zc.
Print Assumptions zf_axiom_subset_zfc.
Print Assumptions choice_axiom_subset_zc.
Print Assumptions choice_axiom_subset_zfc.
Print Assumptions zermelo_choice_axiom_subset_zfc.
Print Assumptions set_zf_model_is_zermelo.
Print Assumptions set_zc_model_iff_zermelo_and_choice.
Print Assumptions set_zfc_model_iff_zf_and_choice.
Print Assumptions set_zfc_model_is_zc.
Print Assumptions set_zermelo_choice_model.
Print Assumptions set_zf_choice_model.
Check zermelo_operations.
Check z_ops_extensional.
Check z_empty.
Check z_empty_spec.
Check z_pair.
Check z_pair_spec.
Check z_sunion.
Check z_sunion_spec.
Check z_power.
Check z_power_spec.
Check z_separate.
Check z_separate_spec.
Check z_infinity.
Check z_infinity_spec.
Check z_foundation_spec.
Check z_singleton.
Check z_union.
Check z_insert.
Check z_sinter.
Check z_inter.
Check z_sdiff.
Check z_successor.
Print Assumptions z_extensionality.
Print Assumptions z_subset_antisym.
Print Assumptions z_not_mem_empty.
Print Assumptions z_empty_unique.
Print Assumptions z_eq_empty_or_nonempty.
Print Assumptions z_empty_subset.
Print Assumptions z_subset_empty_iff_eq_empty.
Print Assumptions z_pair_mem_iff.
Print Assumptions z_pair_unique.
Print Assumptions z_pair_nonempty.
Print Assumptions z_singleton_mem_iff.
Print Assumptions z_singleton_injective.
Print Assumptions z_singleton_nonempty.
Print Assumptions z_singleton_subset_iff_mem.
Print Assumptions z_sunion_mem_iff.
Print Assumptions z_subset_sunion_of_mem.
Print Assumptions z_sunion_empty.
Print Assumptions z_sunion_singleton.
Print Assumptions z_sunion_nonempty_iff.
Print Assumptions z_union_mem_iff.
Print Assumptions z_union_comm.
Print Assumptions z_union_assoc.
Print Assumptions z_union_self.
Print Assumptions z_union_empty_left.
Print Assumptions z_union_empty_right.
Print Assumptions z_union_nonempty_iff.
Print Assumptions z_subset_union_left.
Print Assumptions z_subset_union_right.
Print Assumptions z_union_eq_iff_right_subset.
Print Assumptions z_union_eq_iff_left_subset.
Print Assumptions z_insert_mem_iff.
Print Assumptions z_union_insert.
Print Assumptions z_insert_empty.
Print Assumptions z_insert_nonempty.
Print Assumptions z_subset_insert.
Print Assumptions z_sunion_insert.
Print Assumptions z_insert_union.
Print Assumptions z_insert_eq_self_of_mem.
Print Assumptions z_power_mem_iff.
Print Assumptions z_power_unique.
Print Assumptions z_empty_mem_power.
Print Assumptions z_self_mem_power.
Print Assumptions z_power_empty.
Print Assumptions z_power_nonempty.
Print Assumptions z_separate_mem_iff.
Print Assumptions z_separate_subset.
Print Assumptions z_separate_empty.
Print Assumptions z_sinter_mem_iff.
Print Assumptions z_sinter_subset_of_mem.
Print Assumptions z_sinter_empty.
Print Assumptions z_sinter_singleton.
Print Assumptions z_subset_sinter_iff.
Print Assumptions z_inter_mem_iff.
Print Assumptions z_inter_comm.
Print Assumptions z_inter_assoc.
Print Assumptions z_inter_subset_left.
Print Assumptions z_inter_subset_right.
Print Assumptions z_inter_self.
Print Assumptions z_inter_empty_left.
Print Assumptions z_inter_empty_right.
Print Assumptions z_inter_eq_left_of_subset.
Print Assumptions z_inter_eq_right_of_subset.
Print Assumptions z_sinter_insert.
Print Assumptions z_insert_inter_of_mem.
Print Assumptions z_insert_inter_of_not_mem.
Print Assumptions z_singleton_inter_of_mem.
Print Assumptions z_singleton_inter_of_not_mem.
Print Assumptions z_sdiff_mem_iff.
Print Assumptions z_sdiff_subset.
Print Assumptions z_strict_subset_iff_difference_witness.
Print Assumptions z_sdiff_nonempty_of_strict_subset.
Print Assumptions z_sdiff_empty_right.
Print Assumptions z_sdiff_empty_left.
Print Assumptions z_singleton_sdiff_of_mem.
Print Assumptions z_singleton_sdiff_of_not_mem.
Print Assumptions z_insert_sdiff_of_mem.
Print Assumptions z_insert_sdiff_of_not_mem.
Print Assumptions z_successor_mem_iff.
Print Assumptions z_successor_is_successor.
Print Assumptions z_mem_successor_self.
Print Assumptions z_subset_successor.
Check z_is_inductive.
Print Assumptions z_infinity_inductive.
Check z_omega.
Print Assumptions z_omega_mem_iff.
Print Assumptions z_omega_inductive.
Print Assumptions z_omega_subset_inductive.
Check z_of_nat.
Print Assumptions z_of_nat_in_omega.
Print Assumptions z_successor_injective.
Print Assumptions z_of_nat_injective.
Print Assumptions z_of_nat_eq_iff.
Print Assumptions z_of_nat_mem_iff.
Print Assumptions z_omega_induction.
Print Assumptions z_foundation_inter_empty.
Print Assumptions z_mem_irrefl.
Print Assumptions z_ne_of_mem.
Print Assumptions z_mem_asym.
Print Assumptions z_mem_asym3.
Print Assumptions z_ne_successor.
Check z_kpair.
Check z_kpair_fst.
Check z_kpair_snd.
Print Assumptions z_kpair_mem_iff.
Print Assumptions z_sunion_kpair.
Print Assumptions z_sinter_kpair.
Print Assumptions z_kpair_fst_eval.
Print Assumptions z_kpair_snd_separation.
Print Assumptions z_kpair_snd_eval.
Print Assumptions z_pair_right_injective.
Print Assumptions z_kpair_injective.
Print Assumptions z_kpair_eq_iff.
Print Assumptions z_kpair_in_power_power_union.
Check z_product.
Print Assumptions z_product_mem_iff.
Print Assumptions z_product_monotone.
Print Assumptions z_product_union_left.
Print Assumptions z_product_empty_right.
Print Assumptions z_product_empty_left.
Print Assumptions z_kpair_mem_product_iff.
Print Assumptions z_product_singletons.
Print Assumptions z_insert_kpair_subset_insert_product.
Print Assumptions zermelo_operations_model.
Check z_domain.
Check z_range.
Print Assumptions z_mem_sunion_sunion_of_kpair_mem_left.
Print Assumptions z_mem_sunion_sunion_of_kpair_mem_right.
Print Assumptions z_domain_mem_iff.
Print Assumptions z_range_mem_iff.
Print Assumptions z_mem_domain_of_kpair_mem.
Print Assumptions z_mem_range_of_kpair_mem.
Print Assumptions z_domain_empty.
Print Assumptions z_range_empty.
Print Assumptions z_domain_product.
Print Assumptions z_range_product.
Print Assumptions z_domain_subset_of_subset_product.
Print Assumptions z_range_subset_of_subset_product.
Print Assumptions z_domain_union.
Print Assumptions z_range_union.
Print Assumptions z_domain_inter_subset.
Print Assumptions z_range_inter_subset.
Print Assumptions z_domain_insert_kpair.
Print Assumptions z_range_insert_kpair.
Check z_function.
Print Assumptions z_mem_function_iff.
Print Assumptions z_mem_function_intro.
Print Assumptions z_subset_product_of_mem_function.
Print Assumptions z_mem_of_mem_function.
Print Assumptions z_function_subset_power_product.
Print Assumptions z_exists_unique_of_mem_function.
Print Assumptions z_exists_of_mem_function.
Print Assumptions z_domain_eq_of_mem_function.
Print Assumptions z_range_subset_of_mem_function.
Print Assumptions z_mem_function_range_of_mem_function.
Print Assumptions z_mem_function_of_mem_function_of_subset.
Print Assumptions z_function_subset_function_of_subset.
Check z_is_function.
Print Assumptions z_is_function_iff.
Print Assumptions z_is_function_of_mem.
Print Assumptions z_is_function_mem_function.
Print Assumptions z_is_function_mem_kpair.
Print Assumptions z_is_function_unique.
Print Assumptions z_is_function_of_subset.
Print Assumptions z_function_eq_of_subset.
Print Assumptions z_function_ext.
Print Assumptions z_is_function_insert.
Print Assumptions z_exists_two_valued_function_for_subset.
Print Assumptions z_exists_subset_for_two_valued_function.
Print Assumptions z_two_val_function_mem_iff_not.
Print Assumptions z_two_pow_card_eq_power.
Print Assumptions z_function_empty_empty.
Check z_identity.
Print Assumptions z_identity_mem_iff.
Print Assumptions z_kpair_mem_identity_iff.
Print Assumptions z_identity_mem_function.
Print Assumptions z_identity_is_function.
Print Assumptions z_identity_injective.
Check z_compose.
Print Assumptions z_mem_compose_iff.
Print Assumptions z_kpair_mem_compose_iff.
Print Assumptions z_compose_subset_product.
Print Assumptions z_compose_function.
Check z_injective.
Print Assumptions z_injective_empty.
Print Assumptions z_compose_injective.
Check z_value.
Print Assumptions z_value_mem_iff.
Print Assumptions z_value_mem_range.
Check z_restrict.
Print Assumptions z_restrict_mem_iff.
Print Assumptions z_restrict_subset.
Print Assumptions z_is_function_restrict.
Print Assumptions z_is_function_restrict_eq_self.
Print Assumptions z_domain_restrict_eq.
Print Assumptions z_kpair_mem_restrict_iff.
Print Assumptions z_restrict_restrict_eq_restrict_inter.
Print Assumptions z_restrict_restrict_of_subset.
Print Assumptions z_restrict_insert_kpair_eq_restrict_of_not_mem.
Check z_image.
Print Assumptions z_image_mem_iff.
Check z_card_le.
Print Assumptions z_card_le_of_subset.
Print Assumptions z_card_le_empty.
Print Assumptions z_card_le_refl.
Print Assumptions z_card_le_trans.
Check z_card_lt.
Print Assumptions z_card_lt_power.
Check z_card_eq.
Print Assumptions z_card_eq_refl.
Print Assumptions z_card_eq_symm.
Print Assumptions z_card_eq_trans.
Print Assumptions z_mem_two_iff.
Print Assumptions z_two_val_function_mem_iff_not.
Check membership_well_founded.
Check transitive_model.
Print Assumptions well_founded_predicate_subtype.
Print Assumptions transitive_model_well_founded.
Print Assumptions membership_well_founded_induction.
Print Assumptions transitive_model_induction.
Print Assumptions transitive_model_induction_ambient.
Check membership_minimal_of_nonempty.
Print Assumptions membership_minimal_of_nonempty.
Check universe_choice_data.
Print Assumptions universe_choice_existsUnique.
Check nat_bit.
Check nat_bit_empty.
Check nat_bit_singleton.
Check nat_bit_insert.
Check nat_bit_remove.
Check nat_bit_subset.
Print Assumptions nat_bit_mem_iff.
Print Assumptions nat_bit_exp_le_of_mem.
Print Assumptions nat_bit_lt_of_mem.
Print Assumptions nat_bit_not_mem_of_lt_exp.
Print Assumptions nat_bit_mem_iff_mul_pow2_add.
Print Assumptions nat_bit_not_mem_iff_mul_pow2_add.
Print Assumptions nat_bit_empty_eq_zero.
Print Assumptions nat_bit_not_mem_empty.
Print Assumptions nat_bit_not_mem_zero.
Print Assumptions nat_bit_singleton_eq_pow.
Print Assumptions nat_bit_singleton_injective.
Print Assumptions nat_bit_insert_eq.
Print Assumptions nat_bit_remove_eq.
Print Assumptions nat_bit_singleton_eq_insert_empty.
Print Assumptions nat_bit_mem_insert_iff.
Print Assumptions nat_bit_mem_remove_iff.
Print Assumptions nat_bit_not_mem_remove_self.
Print Assumptions nat_bit_one_eq_singleton_empty.
Print Assumptions nat_bit_mem_singleton_iff.
Print Assumptions nat_bit_remove_lt_of_mem.
Print Assumptions nat_bit_pos_of_nonempty.
Print Assumptions nat_bit_mem_insert.
Print Assumptions nat_bit_insert_eq_self_of_mem.
Print Assumptions nat_bit_subset_iff.
Print Assumptions nat_bit_subset_refl.
Print Assumptions nat_bit_subset_trans.
Print Assumptions nat_bit_eq_zero_of_subset_zero.
Print Assumptions nat_bit_le_of_subset.
Print Assumptions nat_bit_ext.
Print Assumptions nat_bit_ext_iff.
Print Assumptions nat_bit_pos_iff_nonempty.
Print Assumptions nat_bit_nonempty_of_pos.
Print Assumptions nat_bit_eq_empty_or_nonempty.
Print Assumptions nat_bit_nonempty_iff.
Print Assumptions nat_bit_isempty_iff.
Print Assumptions nat_bit_empty_subset.
Print Assumptions nat_bit_log2_mem_of_pos.
Print Assumptions nat_bit_le_log2_of_mem.
Print Assumptions nat_bit_lt_size_of_mem.
Print Assumptions nat_bit_lt_of_lt_log2.
Print Assumptions nat_bit_succ_mem_iff_div2.
Print Assumptions nat_bit_subset_div2.
Print Assumptions nat_bit_zero_not_mem_iff_even.
Print Assumptions nat_bit_zero_not_mem_double.
Print Assumptions nat_bit_zero_mem_double_add_one.
Print Assumptions nat_bit_succ_mem_double_iff.
Print Assumptions nat_bit_succ_mem_double_add_one_iff.
Check nat_bit_under.
Print Assumptions nat_bit_le_under.
Print Assumptions nat_bit_under_lt_pow.
Print Assumptions nat_bit_mem_under_iff.
Print Assumptions nat_bit_mem_exp_add_succ_sub_one.
Print Assumptions nat_bit_not_mem_under_self.
Print Assumptions nat_bit_under_injective.
Print Assumptions nat_bit_under_zero.
Print Assumptions nat_bit_under_succ.
Print Assumptions nat_bit_under_succ_arithmetic.
Print Assumptions nat_bit_lt_pow_iff.
Print Assumptions nat_bit_insert_remove.
Check hfs_code.
Check hfs_mem.
Check hfs_empty.
Check hfs_insert.
Check hfs_remove.
Check hfs_subset.
Check hfs_equiv.
Print Assumptions hfs_extensionality.
Print Assumptions hfs_equiv_iff_eq.
Print Assumptions hfs_mem_empty_iff.
Print Assumptions hfs_mem_insert_iff.
Print Assumptions hfs_mem_remove_iff.
Print Assumptions hfs_subset_trans.
Print Assumptions hfs_subset_antisym.
Print Assumptions hfs_insert_subset_insert.
Print Assumptions hfs_remove_subset.
Print Assumptions hfs_insert_remove.
Check hfs_singleton.
Check hfs_pair.
Print Assumptions hfs_mem_singleton_iff.
Print Assumptions hfs_mem_pair_iff.
Check hfs_union.
Check hfs_inter.
Print Assumptions hfs_mem_union_iff.
Print Assumptions hfs_mem_inter_iff.
Print Assumptions hfs_union_comm.
Print Assumptions hfs_inter_comm.
Print Assumptions hfs_union_subset_left.
Print Assumptions hfs_union_subset_right.
Print Assumptions hfs_inter_eq_left_of_subset.
Print Assumptions hfs_insert_eq_union_singleton.
Check hfs_disjoint.
Print Assumptions hfs_disjoint_iff.
Print Assumptions hfs_disjoint_sym.
Check hfs_arithmetize_list.
Print Assumptions hfs_mem_arithmetize_list_iff.
Print Assumptions hfs_arithmetize_list_app.
Print Assumptions hfs_arithmetize_list_nodup.
Print Assumptions hfs_arithmetize_list_insert.
Check hfs_index_pair.
Check hfs_index_fst.
Check hfs_index_snd.
Print Assumptions hfs_index_fst_pair.
Print Assumptions hfs_index_snd_pair.
Print Assumptions hfs_index_pair_injective.
Print Assumptions hfs_index_pair_projections.
Print Assumptions hfs_index_pair_left_le.
Print Assumptions hfs_index_pair_right_le.
Print Assumptions hfs_index_pair_monotone.
Print Assumptions hfs_index_fst_le.
Print Assumptions hfs_index_snd_le.
Check hfs_sequence_code_from.
Check hfs_sequence_code_list.
Print Assumptions hfs_mem_sequence_code_list_iff.
Print Assumptions hfs_mem_sequence_index_iff.
Print Assumptions hfs_sequence_code_list_injective.
Check hfs_is_sequence.
Check hfs_sequence_length_graph.
Check hfs_sequence_nth_graph.
Print Assumptions hfs_sequence_values_unique.
Print Assumptions hfs_sequence_length_graph_functional.
Print Assumptions hfs_sequence_nth_graph_functional.
Check hfs_sequence.
Check hfs_sequence_code.
Check hfs_sequence_length.
Check hfs_sequence_nth.
Check hfs_sequence_znth.
Check hfs_sequence_empty.
Check hfs_sequence_cons.
Check hfs_sequence_take.
Print Assumptions hfs_sequence_code_injective.
Print Assumptions hfs_sequence_znth_in_range.
Print Assumptions hfs_sequence_znth_out_of_range.
Print Assumptions hfs_sequence_length_zero_iff.
Print Assumptions hfs_sequence_cons_code.
Print Assumptions hfs_mem_sequence_cons_code_iff.
Print Assumptions hfs_sequence_cons_length.
Print Assumptions hfs_sequence_cons_nth_old.
Print Assumptions hfs_sequence_cons_nth_last.
Print Assumptions hfs_sequence_cons_code_subset.
Print Assumptions hfs_sequence_cons_code_strict.
Print Assumptions hfs_sequence_extensionality.
Print Assumptions hfs_sequence_eq_of_length_and_code_subset.
Print Assumptions hfs_sequence_cons_injective.
Print Assumptions hfs_sequence_cases.
Print Assumptions hfs_sequence_induction.
Print Assumptions hfs_sequence_take_length.
Print Assumptions hfs_sequence_take_nth.
Print Assumptions hfs_sequence_take_code_subset.
Print Assumptions hfs_sequence_take_full.
Check hfs_sequence_singleton.
Check hfs_sequence_doubleton.
Print Assumptions hfs_sequence_singleton_nth.
Check hfs_vector_to_sequence.
Print Assumptions vorspiel_fin_enum_nth_error.
Print Assumptions hfs_vector_to_sequence_length.
Print Assumptions hfs_vector_to_sequence_nth.
Print Assumptions hfs_vector_to_sequence_mem.
Check hfs_relation_choice_vector.
Print Assumptions hfs_relation_choice_vector_spec.
Print Assumptions hfs_sequence_exists_for_relation.
Print Assumptions hfs_sequence_existsUnique_for_relation.
Print Assumptions hfs_mem_list_big_union_iff.
Print Assumptions hfs_mem_list_big_inter_iff.
Print Assumptions hfs_list_big_union_empty.
Print Assumptions hfs_list_big_union_cons.
Print Assumptions hfs_list_big_union_app.
Print Assumptions hfs_list_big_union_subset_of_subset.
Print Assumptions hfs_list_big_inter_singleton.
Print Assumptions hfs_list_big_inter_cons.
Print Assumptions hfs_list_big_inter_subset_head.
Print Assumptions hfs_list_big_inter_subset_member.
Print Assumptions hfs_mem_list_product_iff.
Print Assumptions hfs_mem_list_domain_iff.
Print Assumptions hfs_mem_list_range_iff.
Print Assumptions hfs_list_big_union_existsUnique.
Print Assumptions hfs_list_big_inter_existsUnique.
Print Assumptions hfs_list_product_existsUnique.
Print Assumptions hfs_list_product_empty_left.
Print Assumptions hfs_list_product_empty_right.
Print Assumptions hfs_list_product_app_left.
Print Assumptions hfs_list_product_app_right.
Print Assumptions hfs_list_product_singleton.
Print Assumptions hfs_list_domain_existsUnique.
Print Assumptions hfs_list_range_existsUnique.
Print Assumptions hfs_list_domain_empty.
Print Assumptions hfs_list_range_empty.
Print Assumptions hfs_list_domain_app.
Print Assumptions hfs_list_range_app.
Print Assumptions hfs_list_domain_singleton.
Print Assumptions hfs_list_range_singleton.
Print Assumptions hfs_mem_list_image_iff.
Print Assumptions hfs_list_image_existsUnique.
Print Assumptions hfs_list_image_empty.
Print Assumptions hfs_list_image_cons.
Print Assumptions hfs_list_image_app.
Print Assumptions hfs_list_image_subset_of_subset.
Print Assumptions hfs_list_restrict_In_iff.
Print Assumptions hfs_mem_list_restrict_code_iff.
Print Assumptions hfs_list_restrict_code_empty.
Print Assumptions hfs_list_restrict_code_subset.
Print Assumptions hfs_list_domain_restrict_code.
Print Assumptions hfs_list_domain_restrict_code_of_subset.
Print Assumptions hfs_list_is_mapping_restrict.
Print Assumptions hfs_list_is_mapping_app.
Print Assumptions hfs_list_is_mapping_singleton.
Print Assumptions hfs_list_is_mapping_of_subset.
Print Assumptions hfs_list_is_mapping_cons_fresh.
Print Assumptions hfs_list_skolem_exists.
Print Assumptions hfs_list_mapping_fiber_existsUnique.
Print Assumptions hfs_list_compose_In_iff.
Print Assumptions hfs_mem_list_identity_iff.
Print Assumptions hfs_list_is_mapping_identity.
Print Assumptions hfs_list_is_injective_identity.
Print Assumptions hfs_list_compose_is_mapping.
Print Assumptions hfs_list_compose_is_injective.
Print Assumptions hfs_list_compose_assoc_In_iff.
Print Assumptions hfs_mem_code_elements_iff.
Print Assumptions hfs_code_elements_arithmetize.
Print Assumptions hfs_code_elements_nonempty_of_mem.
Print Assumptions hfs_mem_code_elements.
Print Assumptions hfs_code_elements_nodup.
Print Assumptions hfs_mem_code_big_union_iff.
Print Assumptions hfs_code_big_union_existsUnique.
Print Assumptions hfs_code_big_union_empty.
Print Assumptions hfs_code_big_union_subset_of_subset.
Print Assumptions hfs_mem_code_big_inter_iff.
Print Assumptions hfs_code_big_inter_existsUnique.
Print Assumptions hfs_mem_code_product_iff.
Print Assumptions hfs_code_product_existsUnique.
Print Assumptions hfs_code_product_empty_left.
Print Assumptions hfs_code_product_empty_right.
Print Assumptions hfs_mem_code_domain_iff.
Print Assumptions hfs_code_domain_existsUnique.
Print Assumptions hfs_code_domain_empty.
Print Assumptions hfs_mem_code_range_iff.
Print Assumptions hfs_code_range_existsUnique.
Print Assumptions hfs_code_range_empty.
Print Assumptions hfs_mem_code_image_iff.
Print Assumptions hfs_code_image_existsUnique.
Print Assumptions hfs_code_image_empty.
Print Assumptions hfs_code_image_union.
Print Assumptions hfs_code_image_insert.
Print Assumptions hfs_code_image_subset_of_subset.
Print Assumptions hfs_mem_code_image2_iff.
Print Assumptions hfs_code_image2_existsUnique.
Print Assumptions hfs_mem_code_restrict_iff.
Print Assumptions hfs_code_restrict_subset.
Print Assumptions hfs_code_restrict_empty.
Print Assumptions hfs_code_domain_restrict.
Print Assumptions hfs_code_domain_restrict_of_subset.
Print Assumptions hfs_code_domain_union.
Print Assumptions hfs_code_is_mapping_union_of_disjoint.
Print Assumptions hfs_code_is_mapping_insert_fresh.
Print Assumptions hfs_code_is_mapping_empty.
Print Assumptions hfs_code_is_mapping_singleton.
Print Assumptions hfs_code_is_mapping_of_subset.
Print Assumptions hfs_code_is_mapping_restrict.
Print Assumptions hfs_code_skolem_exists.
Check hfs_pr_construction.
Check hfs_pr_result.
Print Assumptions hfs_pr_result_zero.
Print Assumptions hfs_pr_result_succ.
Check hfs_pr_trace.
Print Assumptions hfs_pr_trace_length.
Print Assumptions hfs_pr_trace_nth.
Print Assumptions hfs_pr_trace_last.
Print Assumptions hfs_pr_trace_mem.
Check hfs_pr_computation.
Print Assumptions hfs_pr_trace_computation.
Print Assumptions hfs_pr_computation_value.
Print Assumptions hfs_pr_computations_agree.
Print Assumptions hfs_pr_computation_eq_trace.
Check hfs_pr_result_graph.
Print Assumptions hfs_pr_result_graph_iff.
Print Assumptions hfs_pr_result_graph_functional.
Print Assumptions hfs_pr_result_graph_exists_unique.
Check hfs_fp_construction.
Check hfs_fp_finite.
Check hfs_fp_strong_finite.
Check hfs_collect_below.
Print Assumptions hfs_mem_collect_below_iff.
Check hfs_restrict_below.
Print Assumptions hfs_mem_restrict_below_iff.
Check hfs_prefix_codes.
Print Assumptions hfs_in_prefix_codes_iff.
Print Assumptions hfs_fp_strong_finite_implies_finite.
Check hfs_fp_successor.
Check hfs_fp_stage.
Print Assumptions hfs_fp_mem_successor_iff.
Print Assumptions hfs_fp_mem_stage_succ_iff.
Print Assumptions hfs_fp_stage_cumulative.
Check hfs_fp_fixedpoint.
Print Assumptions hfs_fp_unfold.
Print Assumptions hfs_fp_mem_stage_self.
Print Assumptions hfs_fp_fixedpoint_iff_self_stage.
Print Assumptions hfs_fp_finite_upper_stage.
Print Assumptions hfs_fp_case.
Print Assumptions hfs_fp_induction.
Print Assumptions nat_positive_successor_induction.
Print Assumptions nat_bounded_order_induction.
Print Assumptions nat_bounded_order_induction_unary.
Print Assumptions nat_bounded_order_induction_two_parameters.
Print Assumptions nat_bounded_order_induction_three_parameters.
Print Assumptions nat_bounded_order_induction_family.
Print Assumptions nat_measure_induction.
Print Assumptions nat_measured_bounded_order_induction.
Print Assumptions nat_measured_numeric_bounded_order_induction.
Print Assumptions nat_disjunctive_successor_induction.
Print Assumptions nat_disjunctive_order_induction.
Print Assumptions nat_indexed_disjunctive_order_induction.
Check hfs_vector_adjoin_code.
Check hfs_vector_code_list.
Print Assumptions hfs_vector_adjoin_code_injective.
Print Assumptions hfs_vector_code_list_injective.
Check hfs_vector_fst_code.
Check hfs_vector_snd_code.
Print Assumptions hfs_vector_fst_adjoin_code.
Print Assumptions hfs_vector_snd_adjoin_code.
Print Assumptions hfs_vector_head_lt_adjoin_code.
Print Assumptions hfs_vector_tail_lt_adjoin_code.
Print Assumptions hfs_vector_adjoin_code_monotone.
Print Assumptions hfs_vector_raw_cases.
Check hfs_vector_decode_nat.
Print Assumptions hfs_vector_code_decode_nat.
Check hfs_vector.
Check hfs_vector_code.
Print Assumptions hfs_vector_code_adjoin.
Check hfs_vector_decode.
Print Assumptions hfs_vector_code_decode.
Print Assumptions hfs_vector_decode_code.
Print Assumptions hfs_vector_code_surjective.
Check hfs_vector_empty.
Check hfs_vector_adjoin.
Check hfs_vector_head.
Check hfs_vector_tail.
Check hfs_vector_nth.
Check hfs_vector_length.
Print Assumptions hfs_vector_code_injective.
Print Assumptions hfs_vector_adjoin_injective.
Print Assumptions hfs_vector_cases.
Print Assumptions hfs_vector_induction.
Print Assumptions hfs_vector_nth_empty.
Print Assumptions hfs_vector_nth_adjoin_zero.
Print Assumptions hfs_vector_nth_adjoin_succ.
Print Assumptions hfs_vector_length_zero_iff.
Print Assumptions hfs_vector_nth_out_of_range.
Print Assumptions hfs_vector_bounded_extensionality.
Print Assumptions hfs_vector_length_le_code.
Print Assumptions hfs_vector_nth_lt_code.
Print Assumptions hfs_vector_nth_le_code.
Print Assumptions hfs_vector_code_pointwise_monotone.
Print Assumptions hfs_vector_decode_adjoin_code.
Check hfs_vector_raw_length.
Check hfs_vector_raw_nth.
Print Assumptions hfs_vector_raw_length_adjoin.
Print Assumptions hfs_vector_raw_length_code.
Print Assumptions hfs_vector_raw_length_zero_iff.
Print Assumptions hfs_vector_raw_nth_adjoin_zero.
Print Assumptions hfs_vector_raw_nth_adjoin_succ.
Print Assumptions hfs_vector_raw_nth_le.
Print Assumptions hfs_vector_raw_nth_lt_nonzero.
Check hfs_vector_singleton.
Check hfs_vector_doubleton.
Print Assumptions hfs_vector_length_one_iff.
Print Assumptions hfs_vector_length_two_iff.
Check hfs_vector_tabulate.
Print Assumptions hfs_vector_tabulate_length.
Print Assumptions hfs_vector_tabulate_nth.
Print Assumptions hfs_vector_constructive_skolem.
Check hfs_vector_recursion.
Check hfs_vector_rec.
Print Assumptions hfs_vector_rec_empty.
Print Assumptions hfs_vector_rec_adjoin_law.
Print Assumptions hfs_vector_rec_unique.
Check hfs_vector_max.
Print Assumptions hfs_vector_max_adjoin.
Print Assumptions hfs_vector_nth_le_max.
Print Assumptions hfs_vector_max_le_iff.
Check hfs_vector_take_last.
Print Assumptions hfs_vector_take_last_adjoin.
Print Assumptions hfs_vector_take_last_length.
Print Assumptions hfs_vector_take_last_all.
Print Assumptions hfs_vector_take_last_nth.
Print Assumptions hfs_vector_take_last_succ.
Check hfs_vector_snoc.
Check hfs_vector_concat.
Print Assumptions hfs_vector_concat_adjoin.
Print Assumptions hfs_vector_concat_length.
Print Assumptions hfs_vector_concat_nth_old.
Print Assumptions hfs_vector_concat_nth_last.
Check hfs_vector_mem.
Print Assumptions hfs_vector_mem_iff_nth.
Print Assumptions hfs_vector_mem_lt_code.
Print Assumptions hfs_vector_nth_mem.
Print Assumptions hfs_vector_mem_adjoin_iff.
Check hfs_vector_subset.
Print Assumptions hfs_vector_subset_empty.
Print Assumptions hfs_vector_subset_trans.
Print Assumptions hfs_vector_subset_adjoin_iff.
Check hfs_vector_repeat.
Print Assumptions hfs_vector_repeat_length.
Print Assumptions hfs_vector_repeat_nth.
Print Assumptions hfs_vector_mem_repeat_iff.
Print Assumptions hfs_vector_repeat_length_le_code.
Print Assumptions hfs_vector_code_le_repeat.
Check hfs_vector_to_set.
Print Assumptions hfs_vector_to_set_adjoin.
Print Assumptions hfs_mem_vector_to_set_iff_nth.
Print Assumptions hfs_vector_nth_mem_to_set.
Print Assumptions hfs_vector_to_set_subset_iff.
Check hfs_vector_as_sequence.
Print Assumptions hfs_vector_as_sequence_length.
Print Assumptions hfs_vector_as_sequence_nth.

(* SetTheory/Ordinal.v: generalized transitive-set and ordinal surface. *)
Check z_is_transitive.
Check z_is_transitive_mem_trans.
Print Assumptions z_is_transitive_successor.
Print Assumptions z_is_transitive_union.
Print Assumptions z_is_transitive_sunion.
Print Assumptions z_is_transitive_sinter.
Print Assumptions z_is_transitive_omega.
Check z_is_ordinal.
Print Assumptions z_ordinal_of_mem.
Print Assumptions z_is_ordinal_successor.
Print Assumptions z_ordinal_nat.
Print Assumptions z_ordinal_mem_of_strict_subset.
Print Assumptions z_ordinal_strict_subset_iff.
Print Assumptions z_ordinal_subset_iff.
Print Assumptions z_ordinal_mem_iff_subset_and_not_subset.
Print Assumptions z_ordinal_subset_or_supset.
Print Assumptions z_ordinal_mem_trichotomy.
Print Assumptions z_ordinal_of_transitive.
Print Assumptions z_is_ordinal_omega.
Print Assumptions z_ordinal_sunion.
Print Assumptions z_ordinal_sinter.
Print Assumptions z_ordinal_empty_mem_iff_nonempty.
Check z_ordinal.
Check z_ordinal_lt.
Check z_ordinal_le.
Print Assumptions z_ordinal_lt_irrefl.
Print Assumptions z_ordinal_lt_trans.
Print Assumptions z_ordinal_le_antisym.
Print Assumptions z_ordinal_le_total.
Print Assumptions z_ordinal_lt_iff_le_and_not_ge.
Print Assumptions z_ordinal_le_iff_eq_or_lt.
Print Assumptions z_ordinal_pos_iff_nonempty.
Print Assumptions z_ordinal_eq_bottom_or_pos.
Print Assumptions z_ordinal_lt_succ.
Print Assumptions z_ordinal_sinter_mem.
Print Assumptions z_ordinal_minimal_prop_of_exists_aux.
Print Assumptions z_ordinal_minimal_lt_of_exists.
Print Assumptions z_ordinal_minimal_prop_of_exists.
Print Assumptions z_ordinal_minimal_le_of_exists_aux.
Print Assumptions z_ordinal_minimal_le_of_exists.
Print Assumptions z_ordinal_exists_minimal.
Print Assumptions z_ordinal_transfinite_induction.
Check z_is_well_founded_rel.
Print Assumptions z_membership_well_founded.
Check z_set_like.
Print Assumptions z_set_like_left_exists_unique.
Print Assumptions z_set_like_left_exists.
Print Assumptions z_set_like_mem_left.

(* FirstOrder/Skolemization/Hull.v: semantic Skolem functions and hull. *)
Check skolem_language.
Check skolem_structure.
Print Assumptions skolem_structure_func_spec.
Check skolem_hull.
Print Assumptions skolem_hull_subset.
Print Assumptions skolem_hull_closed.
Print Assumptions skolem_graph_exists.
Print Assumptions skolem_hull_closed_func.
Check skolem_hull_structure.
Print Assumptions skolem_hull_semiterm_val.
Print Assumptions skolem_hull_closed_semiterm_val.
Print Assumptions skolem_hull_semiformula_eval.
Print Assumptions skolem_hull_nonempty.
Print Assumptions skolem_hull_elementary_equiv.
Print Assumptions skolem_hull_structure_interprets_eq.

(* FirstOrder/SetTheory/LoewenheimSkolem.v: set-theoretic hull wrappers. *)
Check set_theory_eq_operator.
Print Assumptions set_standard_structure_interprets_eq.
Check set_hull.
Print Assumptions set_hull_subset.
Print Assumptions set_hull_closed.
Print Assumptions set_hull_models_iff.
Print Assumptions set_hull_nonempty.
Print Assumptions set_hull_elementary_equiv.

(* FirstOrder/Interpretation.v: semantic direct-interpretation core. *)
Check direct_translation.
Check direct_translation_realization.
Print Assumptions direct_translation_domain_nonempty.
Print Assumptions direct_translation_func_defined.
Print Assumptions direct_translation_preserve_eq.
Check direct_translation_model_carrier.
Print Assumptions direct_translation_model_func_val_spec.
Check direct_translation_model_structure.
Print Assumptions direct_translation_model_structure_rel.
Print Assumptions direct_translation_model_func_iff.
Print Assumptions direct_translation_model_func_iff'.
Print Assumptions direct_translation_model_semiterm_val_domain.
Print Assumptions direct_translation_model_atomic_iff.
Print Assumptions direct_translation_model_nonempty.
Print Assumptions direct_translation_model_interprets_eq.

(* FirstOrder/Bootstrapping/DerivabilityCondition/EquationalTheory.v:
   semantic equality replacement core. *)
Check bootstrapping_term_replace.
Print Assumptions bootstrapping_term_replace.
Check bootstrapping_formula_replace.
Print Assumptions bootstrapping_formula_replace.
Check bootstrapping_formula_replace_forward.

(* FirstOrder/Bootstrapping/DerivabilityCondition/PeanoMinus.v:
   semantic PA-minus order lemmas used by numeral bootstrapping. *)
Check peano_minus_boot_lt_add_self_add_one.
Print Assumptions peano_minus_boot_lt_add_self_add_one.
Check peano_minus_boot_lt_succ_iff_eq_or_lt.
Print Assumptions peano_minus_boot_lt_succ_iff_eq_or_lt.

(* FirstOrder/Incompleteness/StandardProvability.v: finite-context
   derivability-condition adapters. *)
Check boot_standard_provability.
Print Assumptions boot_standard_provability_of_code.
Print Assumptions boot_standard_provability_of_code_iff_theory.
Print Assumptions boot_standard_sigma_one_provable_iff.
Check boot_context_proof.
Check boot_context_provable.
Print Assumptions boot_context_weaken.
Print Assumptions boot_context_modus_ponens_raw.
Print Assumptions boot_context_modus_ponens.
Print Assumptions boot_context_D2.
Print Assumptions boot_context_D3.
