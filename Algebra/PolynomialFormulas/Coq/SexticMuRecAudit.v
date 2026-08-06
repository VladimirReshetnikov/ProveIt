(* ===================================================================== *)
(*  Compact kernel audit for the concrete Mu-recursive sextic pipeline.  *)
(*                                                                       *)
(*  The checks below keep the vector, one-code, graph-computability, and  *)
(*  semantic interfaces visible in one place, including the closed core  *)
(*  exactness theorem consumed by the public wrappers.                    *)
(* ===================================================================== *)

From PolynomialFormulas Require Import
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecQuinticResolvent SexticMuRecCollisionEvaluator
  SexticMuRecResolventRootEvaluator SexticMuRecFinalAssembly
  SexticMuRecIrreducibleAssembly SexticMuRecCompleteDecision
  SexticMuRecConcreteDecision SexticMuRecCoreExactness
  SexticMuRecVerifiedDecision.

Module PolynomialFormulasSexticMuRecAudit.

Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module QR := PolynomialFormulasSexticMuRecQuinticResolvent.
Module CE := PolynomialFormulasSexticMuRecCollisionEvaluator.
Module RE := PolynomialFormulasSexticMuRecResolventRootEvaluator.
Module FA := PolynomialFormulasSexticMuRecFinalAssembly.
Module IA := PolynomialFormulasSexticMuRecIrreducibleAssembly.
Module CD := PolynomialFormulasSexticMuRecCompleteDecision.
Module CC := PolynomialFormulasSexticMuRecConcreteDecision.
Module CX := PolynomialFormulasSexticMuRecCoreExactness.
Module VD := PolynomialFormulasSexticMuRecVerifiedDecision.

(* --------------------------------------------------------------------- *)
(* Proper-factor decision: six-vector and one-natural graph interfaces.  *)

Check ra_encoded_monic_has_proper_factor.
Check encoded_monic_proper_factor_relation.
Check FD.sextic_monic_factor_relation.
Check FD.sextic_monic_factor_relation_murec.
Check ra_encoded_monic_proper_factor_code.
Check encoded_monic_proper_factor_code_relation.
Check FD.sextic_monic_factor_code_relation.
Check FD.sextic_monic_factor_code_relation_murec.
Check FD.encoded_monic_has_proper_factorb_mathcomp.
Check FD.sextic_monic_factor_relation_mathcomp.
Check FD.sextic_monic_factor_code_relation_mathcomp.

(* --------------------------------------------------------------------- *)
(* Padded-quintic resolvent and its vector/one-natural decisions.         *)

Check QR.ra_quintic_resolvent_coefficient_vector.
Check QR.quintic_resolvent_coefficient_vector_relation.
Check QR.quintic_resolvent_coefficient_vector_relation_murec.
Check QR.ra_quintic_resolvent_root.
Check QR.quintic_resolvent_root_relation.
Check QR.quintic_resolvent_root_relation_murec.
Check QR.ra_quintic_resolvent_root_code.
Check QR.quintic_resolvent_root_code_relation.
Check QR.quintic_resolvent_root_code_relation_murec.
Check QR.ra_encoded_monic_quintic_radical.
Check QR.encoded_monic_quintic_radical_relation.
Check QR.encoded_monic_quintic_radical_relation_murec.
Check QR.ra_encoded_monic_quintic_radical_code.
Check QR.encoded_monic_quintic_radical_code_relation.
Check QR.encoded_monic_quintic_radical_code_relation_murec.
Check QR.encoded_monic_quintic_radicalb_QCD.
Check QR.encoded_monic_quintic_radical_relation_QCD.
Check QR.encoded_monic_quintic_radical_code_relation_QCD.

(* --------------------------------------------------------------------- *)
(* Pair/triple collision evaluators and projected arity-seven programs.  *)

Check CE.ra_newton_sparse_term.
Check CE.newton_sparse_term_relation.
Check CE.newton_sparse_term_relation_murec.
Check CE.ra_pair_scaled_collision_value.
Check CE.ra_pair_scaled_collision_value_correct.
Check CE.ra_pair_collision_test.
Check CE.ra_pair_collision_test_correct.
Check CE.ra_pair_projected_collision_test.
Check CE.ra_pair_projected_collision_test_correct.
Check CE.ra_triple_scaled_collision_value.
Check CE.ra_triple_scaled_collision_value_correct.
Check CE.ra_triple_collision_test.
Check CE.ra_triple_collision_test_correct.
Check CE.ra_triple_projected_collision_test.
Check CE.ra_triple_projected_collision_test_correct.

(* --------------------------------------------------------------------- *)
(* Pair/triple rational-root evaluators.                                 *)

Check RE.encoded_pair_resolvent_rootb.
Check RE.ra_pair_resolvent_root.
Check RE.ra_pair_resolvent_root_correct.
Check RE.ra_pair_resolvent_root_primitive_recursive.
Check RE.encoded_triple_resolvent_rootb.
Check RE.ra_triple_resolvent_root.
Check RE.ra_triple_resolvent_root_correct.
Check RE.ra_triple_resolvent_root_primitive_recursive.

(* --------------------------------------------------------------------- *)
(* Reducible dispatcher and generic raw front end.                       *)

Check FA.ra_encoded_monic_reducible_radical.
Check FA.encoded_monic_reducible_radical_relation.
Check FA.encoded_monic_reducible_radical_relation_murec.
Check FA.ra_encoded_monic_reducible_radical_code.
Check FA.encoded_monic_reducible_radical_code_relation.
Check FA.encoded_monic_reducible_radical_code_relation_murec.
Check FA.encoded_monic_reducible_radicalP.
Check FA.ra_encoded_raw_sextic_radical.
Check FA.encoded_raw_sextic_radical_relation.
Check FA.encoded_raw_sextic_radical_relation_murec.
Check FA.ra_encoded_raw_sextic_radical_code.
Check FA.encoded_raw_sextic_radical_code_relation.
Check FA.encoded_raw_sextic_radical_code_relation_murec.
Check FA.encoded_raw_sextic_radicalP.

(* --------------------------------------------------------------------- *)
(* Generic irreducible assembly: selected search, vector, and one-code.   *)

Check IA.ra_selected_projected_index.
Check IA.selected_projected_index_relation.
Check IA.selected_projected_index_relation_murec.
Check IA.ra_encoded_irreducible_resolvent.
Check IA.encoded_irreducible_resolvent_relation.
Check IA.encoded_irreducible_resolvent_relation_murec.
Check IA.ra_encoded_irreducible_resolvent_code.
Check IA.encoded_irreducible_resolvent_code_relation.
Check IA.encoded_irreducible_resolvent_code_relation_murec.
Check IA.encoded_irreducible_resolventb_mathcomp.
Check IA.encoded_irreducible_resolventP.

(* --------------------------------------------------------------------- *)
(* Complete generic monic and raw decisions.                             *)

Check CD.ra_encoded_monic_sextic_radical.
Check CD.encoded_monic_sextic_radical_relation.
Check CD.encoded_monic_sextic_radical_relation_murec.
Check CD.ra_encoded_monic_sextic_radical_code.
Check CD.encoded_monic_sextic_radical_code_relation.
Check CD.encoded_monic_sextic_radical_code_relation_murec.
Check CD.encoded_monic_sextic_radicalP.
Check CD.ra_encoded_raw_sextic_radical.
Check CD.encoded_raw_sextic_radical_relation.
Check CD.encoded_raw_sextic_radical_relation_murec.
Check CD.ra_encoded_raw_sextic_radical_code.
Check CD.encoded_raw_sextic_radical_code_relation.
Check CD.encoded_raw_sextic_radical_code_relation_murec.
Check CD.encoded_raw_sextic_radicalP.
Check CD.encoded_raw_sextic_radical_codeP.

(* --------------------------------------------------------------------- *)
(* Concrete evaluator package and current public endpoints.              *)

Check CC.decode_encode_monic_sextic_coefficients.
Check CC.encode_decode_monic_sextic_coefficients.
Check CC.pair_collision_program.
Check CC.pair_collision_program_correct.
Check CC.triple_collision_program.
Check CC.triple_collision_program_correct.
Check CC.pair_root_program.
Check CC.pair_root_program_correct.
Check CC.triple_root_program.
Check CC.triple_root_program_correct.
Check CC.core_semantic_exactness.
Check CC.pair_guarded_projected_eventually.
Check CC.triple_guarded_projected_eventually.
Check CC.ra_encoded_monic_sextic_radical.
Check CC.encoded_monic_sextic_radical_relation.
Check CC.encoded_monic_sextic_radical_relation_murec.
Check CC.encoded_monic_sextic_radicalP.
Check CC.ra_encoded_raw_sextic_radical.
Check CC.encoded_raw_sextic_radical_relation.
Check CC.encoded_raw_sextic_radical_relation_murec.
Check CC.ra_encoded_raw_sextic_radical_code.
Check CC.encoded_raw_sextic_radical_code_relation.
Check CC.encoded_raw_sextic_radical_code_relation_murec.
Check CC.encoded_raw_sextic_radicalP.
Check CC.encoded_raw_sextic_radical_codeP.

(* --------------------------------------------------------------------- *)
(* Closed exactness package and parameter-free public endpoints.         *)

Check CX.verified_core_semantic_exactness.
Check VD.verified_core_semantic_exactness.
Check VD.pair_eventually.
Check VD.triple_eventually.

Check VD.encoded_monic_sextic_radicalb.
Check VD.ra_encoded_monic_sextic_radical.
Check VD.ra_encoded_monic_sextic_radical_correct.
Check VD.encoded_monic_sextic_radical_relation.
Check VD.encoded_monic_sextic_radical_relation_murec.
Check VD.encoded_monic_sextic_radicalb_mathcomp.
Check VD.encoded_monic_sextic_radical_canonicalP.
Check VD.encoded_monic_sextic_radicalP.
Check VD.encoded_monic_sextic_radical_decidable.

Check VD.encoded_monic_sextic_radical_codeb.
Check VD.ra_encoded_monic_sextic_radical_code.
Check VD.ra_encoded_monic_sextic_radical_code_correct.
Check VD.encoded_monic_sextic_radical_code_relation.
Check VD.encoded_monic_sextic_radical_code_relation_murec.
Check VD.encoded_monic_sextic_radical_codeP.
Check VD.encoded_monic_sextic_radical_code_decidable.

Check VD.encoded_raw_sextic_radicalb.
Check VD.ra_encoded_raw_sextic_radical.
Check VD.ra_encoded_raw_sextic_radical_correct.
Check VD.encoded_raw_sextic_radical_relation.
Check VD.encoded_raw_sextic_radical_relation_murec.
Check VD.encoded_raw_sextic_radicalb_mathcomp.
Check VD.encoded_raw_sextic_radicalP.
Check VD.encoded_raw_sextic_radical_decidable.

Check VD.encoded_raw_sextic_radical_codeb.
Check VD.ra_encoded_raw_sextic_radical_code.
Check VD.ra_encoded_raw_sextic_radical_code_correct.
Check VD.encoded_raw_sextic_radical_code_relation.
Check VD.encoded_raw_sextic_radical_code_relation_murec.
Check VD.encoded_raw_sextic_radical_codeP.
Check VD.encoded_raw_sextic_radical_code_decidable.

End PolynomialFormulasSexticMuRecAudit.

(* --------------------------------------------------------------------- *)
(* Minimal deep audit.  Broad interface coverage stays above as [Check]s; *)
(* only the final public terms are recursively traversed here.            *)

(* Exactness and both graph-computability results must be kernel-closed. *)
Print Assumptions
  PolynomialFormulasSexticMuRecCoreExactness.verified_core_semantic_exactness.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.verified_core_semantic_exactness.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_code_relation_murec.

(* The final reflectors and constructive decisions may use only the         *)
(* existing classical semantic bridge, never an evaluator assumption.       *)
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_codeP.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_decidable.
Print Assumptions
  PolynomialFormulasSexticMuRecVerifiedDecision.encoded_raw_sextic_radical_code_decidable.
