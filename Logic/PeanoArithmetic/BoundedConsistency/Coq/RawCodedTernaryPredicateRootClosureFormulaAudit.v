(** Kernel audit for the represented ternary-predicate root-closure formula. *)

From BoundedPAConsistency Require Import
  RawCodedTernaryPredicateRootClosureFormula.

Module PABoundedRawCodedTernaryPredicateRootClosureFormulaAudit.

Import PABoundedRawCodedTernaryPredicateRootClosureFormula.

Check codedTernaryPredicateRootClosedTermAt.
Check codedTernaryPredicateRootClosedFormula.

(** This lemma audits the three-binder de Bruijn lift used by the universal
    replacement clause. *)
Check raw_rootClosure_eval_liftTerm_three.

Check raw_sat_codedTernaryPredicateRootClosedTermAt_iff.
Check raw_sat_codedTernaryPredicateRootClosedFormula_iff.

Print Assumptions raw_rootClosure_eval_liftTerm_three.
Print Assumptions raw_sat_codedTernaryPredicateRootClosedTermAt_iff.
Print Assumptions raw_sat_codedTernaryPredicateRootClosedFormula_iff.

End PABoundedRawCodedTernaryPredicateRootClosureFormulaAudit.
