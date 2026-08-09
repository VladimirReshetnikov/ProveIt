(** Public-surface and assumption audit for the Sigma/Or fixed-production
    proof template. *)

From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedDynamicTruthSigmaOrFixedProductionTemplate.

Module PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplateAudit.

Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplate.

Check templateExistentialWitnessOpeningMany.
Check templateExistentialWitnessIntroductionFrom.
Check templateExistentialWitnessIntroductionFrom_derives.

Check coqDynamicTruthSigmaOrWitnessesAt.
Check coqDynamicTruthSigmaOrFixedProductionContextAt.
Check coqDynamicTruthSigmaOrOpenedLeafProofAt.
Check coqDynamicTruthSigmaOrOpenedBranchesProofAt.
Check coqDynamicTruthSigmaOrOpenedRowBodyProofAt.
Check coqDynamicTruthSigmaOrSuccessorRowProofAt.
Check coqDynamicTruthSigmaOrFixedProductionProofAt.

Check coqDynamicTruthSigmaOrOpenedLeafProofAt_derives.
Check coqDynamicTruthSigmaOrOpenedBranchesProofAt_derives.
Check coqDynamicTruthSigmaOrOpenedRowBodyProofAt_derives.
Check coqDynamicTruthSigmaOrSuccessorRowProofAt_derives.
Check coqDynamicTruthSigmaOrFixedProductionProofAt_derives.
Check raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production.

(** The indexed disjunction introduction really selects the fifth Sigma
    alternative (zero-based branch four), rather than merely producing an
    extensionally similar disjunction. *)
Goal forall witness7 witness6 witness5 witness4
    witness3 witness2 witness1 witness0,
  templateRightDisjunctionBranchAt
    (coqDynamicTruthSigmaOrOpenedBranchPrefixAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    (coqDynamicTruthSigmaOrOpenedUniversalAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0)
    4 =
  Some
    (coqDynamicTruthSigmaOrOpenedLeafAt
      witness7 witness6 witness5 witness4
      witness3 witness2 witness1 witness0).
Proof. intros. reflexivity. Qed.

Print Assumptions templateExistentialWitnessIntroductionFrom_derives.
Print Assumptions coqDynamicTruthSigmaOrOpenedRowBodyAt_exact.
Print Assumptions coqDynamicTruthSigmaOrFixedProductionProofAt_derives.
Print Assumptions
  raw_codedPALocalProofOf_dynamic_truth_sigma_or_fixed_production.

End PABoundedRawCodedDynamicTruthSigmaOrFixedProductionTemplateAudit.
