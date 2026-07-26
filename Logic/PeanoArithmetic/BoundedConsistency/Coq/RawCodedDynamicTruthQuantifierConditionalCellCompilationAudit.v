(** Audit of structural compilation for the conditional quantifier cells. *)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import HierarchyReduction.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateProjectionSchemas
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation.

Import ListNotations.

Module PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilationAudit.

Import PA.
Import PAHierarchyReduction.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.

(** Generic finite logical kernel. *)
Check templateRepeatedAllExistsCollisionProof.
Check templateRepeatedAllExistsCollisionProof_derives.
Check templateQuantifierConditionalCellProof.
Check templateQuantifierConditionalCellProof_derives.
Check templateQuantifierConditionalCellReversedProof.
Check templateQuantifierConditionalCellReversedProof_derives.

(** Exact native template instances. *)
Check coqDynamicTruthSigmaEx8BranchTemplate.
Check coqDynamicTruthPiExistentialCounterexampleTemplate.
Check coqDynamicTruthPiExistentialEx8BranchTemplate.
Check coqDynamicTruthSigmaExPiExConditionalCellTemplate.
Check coqDynamicTruthSigmaExPiExConditionalCellTemplateProof.
Check coqDynamicTruthSigmaExPiExConditionalCellTemplateProof_derives.
Check coqDynamicTruthSigmaUniversalCounterexampleTemplate.
Check coqDynamicTruthSigmaUniversalEx8BranchTemplate.
Check coqDynamicTruthPiAllEx8BranchTemplate.
Check coqDynamicTruthSigmaAllPiAllConditionalCellTemplate.
Check coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof.
Check coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof_derives.

Goal coqDynamicTruthSigmaExPiExConditionalCellTemplate =
  tfImp
    (tfImp
      (templateRepeatedExists 8 coqDynamicTruthSigmaExLeafTemplate)
      (templateRepeatedForall 8
        (tfImp coqDynamicTruthPiExistentialPrefixTemplate
          (templateRepeatedExists 3
            (tfAnd coqDynamicTruthPiBinderPrependTemplate
              coqDynamicTruthLowerSigmaAtomTemplate)))))
    (tfImp
      (templateRepeatedExists 8 coqDynamicTruthSigmaExLeafTemplate)
      (tfImp
        (templateRepeatedExists 8
          (tfAnd coqDynamicTruthPiExistentialPrefixTemplate
            (tfImp
              (templateRepeatedExists 3
                (tfAnd coqDynamicTruthPiBinderPrependTemplate
                  coqDynamicTruthLowerSigmaAtomTemplate))
              tfBot)))
        tfBot)).
Proof. reflexivity. Qed.

Goal coqDynamicTruthSigmaAllPiAllConditionalCellTemplate =
  tfImp
    (tfImp
      (templateRepeatedExists 8 coqDynamicTruthPiAllLeafTemplate)
      (templateRepeatedForall 8
        (tfImp coqDynamicTruthSigmaUniversalPrefixTemplate
          (templateRepeatedExists 3
            (tfAnd coqDynamicTruthSigmaBinderPrependTemplate
              coqDynamicTruthLowerPiAtomTemplate)))))
    (tfImp
      (templateRepeatedExists 8
        (tfAnd coqDynamicTruthSigmaUniversalPrefixTemplate
          (tfImp
            (templateRepeatedExists 3
              (tfAnd coqDynamicTruthSigmaBinderPrependTemplate
                coqDynamicTruthLowerPiAtomTemplate))
            tfBot)))
      (tfImp
        (templateRepeatedExists 8 coqDynamicTruthPiAllLeafTemplate)
        tfBot)).
Proof. reflexivity. Qed.

(** The exact carrier trace seam. *)
Check RawDynamicTruthQuantifierLowerApplicationDirectTrace.
Check rawDynamicTruthQuantifierLowerApplication_inputs.
Check rawDynamicTruthQuantifierLowerApplication_designated.
Check RawDynamicTruthQuantifierLowerApplicationDirectTraceTotal.
Check rawDynamicTruthQuantifierLowerApplication_sigma_designated.
Check rawDynamicTruthQuantifierLowerApplicationDirectTrace_of_native.
Check rawDynamicTruthQuantifierLowerApplicationDirectTrace_of_native_pi.
Check rawDirectTemplateFormula_quantifier_embedPA.
Check rawDirect_dynamicTruthSigmaExPiExConditionalCellTemplate_identified.
Check rawDirect_dynamicTruthSigmaAllPiAllConditionalCellTemplate_identified.

(** Represented PA certificates and conditional discharge of the original
    arbitrary-carrier compiler interface. *)
Check rawDynamicTruthQuantifierDirectTranslation.
Check rawDynamicTruthSigmaExPiExConditionalCellCertificate.
Check rawDynamicTruthSigmaAllPiAllConditionalCellCertificate.
Check raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_direct.
Check raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct.
Check
  rawDynamicTruthQuantifierConditionalCellCompilerTotal_of_directTraceTotal.

(** Existing-common-context adapters. *)
Check rawDynamicTruthSigmaExPiExConditionalCellLocalRoot.
Check rawDynamicTruthSigmaAllPiAllConditionalCellLocalRoot.
Check
  raw_codedPALocalProofOf_dynamicTruthSigmaExPiExConditionalCell_direct.
Check
  raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct.

(** Assumption audit: compilation is entirely through finite proof trees and
    represented operation traces, never semantic completeness. *)
Print Assumptions templateRepeatedAllExistsCollisionProof_derives.
Print Assumptions coqDynamicTruthSigmaExPiExConditionalCellTemplateProof_derives.
Print Assumptions coqDynamicTruthSigmaAllPiAllConditionalCellTemplateProof_derives.
Print Assumptions rawDirect_dynamicTruthSigmaExPiExConditionalCellTemplate_identified.
Print Assumptions rawDirect_dynamicTruthSigmaAllPiAllConditionalCellTemplate_identified.
Print Assumptions
  rawDynamicTruthQuantifierLowerApplicationDirectTrace_of_native.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthSigmaExPiExConditionalCell_direct.
Print Assumptions
  raw_codedPAProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct.
Print Assumptions
  rawDynamicTruthQuantifierConditionalCellCompilerTotal_of_directTraceTotal.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthSigmaExPiExConditionalCell_direct.
Print Assumptions
  raw_codedPALocalProofOf_dynamicTruthSigmaAllPiAllConditionalCell_direct.

End PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilationAudit.
