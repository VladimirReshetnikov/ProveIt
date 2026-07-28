(**
  The carrier-level induction shell for the derivation-soundness template.

  [RawCodedRestrictedPAConsistencyFromUniversalSoundness] fixes an honest
  finite template for the model-internal soundness predicate.  This module
  performs only the deterministic syntactic part of ordinary PA induction
  on that predicate: shift the induction variable, form its successor and
  zero instances, and assemble the induction body.

  Three genuinely nonstandard operations are intentionally retained as the
  explicit [RawCoqRestrictedPADerivationSoundnessClosureRemainder]: a bound
  for the assembled body, its represented universal closure, and enough
  diagonal substitutions to reduce that closure.  Neither these operations
  nor PA proofs of the zero and successor cases can be inferred merely from
  the finite template.  In particular, this module does not confuse a
  standard metatheoretic formula with an arbitrary carrier-coded one.

  The final theorem packages supplied case proofs as an ordinary PA proof
  certificate.  That shape matters downstream: the certificate can be
  merged into a witnessed base context before the canonical existential
  descent is rebuilt, instead of attempting to remove the newly introduced
  induction axiom from a local context.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedPAAxiomWitness
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateStructuralPAAgreement
  RawCodedPAInductionAxiomCertificate
  RawCodedPAUniversalClosureProofReduction
  RawCodedPAClosureInductionCompiler
  RawCodedRestrictedPAConsistencyFromUniversalSoundness.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierInductionShell.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateStructuralPAAgreement.
Import PABoundedRawCodedPAInductionAxiomCertificate.
Import PABoundedRawCodedPAUniversalClosureProofReduction.
Import PABoundedRawCodedPAClosureInductionCompiler.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

(** The structural shift tree is already indexed by every external depth.
    The older public corollary specializes it to depth zero; induction needs
    the equally direct depth-one instance.  Exposing the general lemma here
    avoids any appeal to standard-formula quotation. *)
Theorem rawStructuralTemplateFormula_shiftAt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M) depth formula,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawStructuralTemplateFormula inputs formula)
    (rawStructuralTemplateFormula inputs
      (templateFormulaRename
        (templateShiftRenamingAt depth) formula)).
Proof.
  intros M hPA inputs depth formula.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA
    (rawNumeralValue M 1)
    (rawStructuralTemplateShiftTree inputs depth formula)
    (rawStructuralTemplateShiftTree_valid
      M inputs depth formula)) as hshift.
  rewrite rawStructuralTemplateShiftTree_depth in hshift.
  rewrite rawStructuralTemplateShiftTree_source in hshift.
  rewrite rawStructuralTemplateShiftTree_target in hshift.
  exact hshift.
Qed.

(** ------------------------------------------------------------------
    The exact finite induction templates. *)

Definition coqRestrictedPADerivationSoundnessCarrierInductionSourceTemplate
    : TemplateFormula :=
  coqRestrictedPADerivationSoundnessPredicateTemplate.

Definition coqRestrictedPADerivationSoundnessCarrierInductionShiftedTemplate
    : TemplateFormula :=
  templateFormulaRename (templateShiftRenamingAt 1)
    coqRestrictedPADerivationSoundnessCarrierInductionSourceTemplate.

Definition
    coqRestrictedPADerivationSoundnessCarrierInductionSuccessorTemplate
    : TemplateFormula :=
  templateFormulaOpen (embedPATerm (tSucc (tVar 0)))
    coqRestrictedPADerivationSoundnessCarrierInductionShiftedTemplate.

Definition coqRestrictedPADerivationSoundnessCarrierInductionZeroTemplate
    : TemplateFormula :=
  templateFormulaOpen (embedPATerm tZero)
    coqRestrictedPADerivationSoundnessCarrierInductionSourceTemplate.

(** ------------------------------------------------------------------
    Their raw carrier codes.  Compound codes use the public raw syntax
    constructors, so the corresponding induction-data equations are small
    definitional equalities. *)

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawCoqRestrictedPADerivationSoundnessPredicateCode M inputs.

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionShiftedCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierInductionShiftedTemplate.

Definition
    rawCoqRestrictedPADerivationSoundnessCarrierInductionSuccessorCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierInductionSuccessorTemplate.

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawStructuralTemplateFormula inputs
    coqRestrictedPADerivationSoundnessCarrierInductionZeroTemplate.

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceAllCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs.

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionStepImpCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSuccessorCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAllCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepImpCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionPremiseCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaAndCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
      M inputs).

Definition rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M) : M :=
  rawFormulaImpCode M
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceAllCode
      M inputs).

Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionShiftedCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionSuccessorCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceAllCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionStepImpCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionPremiseCode
  M inputs : clear implicits.
Arguments rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
  M inputs : clear implicits.

(** These are precisely the three fields which structural recursion over a
    finite template does not settle for arbitrary carrier values. *)
Definition RawCoqRestrictedPADerivationSoundnessClosureRemainder
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    (replacement axiom closureCount : M) : Prop :=
  RawCodedFormulaBound M
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
      M inputs)
    closureCount /\
  RawCodedUniversalClosure M closureCount
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
      M inputs)
    axiom /\
  RawCodedUniversalClosureSelfInstantiationThrough M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
      M inputs)
    closureCount.

Arguments RawCoqRestrictedPADerivationSoundnessClosureRemainder
  M inputs replacement axiom closureCount : clear implicits.

(** Assemble all eleven fields of the generic induction interface.  The
    first eight are derived below; the final three are merely copied from
    the explicit remainder. *)
Theorem
    raw_coqRestrictedPADerivationSoundnessCarrierClosureInductionData :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M)
    replacement axiom closureCount,
  RawCoqRestrictedPADerivationSoundnessClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPAClosureInductionData M replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode
      M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
      M inputs)
    closureCount.
Proof.
  intros M hPA inputs replacement axiom closureCount
    [hbound [hclosure hself]].
  unfold RawCodedPAClosureInductionData.
  repeat apply conj.
  - unfold
      rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode,
      rawCoqRestrictedPADerivationSoundnessCarrierInductionShiftedCode,
      coqRestrictedPADerivationSoundnessCarrierInductionShiftedTemplate,
      coqRestrictedPADerivationSoundnessCarrierInductionSourceTemplate.
    rewrite raw_coqRestrictedPADerivationSoundnessPredicateCode_structural.
    exact (rawStructuralTemplateFormula_shiftAt M hPA inputs 1
      coqRestrictedPADerivationSoundnessPredicateTemplate).
  - rewrite <- (rawQuotedTermCode_standard M hPA
      (tSucc (tVar 0))).
    rewrite <- (rawStructuralTemplateTerm_embedPA M inputs
      (tSucc (tVar 0))).
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierInductionShiftedCode,
      rawCoqRestrictedPADerivationSoundnessCarrierInductionSuccessorCode,
      coqRestrictedPADerivationSoundnessCarrierInductionSuccessorTemplate.
    exact (rawStructuralTemplateFormula_open M hPA inputs
      coqRestrictedPADerivationSoundnessCarrierInductionShiftedTemplate
      (embedPATerm (tSucc (tVar 0)))).
  - rewrite <- (rawQuotedTermCode_standard M hPA tZero).
    rewrite <- (rawStructuralTemplateTerm_embedPA M inputs tZero).
    unfold
      rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode,
      rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode,
      coqRestrictedPADerivationSoundnessCarrierInductionZeroTemplate,
      coqRestrictedPADerivationSoundnessCarrierInductionSourceTemplate.
    rewrite raw_coqRestrictedPADerivationSoundnessPredicateCode_structural.
    exact (rawStructuralTemplateFormula_open M hPA inputs
      coqRestrictedPADerivationSoundnessPredicateTemplate
      (embedPATerm tZero)).
  - exact (raw_coqRestrictedPADerivationSoundnessUniversalCode_view
      M inputs).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact hbound.
  - exact hclosure.
  - exact hself.
Qed.

(** Conditional ordinary-proof packaging.  The hypotheses are deliberately
    the exact zero and successor roots required by ordinary induction; this
    theorem neither manufactures them nor weakens their extended context. *)
Theorem
    raw_codedPAProofOf_coqRestrictedPADerivationSoundnessUniversal_of_cases :
    forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateStructuralInputs M)
    replacement axiom closureCount baseWitnessList baseContext
    zeroChild stepChild,
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  RawCoqRestrictedPADerivationSoundnessClosureRemainder
    M inputs replacement axiom closureCount ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode
      M inputs)
    zeroChild ->
  RawCodedPALocalProofOf M
    (rawPAInductionExtendedContext M baseContext axiom)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
      M inputs)
    stepChild ->
  exists bodyChild : M,
    RawCodedPAProofOf M
      (rawCoqRestrictedPADerivationSoundnessUniversalCode M inputs)
      (rawPAClosureInductionCertificate M
        baseWitnessList baseContext
        (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode
          M inputs)
        axiom
        (rawCoqRestrictedPADerivationSoundnessCarrierInductionPremiseCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceAllCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode
          M inputs)
        (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
          M inputs)
        bodyChild zeroChild stepChild).
Proof.
  intros M hPA inputs replacement axiom closureCount
    baseWitnessList baseContext zeroChild stepChild
    hbase hremainder hzero hstep.
  exact (raw_codedPAProofOf_closure_induction M hPA
    baseWitnessList baseContext replacement
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceCode
      M inputs)
    axiom
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionShiftedCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSuccessorCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionZeroCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionSourceAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepImpCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionStepAllCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionPremiseCode
      M inputs)
    (rawCoqRestrictedPADerivationSoundnessCarrierInductionBodyCode
      M inputs)
    closureCount zeroChild stepChild hbase
    (raw_coqRestrictedPADerivationSoundnessCarrierClosureInductionData
      M hPA inputs replacement axiom closureCount hremainder)
    hzero hstep).
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessCarrierInductionShell.
