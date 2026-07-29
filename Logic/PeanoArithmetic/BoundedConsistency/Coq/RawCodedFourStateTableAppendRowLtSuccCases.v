(**
  Specialize the represented successor-bound split to an appended table row.

  The generic arithmetic compiler keeps a finite temporary template prefix
  above a witnessed PA tail.  The append compiler describes the same context
  operationally, by eliminating eight table witnesses and then introducing
  five row variables.  This module proves that their carrier context codes
  coincide and exposes the case disjunction in the latter, client-facing
  form.  No carrier-coded context or witness list is decoded.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedProof
  RawCodedSyntaxConstructors
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitnessPrefix
  RawCodedPALocalProofExistential
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplatePAEmbedding
  RawCodedTemplatePAEmbeddingSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedTemplateLocalProofStandardWitnessTailTransport
  RawCodedPALocalProofUniversalIntroductionChain
  RawCodedLtSuccCasesProofCompilation
  RawCodedFourStateTableAppendExistentialElimination.

Import ListNotations.

Module PABoundedRawCodedFourStateTableAppendRowLtSuccCases.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedProof.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplatePAEmbedding.
Import PABoundedRawCodedTemplatePAEmbeddingSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedTemplateLocalProofStandardWitnessTailTransport.
Import PABoundedRawCodedPALocalProofUniversalIntroductionChain.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedFourStateTableAppendExistentialElimination.

(** Agreement on embedded PA syntax identifies the metatheoretic witnessed
    template tail with its synchronized carrier-coded context. *)
Lemma raw_templateContextCode_embedPAAxiomWitnesses : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall witnesses,
  rawTemplateContextCode translation
    (embedPAContext (map witnessedAxiom witnesses)) =
  rawStandardPAAxiomWitnessPrefixContextCode M witnesses (raw_zero M).
Proof.
  intros M translation hagreement witnesses.
  rewrite raw_templateContextCode_as_on_tail_general.
  apply (raw_templateContextCodeOnTail_embedPAAxiomWitnesses
    M translation hagreement witnesses (raw_zero M)).
Qed.

(** Carrier-code form of the exact thirteen-assumption prefix equation. *)
Lemma raw_fourStateTableAppendRowContext_witnessed_tail_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses,
  rawTemplateContextCode translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        (embedPAContext (map witnessedAxiom witnesses)))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M
      witnesses (raw_zero M))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep).
Proof.
  intros M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep witnesses.
  rewrite coqFourStateTableAppendRowContext_witnessed_tail.
  rewrite raw_templateContextCode_app_on_tail_general.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement witnesses).
  reflexivity.
Qed.

(** Reassociate a newly selected standard witness batch with the caller's
    existing batch, while presenting the context through embedded templates. *)
Lemma raw_fourStateTableAppendRow_combined_witnessed_tail : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall extra witnesses,
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M extra
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M)))
    (rawStandardPAAxiomWitnessPrefixContextCode M extra
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))) ->
  RawCodedPAAxiomWitnessContext M
    (rawStandardPAAxiomWitnessPrefixWitnessListCode M
      (extra ++ witnesses) (raw_zero M))
    (rawTemplateContextCode translation
      (embedPAContext (map witnessedAxiom (extra ++ witnesses)))).
Proof.
  intros M translation hagreement extra witnesses hwitnessed.
  rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
  rewrite (raw_templateContextCode_embedPAAxiomWitnesses
    M translation hagreement (extra ++ witnesses)).
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  exact hwitnessed.
Qed.

(** The same reassociation at the full temporary-row context code. *)
Lemma raw_fourStateTableAppendRowContext_combined_tail_code : forall
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep extra witnesses,
  rawTemplateContextCode translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        (embedPAContext
          (map witnessedAxiom (extra ++ witnesses))))) =
  rawTemplateContextCodeOnTail translation
    (rawStandardPAAxiomWitnessPrefixContextCode M extra
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M)))
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep).
Proof.
  intros M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep extra witnesses.
  rewrite (raw_fourStateTableAppendRowContext_witnessed_tail_code
    M translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    (extra ++ witnesses)).
  rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
  reflexivity.
Qed.

(** Compile [i < S b -> i < b \/ i = b] in the literal appended-row
    context.  The returned standard witness batch is concatenated ahead of
    the caller's batch in both the witness-list and context views. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_lt_succ_cases :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          (embedPAContext (map witnessedAxiom witnesses)))))
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound)) antecedentRoot ->
  exists (extra : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep
            (embedPAContext
              (map witnessedAxiom (extra ++ witnesses))))))
      (rawTemplateFormula translation
        (coqLtSuccCasesResultTemplate index rowBound)) root.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot hprefix hantecedent.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hantecedentPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqLtSuccCasesAntecedentTemplate index rowBound))
      antecedentRoot).
  {
    rewrite <- (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep witnesses).
    exact hantecedent.
  }
  destruct
    (raw_codedPALocalProofOf_lt_succ_cases_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowBound antecedentRoot hprefix hbase hantecedentPrefix)
    as (extra & root & hextended & hcases).
  exists extra, root.
  split.
  - rewrite rawStandardPAAxiomWitnessPrefixWitnessListCode_app.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement (extra ++ witnesses)).
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hextended.
  - rewrite (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      (extra ++ witnesses)).
    rewrite rawStandardPAAxiomWitnessPrefixContextCode_app.
    exact hcases.
Qed.

(** Exact represented case elimination in the append-row context.  Each
    callback sees its arithmetic branch formula as the literal head of the
    combined temporary context. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_lt_succ_cases_eliminate :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M),
  RawCodedTemplatePAAgreement M translation ->
  forall
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot conclusion,
  RawCodedTemplatePrefixAtomicallyAdequate M translation
    (coqFourStateTableAppendRowPrefix
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep) ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCode translation
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          (embedPAContext (map witnessedAxiom witnesses)))))
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound)) antecedentRoot ->
  (forall extra,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesBelowTemplate index rowBound))
          (rawTemplateContextCode translation
            (templateContextShiftMany 5
              (coqFourStateTableAppendWitnessContext
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep
                (embedPAContext
                  (map witnessedAxiom (extra ++ witnesses)))))))
        conclusion root) ->
  (forall extra,
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) ->
    exists root,
      RawCodedPALocalProofOf M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesEqualTemplate index rowBound))
          (rawTemplateContextCode translation
            (templateContextShiftMany 5
              (coqFourStateTableAppendWitnessContext
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep
                (embedPAContext
                  (map witnessedAxiom (extra ++ witnesses)))))))
        conclusion root) ->
  exists (extra : StandardPAAxiomWitnessPrefix) (root : M),
    RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        (extra ++ witnesses) (raw_zero M))
      (rawTemplateContextCode translation
        (embedPAContext (map witnessedAxiom (extra ++ witnesses)))) /\
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep
            (embedPAContext
              (map witnessedAxiom (extra ++ witnesses))))))
      conclusion root.
Proof.
  intros M hPA translation hagreement
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    witnesses index rowBound antecedentRoot conclusion
    hprefix hantecedent hbelowBranch hequalBranch.
  assert (hbase : RawCodedPAAxiomWitnessContext M
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))).
  {
    pose proof (raw_templateEmbeddedPAAxiomWitnessContext
      M hPA translation hagreement witnesses) as hbaseTemplate.
    rewrite (raw_templateContextCode_embedPAAxiomWitnesses
      M translation hagreement witnesses) in hbaseTemplate.
    exact hbaseTemplate.
  }
  assert (hantecedentPrefix : RawCodedPALocalProofOf M
      (rawTemplateContextCodeOnTail translation
        (rawStandardPAAxiomWitnessPrefixContextCode M
          witnesses (raw_zero M))
        (coqFourStateTableAppendRowPrefix
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep))
      (rawTemplateFormula translation
        (coqLtSuccCasesAntecedentTemplate index rowBound))
      antecedentRoot).
  {
    rewrite <- (raw_fourStateTableAppendRowContext_witnessed_tail_code
      M translation hagreement
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep witnesses).
    exact hantecedent.
  }
  pose proof
    (raw_codedPALocalProofOf_lt_succ_cases_eliminate_on_witnessed_tail_under_prefix
      M hPA translation hagreement
      (rawStandardPAAxiomWitnessPrefixWitnessListCode M
        witnesses (raw_zero M))
      (rawStandardPAAxiomWitnessPrefixContextCode M
        witnesses (raw_zero M))
      (coqFourStateTableAppendRowPrefix
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep)
      index rowBound antecedentRoot conclusion
      hprefix hbase hantecedentPrefix) as hsplit.
  lazymatch type of hsplit with
  | ?belowType -> ?equalType -> _ =>
      assert (hbelowForSplit : belowType);
      [ intros extra hextended;
        pose proof (raw_fourStateTableAppendRow_combined_witnessed_tail
          M translation hagreement extra witnesses hextended) as hcombined;
        destruct (hbelowBranch extra hcombined) as [root hroot];
        exists root;
        rewrite <- (raw_fourStateTableAppendRowContext_combined_tail_code
          M translation hagreement
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep extra witnesses);
        exact hroot
      | assert (hequalForSplit : equalType);
        [ intros extra hextended;
          pose proof (raw_fourStateTableAppendRow_combined_witnessed_tail
            M translation hagreement extra witnesses hextended) as hcombined;
          destruct (hequalBranch extra hcombined) as [root hroot];
          exists root;
          rewrite <- (raw_fourStateTableAppendRowContext_combined_tail_code
            M translation hagreement
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep extra witnesses);
          exact hroot
        | destruct (hsplit hbelowForSplit hequalForSplit)
            as (extra & root & hextended & hroot);
          exists extra, root;
          split;
          [ exact (raw_fourStateTableAppendRow_combined_witnessed_tail
              M translation hagreement extra witnesses hextended)
          | rewrite (raw_fourStateTableAppendRowContext_combined_tail_code
              M translation hagreement
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              bound mode formula assignmentCode assignmentStep
              extra witnesses);
            exact hroot ] ] ]
  end.
Qed.

End PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
