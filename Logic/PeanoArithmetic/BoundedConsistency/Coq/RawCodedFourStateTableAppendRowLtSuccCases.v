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
  RawCodedContextLists
  RawCodedRestrictedPAProof
  RawCodedFixedLevelTruthTotality
  RawCodedPAAxiomWitnessPrefix
  RawCodedProofAssumptionLeaf
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofEquality
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
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedPAAxiomWitnessPrefix.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofEquality.
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

(** Use an equality appearing as a freshly consed assumption in the reverse
    direction.  This is the characteristic shape of the append equality
    branch: the base context proves the motive at [target], while the branch
    head says [source = target].  Symmetry and equality elimination are both
    derived inside the represented proof calculus; the base proof is moved
    below the branch head only by the guarded context-transplant theorem. *)
Theorem raw_codedPALocalProofOf_templateEqTransport_reverse_head : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context source target motive motiveRoot,
  let equalityHead :=
    rawTemplateFormula translation (tfEq source target) in
  RawCodedFormulaAtomicallyAdequate M equalityHead ->
  RawContextListRealizable M context ->
  RawCodedPALocalProofOf M context
    (rawTemplateFormula translation
      (templateFormulaOpen target motive)) motiveRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M equalityHead context)
      (rawTemplateFormula translation
        (templateFormulaOpen source motive)) root.
Proof.
  intros M hPA translation context source target motive motiveRoot
    equalityHead hhead hcontext hmotive.
  cbn zeta in *.
  pose proof (raw_codedPALocalProofOf_assumption M hPA context
    (rawTemplateFormula translation (tfEq source target)) hcontext)
    as hequality.
  destruct (raw_codedPALocalProofOf_templateEqSymmetry M hPA translation
    (rawListNode M
      (rawTemplateFormula translation (tfEq source target)) context)
    source target
    (rawProofAssumptionRoot M
      (rawListNode M
        (rawTemplateFormula translation (tfEq source target)) context)
      (rawTemplateFormula translation (tfEq source target)))
    hequality) as [symmetryRoot hsymmetry].
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    context
    (rawTemplateFormula translation (tfEq source target))
    (rawTemplateFormula translation
      (templateFormulaOpen target motive))
    motiveRoot hhead hcontext hmotive)
    as [transplantedMotiveRoot htransplantedMotive].
  eexists.
  exact (raw_codedPALocalProofOf_templateEqElim M hPA translation
    (rawListNode M
      (rawTemplateFormula translation (tfEq source target)) context)
    target source motive symmetryRoot transplantedMotiveRoot
    hsymmetry htransplantedMotive).
Qed.

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

(** Concrete predecessor callback for the represented case split.  Two
    structural equalities identify the arithmetic source's antecedent and
    left branch with the append preservation law's current and old bounds.
    The old bound is then obtained by an honest head-assumption proof. *)
Theorem
    raw_codedPALocalProofOf_four_state_table_append_row_predecessor_branch_lookup :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    currentBoundRoot oldStateLookupRoot,
  let shiftedWitnessContext := templateContextShiftMany 5
    (coqFourStateTableAppendWitnessContext
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep context) in
  let shiftedWitnessContextCode :=
    rawTemplateContextCode translation shiftedWitnessContext in
  let branchHead := rawTemplateFormula translation
    (coqLtSuccCasesBelowTemplate index rowBound) in
  let modeAt := coqFourStateTableAppendRowModePreservationAtTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep index rowMode in
  let formulaAt := coqFourStateTableAppendRowFormulaPreservationAtTemplate
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep index rowFormula in
  let assignmentCodeAt :=
    coqFourStateTableAppendRowAssignmentCodePreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentCode in
  let assignmentStepAt :=
    coqFourStateTableAppendRowAssignmentStepPreservationAtTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowAssignmentStep in
  templateImpAntecedent formulaAt = templateImpAntecedent modeAt ->
  templateImpAntecedent assignmentCodeAt = templateImpAntecedent modeAt ->
  templateImpAntecedent assignmentStepAt = templateImpAntecedent modeAt ->
  templateImp3SecondPremise formulaAt =
    templateImp3SecondPremise modeAt ->
  templateImp3SecondPremise assignmentCodeAt =
    templateImp3SecondPremise modeAt ->
  templateImp3SecondPremise assignmentStepAt =
    templateImp3SecondPremise modeAt ->
  coqLtSuccCasesAntecedentTemplate index rowBound =
    coqFourStateTableAppendRowPredecessorCurrentBoundTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode ->
  coqLtSuccCasesBelowTemplate index rowBound =
    coqFourStateTableAppendRowPredecessorOldBoundTemplate
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep index rowMode ->
  RawCodedFormulaAtomicallyAdequate M branchHead ->
  RawCodedPALocalProofOf M shiftedWitnessContextCode
    (rawTemplateFormula translation
      (coqLtSuccCasesAntecedentTemplate index rowBound))
    currentBoundRoot ->
  RawCodedPALocalProofOf M shiftedWitnessContextCode
    (rawTemplateFormula translation
      (coqFourStateTableAppendRowPredecessorOldStateLookupTemplate
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep
        index rowMode rowFormula rowAssignmentCode rowAssignmentStep))
    oldStateLookupRoot ->
  exists root,
    RawCodedPALocalProofOf M
      (rawListNode M branchHead shiftedWitnessContextCode)
      (rawTemplateFormula translation
        (coqFourStateTableAppendRowPredecessorNewStateLookupTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep
          index rowMode rowFormula rowAssignmentCode rowAssignmentStep)) root.
Proof.
  intros M hPA translation context
    modeCode modeStep formulaCode formulaStep
    assignmentCodeCode assignmentCodeStep
    assignmentStepCode assignmentStepStep
    bound mode formula assignmentCode assignmentStep
    index rowBound rowMode rowFormula rowAssignmentCode rowAssignmentStep
    currentBoundRoot oldStateLookupRoot
    shiftedWitnessContext shiftedWitnessContextCode branchHead
    modeAt formulaAt assignmentCodeAt assignmentStepAt
    hformulaFirst hassignmentCodeFirst hassignmentStepFirst
    hformulaSecond hassignmentCodeSecond hassignmentStepSecond
    hantecedentCurrent hbelowOld hhead hcurrent holdLookup.
  cbn zeta in *.
  pose proof (raw_templateContext_realizable M hPA translation
    (templateContextShiftMany 5
      (coqFourStateTableAppendWitnessContext
        modeCode modeStep formulaCode formulaStep
        assignmentCodeCode assignmentCodeStep
        assignmentStepCode assignmentStepStep
        bound mode formula assignmentCode assignmentStep context)))
    as hcontext.
  pose proof (raw_codedPALocalProofOf_assumption M hPA
    (rawTemplateContextCode translation
      (templateContextShiftMany 5
        (coqFourStateTableAppendWitnessContext
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep context)))
    (rawTemplateFormula translation
      (coqLtSuccCasesBelowTemplate index rowBound)) hcontext)
    as holdBoundAssumption.
  assert (hcurrentBound : RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (templateContextShiftMany 5
          (coqFourStateTableAppendWitnessContext
            modeCode modeStep formulaCode formulaStep
            assignmentCodeCode assignmentCodeStep
            assignmentStepCode assignmentStepStep
            bound mode formula assignmentCode assignmentStep context)))
      (rawTemplateFormula translation
        (coqFourStateTableAppendRowPredecessorCurrentBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep index rowMode))
      currentBoundRoot).
  {
    rewrite <- hantecedentCurrent.
    exact hcurrent.
  }
  assert (holdBound : RawCodedPALocalProofOf M
      (rawListNode M
        (rawTemplateFormula translation
          (coqLtSuccCasesBelowTemplate index rowBound))
        (rawTemplateContextCode translation
          (templateContextShiftMany 5
            (coqFourStateTableAppendWitnessContext
              modeCode modeStep formulaCode formulaStep
              assignmentCodeCode assignmentCodeStep
              assignmentStepCode assignmentStepStep
              bound mode formula assignmentCode assignmentStep context))))
      (rawTemplateFormula translation
        (coqFourStateTableAppendRowPredecessorOldBoundTemplate
          modeCode modeStep formulaCode formulaStep
          assignmentCodeCode assignmentCodeStep
          assignmentStepCode assignmentStepStep
          bound mode formula assignmentCode assignmentStep index rowMode))
      (rawProofAssumptionRoot M
        (rawListNode M
          (rawTemplateFormula translation
            (coqLtSuccCasesBelowTemplate index rowBound))
          (rawTemplateContextCode translation
            (templateContextShiftMany 5
              (coqFourStateTableAppendWitnessContext
                modeCode modeStep formulaCode formulaStep
                assignmentCodeCode assignmentCodeStep
                assignmentStepCode assignmentStepStep
                bound mode formula assignmentCode assignmentStep context))))
        (rawTemplateFormula translation
          (coqLtSuccCasesBelowTemplate index rowBound)))).
  {
    rewrite <- hbelowOld.
    exact holdBoundAssumption.
  }
  eapply
    (raw_codedPALocalProofOf_four_state_table_append_row_predecessor_state_lookup_under_adequate_head
      M hPA translation context
      (rawTemplateFormula translation
        (coqLtSuccCasesBelowTemplate index rowBound))
      modeCode modeStep formulaCode formulaStep
      assignmentCodeCode assignmentCodeStep
      assignmentStepCode assignmentStepStep
      bound mode formula assignmentCode assignmentStep
      index rowMode rowFormula rowAssignmentCode rowAssignmentStep
      currentBoundRoot _ oldStateLookupRoot).
  - exact hformulaFirst.
  - exact hassignmentCodeFirst.
  - exact hassignmentStepFirst.
  - exact hformulaSecond.
  - exact hassignmentCodeSecond.
  - exact hassignmentStepSecond.
  - exact hhead.
  - exact hcurrentBound.
  - exact holdBound.
  - exact holdLookup.
Qed.

End PABoundedRawCodedFourStateTableAppendRowLtSuccCases.
