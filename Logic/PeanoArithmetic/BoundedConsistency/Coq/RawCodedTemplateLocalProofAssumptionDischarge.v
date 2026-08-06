(**
  Discharge temporary template assumptions using represented proofs.

  A number of direct strong-step constructions are most naturally performed
  while two facts remain literal members of a template context.  Their callers
  may nevertheless possess actual local proofs of those facts.  The lemma
  below packages the corresponding two cuts: introduce the first implication,
  weaken its antecedent proof below the second assumption, eliminate it, then
  introduce and eliminate the second implication.

  This statement is translation-generic.  It needs only atomic adequacy of the
  two-formula prefix, not a direct structural translation or PA agreement.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofWitnessedContextMerge
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport
  RawCodedLtSuccCasesProofCompilation
  RawCodedPAGrowingTemplateConjunction.

Module PABoundedRawCodedTemplateLocalProofAssumptionDischarge.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofWitnessedContextMerge.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.
Import PABoundedRawCodedLtSuccCasesProofCompilation.
Import PABoundedRawCodedPAGrowingTemplateConjunction.

(** Eliminate the literal prefix [[first; second]] using proofs of both
    translated assumptions in the base context.  The first proof is inserted
    below [second]; this is the only step that consumes prefix adequacy. *)
Theorem raw_codedPALocalProof_discharge_two_template_assumptions : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    baseContext first second conclusion firstRoot secondRoot childRoot,
  RawContextListRealizable M baseContext ->
  RawCodedTemplatePrefixAtomicallyAdequate M translation [first; second] ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation first) firstRoot ->
  RawCodedPALocalProofOf M baseContext
    (rawTemplateFormula translation second) secondRoot ->
  RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail translation baseContext [first; second])
    conclusion childRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M baseContext conclusion resultRoot.
Proof.
  intros M hPA translation baseContext first second conclusion
    firstRoot secondRoot childRoot hbase hadequate hfirst hsecond hchild.
  cbn [rawTemplateContextCodeOnTail] in hchild.
  pose proof
    (raw_codedPALocalProofOf_impI M hPA
      (rawListNode M (rawTemplateFormula translation second) baseContext)
      (rawTemplateFormula translation first) conclusion childRoot hchild)
    as hfirstImplication.
  destruct
    (raw_codedPALocalProof_templatePrefix M hPA translation baseContext
      [second] (rawTemplateFormula translation first) firstRoot
      hbase
      (fun formula hformula =>
        hadequate formula (or_intror hformula))
      hfirst) as [firstBelowSecondRoot hfirstBelowSecond].
  cbn [rawTemplateContextCodeOnTail] in hfirstBelowSecond.
  pose proof
    (raw_codedPALocalProofOf_impE M hPA
      (rawListNode M (rawTemplateFormula translation second) baseContext)
      (rawTemplateFormula translation first) conclusion
      (rawProofImpIRoot M
        (rawListNode M (rawTemplateFormula translation second) baseContext)
        (rawTemplateFormula translation first) conclusion childRoot)
      firstBelowSecondRoot hfirstImplication hfirstBelowSecond)
    as hafterFirst.
  lazymatch type of hafterFirst with
  | RawCodedPALocalProofOf _ _ _ ?afterFirstRoot =>
      pose proof
        (raw_codedPALocalProofOf_impI M hPA baseContext
          (rawTemplateFormula translation second) conclusion
          afterFirstRoot hafterFirst) as hsecondImplication;
      lazymatch type of hsecondImplication with
      | RawCodedPALocalProofOf _ _ _ ?secondImplicationRoot =>
          pose proof
            (raw_codedPALocalProofOf_impE M hPA baseContext
              (rawTemplateFormula translation second) conclusion
              secondImplicationRoot secondRoot
              hsecondImplication hsecond) as hresult;
          lazymatch type of hresult with
          | RawCodedPALocalProofOf _ _ _ ?resultRoot =>
              exists resultRoot; exact hresult
          end
      end
  end.
Qed.

(** Growing counterpart of the preceding two cuts.  The proofs of [first],
    [second], and the child may each choose a different witnessed PA tail.
    Synchronizing those tails is an implementation detail: callers retain
    only inclusion of their common source context and receive a proof over an
    independently selected common extension.

    Keeping this lemma translation-generic is useful beyond the guarded
    collision case.  It is the standard way to close a proof-producing
    computation performed under two temporary assumptions without imposing
    equality on the finite PA witness batches chosen by its three inputs. *)
Theorem
    raw_codedPAGrowingTemplateLocalProofAt_discharge_two_template_assumptions :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (translation : RawCodedTemplateTranslation M)
    sourceWitnessList sourceContext first second conclusion,
  RawCodedTemplatePrefixAtomicallyAdequate M translation [first; second] ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext []
    (rawTemplateFormula translation first) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext []
    (rawTemplateFormula translation second) ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext [first; second] conclusion ->
  RawCodedPAGrowingTemplateLocalProofAt M translation
    sourceWitnessList sourceContext [] conclusion.
Proof.
  intros M hPA translation sourceWitnessList sourceContext
    first second conclusion hadequate hfirst hsecond hchild.
  destruct
    (raw_codedPAGrowingTemplateLocalProofAt_pair_at_prefix
      M hPA translation sourceWitnessList sourceContext []
      (rawTemplateFormula translation first)
      (rawTemplateFormula translation second)
      hfirst hsecond) as
    (premiseWitnessList & premiseContext & firstRoot & secondRoot &
      hpremiseWitnessed & hsourcePremiseIncluded &
      hfirstPremise & hsecondPremise).
  destruct hchild as
    (childWitnessList & childContext & childRoot & hchildWitnessed &
      hsourceChildIncluded & hchildProof).
  destruct
    (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
      premiseWitnessList premiseContext childWitnessList childContext
      hpremiseWitnessed hchildWitnessed) as
    (targetWitnessList & targetContext & htargetWitnessed &
      _hpremiseWitnessIncluded & hpremiseIncluded &
      _hchildWitnessIncluded & hchildIncluded & _htransport).
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation premiseWitnessList premiseContext
      targetWitnessList targetContext []
      (rawTemplateFormula translation first) firstRoot
      hpremiseWitnessed htargetWitnessed hpremiseIncluded hfirstPremise)
    as [transportedFirstRoot htransportedFirst].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation premiseWitnessList premiseContext
      targetWitnessList targetContext []
      (rawTemplateFormula translation second) secondRoot
      hpremiseWitnessed htargetWitnessed hpremiseIncluded hsecondPremise)
    as [transportedSecondRoot htransportedSecond].
  destruct
    (raw_codedPALocalProof_sameTemplatePrefix_witnessedTail_transport
      M hPA translation childWitnessList childContext
      targetWitnessList targetContext [first; second]
      conclusion childRoot hchildWitnessed htargetWitnessed
      hchildIncluded hchildProof)
    as [transportedChildRoot htransportedChild].
  cbn [rawTemplateContextCodeOnTail] in
    htransportedFirst, htransportedSecond.
  destruct
    (raw_codedPALocalProof_discharge_two_template_assumptions
      M hPA translation targetContext first second conclusion
      transportedFirstRoot transportedSecondRoot transportedChildRoot
      (raw_codedPAAxiomWitnessContext_context_realizable
        M targetWitnessList targetContext htargetWitnessed)
      hadequate htransportedFirst htransportedSecond htransportedChild)
    as [resultRoot hresult].
  exists targetWitnessList, targetContext, resultRoot.
  split; [exact htargetWitnessed |].
  split.
  - intros member hmember.
    exact (hpremiseIncluded member
      (hsourcePremiseIncluded member hmember)).
  - cbn [rawTemplateContextCodeOnTail]. exact hresult.
Qed.

End PABoundedRawCodedTemplateLocalProofAssumptionDischarge.
