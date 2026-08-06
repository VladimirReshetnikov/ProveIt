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
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedTemplateLocalProofWitnessedTailTransport.

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
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedTemplateLocalProofWitnessedTailTransport.

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

End PABoundedRawCodedTemplateLocalProofAssumptionDischarge.
