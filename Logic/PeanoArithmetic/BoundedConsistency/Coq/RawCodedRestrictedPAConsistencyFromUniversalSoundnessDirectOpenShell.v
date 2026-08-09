(**
  The finite proof shell inside consistency-from-universal-soundness.

  After a candidate restricted proof has been opened, its three existential
  witnesses occupy de Bruijn indices 2, 1, and 0 (axiom-witness list, proof
  root, and proof context); the outer candidate code occupies index 3.  At
  that point no induction and no truth construction remains in the logical
  use of universal soundness.  One specializes the invariant at

      proof root, context, bottom, zero assignment code, zero assignment step,

  specializes the witnessed-context truth law at the first two witnesses,
  and performs ordinary implication elimination.

  This module records that finite proof tree explicitly.  The resulting
  theorem is deliberately independent of how the three arithmetic side
  conditions -- admissibility of bottom at the zero assignment, boundedness
  of the selected context, and atomic adequacy of that context -- are
  produced.  It therefore makes the remaining non-propositional work visible
  without replacing it by a semantic or proof-producing assumption.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofAtomicAdequacy
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedRestrictedTargetTemplateContext
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateRepeatedUniversalElimination
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofEmptyContextTransport
  RawCodedRestrictedPAConsistencyFromUniversalSoundness.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedRestrictedTargetTemplateContext.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateRepeatedUniversalElimination.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofEmptyContextTransport.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.

(** The variables in the body of the three candidate-field existentials. *)
Definition coqRestrictedPAOpenShellWitnessListTerm : TemplateTerm := ttVar 2.
Definition coqRestrictedPAOpenShellProofRootTerm : TemplateTerm := ttVar 1.
Definition coqRestrictedPAOpenShellProofContextTerm : TemplateTerm := ttVar 0.
Definition coqRestrictedPAOpenShellBottomCodeTerm : TemplateTerm :=
  embedPATerm rawFormulaBotCodeTerm.

(** Exact fivefold specialization of the universal invariant. *)
Definition coqRestrictedPAOpenShellSoundnessReplacements
    : list TemplateTerm :=
  [coqRestrictedPAOpenShellProofRootTerm;
   coqRestrictedPAOpenShellProofContextTerm;
   coqRestrictedPAOpenShellBottomCodeTerm;
   ttZero;
   ttZero].

Definition coqRestrictedPAOpenShellSoundnessInstanceTemplate
    : TemplateFormula :=
  rawCoqTemplateAllEListResult
    coqRestrictedPAOpenShellSoundnessReplacements
    coqRestrictedPADerivationSoundnessUniversalTemplate.

(** The four premises and the conclusion exposed by that specialization. *)
Definition coqRestrictedPAOpenShellRestrictedProofTemplate
    : TemplateFormula :=
  templateFormulaOpen coqRestrictedPAOpenShellProofRootTerm
    (templateFormulaOpen coqRestrictedPAOpenShellProofContextTerm
      (templateFormulaOpen coqRestrictedPAOpenShellBottomCodeTerm
        (templateFormulaOpen ttZero
          (templateFormulaOpen ttZero
            coqRestrictedPADerivationSoundnessRestrictedProofTemplate)))).

Definition coqRestrictedPAOpenShellEndpointTemplate : TemplateFormula :=
  templateFormulaOpen coqRestrictedPAOpenShellProofRootTerm
    (templateFormulaOpen coqRestrictedPAOpenShellProofContextTerm
      (templateFormulaOpen coqRestrictedPAOpenShellBottomCodeTerm
        (templateFormulaOpen ttZero
          (templateFormulaOpen ttZero
            coqRestrictedPADerivationSoundnessEndpointTemplate)))).

Definition coqRestrictedPAOpenShellAdmissibleTemplate : TemplateFormula :=
  templateFormulaOpen coqRestrictedPAOpenShellProofRootTerm
    (templateFormulaOpen coqRestrictedPAOpenShellProofContextTerm
      (templateFormulaOpen coqRestrictedPAOpenShellBottomCodeTerm
        (templateFormulaOpen ttZero
          (templateFormulaOpen ttZero
            coqRestrictedPADerivationSoundnessAdmissibleTemplate)))).

Definition coqRestrictedPAOpenShellContextTruthTemplate : TemplateFormula :=
  templateFormulaOpen coqRestrictedPAOpenShellProofRootTerm
    (templateFormulaOpen coqRestrictedPAOpenShellProofContextTerm
      (templateFormulaOpen coqRestrictedPAOpenShellBottomCodeTerm
        (templateFormulaOpen ttZero
          (templateFormulaOpen ttZero
            coqRestrictedPADerivationSoundnessContextTruthTemplate)))).

Definition coqRestrictedPAOpenShellConclusionTruthTemplate
    : TemplateFormula :=
  templateFormulaOpen coqRestrictedPAOpenShellProofRootTerm
    (templateFormulaOpen coqRestrictedPAOpenShellProofContextTerm
      (templateFormulaOpen coqRestrictedPAOpenShellBottomCodeTerm
        (templateFormulaOpen ttZero
          (templateFormulaOpen ttZero
            coqRestrictedPADerivationSoundnessConclusionTruthTemplate)))).

(** Exact twofold specialization of the witnessed-context truth law. *)
Definition coqRestrictedPAOpenShellContextTruthReplacements
    : list TemplateTerm :=
  [coqRestrictedPAOpenShellWitnessListTerm;
   coqRestrictedPAOpenShellProofContextTerm].

Definition coqRestrictedPAOpenShellContextTruthLawInstanceTemplate
    : TemplateFormula :=
  rawCoqTemplateAllEListResult
    coqRestrictedPAOpenShellContextTruthReplacements
    coqRestrictedPAAxiomContextsTruthTemplate.

Definition coqRestrictedPAOpenShellWitnessedContextTemplate
    : TemplateFormula :=
  embedPAFormula
    (codedPAAxiomWitnessContextTermAt
      (tVar 2) (tVar 0)).

Definition coqRestrictedPAOpenShellContextBoundedTemplate
    : TemplateFormula :=
  restrictedTargetTemplateFormulaContext
    coqRestrictedPASoundnessLowerLevelTerm
    (restrictedTargetContextAllBoundedContext (tVar 0)).

Definition coqRestrictedPAOpenShellContextAdequateTemplate
    : TemplateFormula :=
  embedPAFormula (contextAllAtomicallyAdequateTermAt (tVar 0)).

(** The two supplied truth laws use exactly the atoms reached above. *)
Definition coqRestrictedPAOpenShellBottomRefutationTemplate
    : TemplateFormula :=
  coqRestrictedPABottomTruthRefutationTemplate.

(** These constructor identities are intentionally audit-visible.  They pin
    the replacement order and prevent a proof from silently instantiating
    the context, conclusion, or assignment fields in the wrong order. *)
Lemma coqRestrictedPAOpenShell_soundness_instance_shape :
  coqRestrictedPAOpenShellSoundnessInstanceTemplate =
  tfImp coqRestrictedPAOpenShellRestrictedProofTemplate
    (tfImp coqRestrictedPAOpenShellEndpointTemplate
      (tfImp coqRestrictedPAOpenShellAdmissibleTemplate
        (tfImp coqRestrictedPAOpenShellContextTruthTemplate
          coqRestrictedPAOpenShellConclusionTruthTemplate))).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPAOpenShell_context_truth_instance_shape :
  coqRestrictedPAOpenShellContextTruthLawInstanceTemplate =
  tfImp coqRestrictedPAOpenShellWitnessedContextTemplate
    (tfImp coqRestrictedPAOpenShellContextBoundedTemplate
      (tfImp coqRestrictedPAOpenShellContextAdequateTemplate
        coqRestrictedPAOpenShellContextTruthTemplate)).
Proof. vm_compute. reflexivity. Qed.

Lemma coqRestrictedPAOpenShell_bottom_refutation_shape :
  coqRestrictedPAOpenShellBottomRefutationTemplate =
  tfImp coqRestrictedPAOpenShellConclusionTruthTemplate tfBot.
Proof. vm_compute. reflexivity. Qed.

(** ------------------------------------------------------------------
    The finite natural-deduction tree. *)

Definition coqRestrictedPAOpenShellAssumptions : list TemplateFormula :=
  [coqRestrictedPADerivationSoundnessUniversalTemplate;
   coqRestrictedPAAxiomContextsTruthTemplate;
   coqRestrictedPAOpenShellBottomRefutationTemplate;
   coqRestrictedPAOpenShellRestrictedProofTemplate;
   coqRestrictedPAOpenShellEndpointTemplate;
   coqRestrictedPAOpenShellAdmissibleTemplate;
   coqRestrictedPAOpenShellWitnessedContextTemplate;
   coqRestrictedPAOpenShellContextBoundedTemplate;
   coqRestrictedPAOpenShellContextAdequateTemplate].

Fixpoint coqRestrictedPAOpenShellImpChain
    (premises : list TemplateFormula) (conclusion : TemplateFormula)
    : TemplateFormula :=
  match premises with
  | [] => conclusion
  | premise :: tail =>
      tfImp premise (coqRestrictedPAOpenShellImpChain tail conclusion)
  end.

(** Implication introduction enters premises in reverse order. *)
Fixpoint coqRestrictedPAOpenShellEnteredContext
    (premises : list TemplateFormula) (base : TemplateContext)
    : TemplateContext :=
  match premises with
  | [] => base
  | premise :: tail =>
      coqRestrictedPAOpenShellEnteredContext tail (premise :: base)
  end.

Fixpoint coqRestrictedPAOpenShellImpIListRoot
    (base : TemplateContext) (premises : list TemplateFormula)
    (conclusion : TemplateFormula) (innerRoot : TemplateRawProof)
    : TemplateRawProof :=
  match premises with
  | [] => innerRoot
  | premise :: tail =>
      trpImpI base premise
        (coqRestrictedPAOpenShellImpChain tail conclusion)
        (coqRestrictedPAOpenShellImpIListRoot
          (premise :: base) tail conclusion innerRoot)
  end.

Arguments coqRestrictedPAOpenShellImpChain premises conclusion
  : clear implicits.
Arguments coqRestrictedPAOpenShellEnteredContext premises base
  : clear implicits.
Arguments coqRestrictedPAOpenShellImpIListRoot
  base premises conclusion innerRoot : clear implicits.

Lemma coqRestrictedPAOpenShell_templateRawDerives_impE : forall
    context antecedent consequent implicationRoot antecedentRoot,
  TemplateRawDerives context (tfImp antecedent consequent) implicationRoot ->
  TemplateRawDerives context antecedent antecedentRoot ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent implicationRoot antecedentRoot).
Proof.
  intros context antecedent consequent implicationRoot antecedentRoot
    [himpValid [himpContext himpConclusion]]
    [hargValid [hargContext hargConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Lemma coqRestrictedPAOpenShell_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption || reflexivity.
Qed.

Theorem coqRestrictedPAOpenShellImpIListRoot_derives : forall
    premises base conclusion innerRoot,
  TemplateRawDerives
    (coqRestrictedPAOpenShellEnteredContext premises base)
    conclusion innerRoot ->
  TemplateRawDerives base
    (coqRestrictedPAOpenShellImpChain premises conclusion)
    (coqRestrictedPAOpenShellImpIListRoot
      base premises conclusion innerRoot).
Proof.
  induction premises as [|premise tail ih];
    intros base conclusion innerRoot hinner.
  - cbn [coqRestrictedPAOpenShellEnteredContext
      coqRestrictedPAOpenShellImpChain
      coqRestrictedPAOpenShellImpIListRoot] in hinner |- *.
    exact hinner.
  - cbn [coqRestrictedPAOpenShellEnteredContext] in hinner.
    cbn [coqRestrictedPAOpenShellImpChain
      coqRestrictedPAOpenShellImpIListRoot].
    apply coqRestrictedPAOpenShell_templateRawDerives_impI.
    exact (ih (premise :: base) conclusion innerRoot hinner).
Qed.

Definition coqRestrictedPAOpenShellInnerContext : TemplateContext :=
  coqRestrictedPAOpenShellEnteredContext
    coqRestrictedPAOpenShellAssumptions [].

Definition coqRestrictedPAOpenShellAssumptionRoot
    (formula : TemplateFormula) : TemplateRawProof :=
  trpAss coqRestrictedPAOpenShellInnerContext formula.

Definition coqRestrictedPAOpenShellSoundnessInstanceRoot
    : TemplateRawProof :=
  rawCoqTemplateAllEListRoot coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellSoundnessReplacements
    coqRestrictedPADerivationSoundnessUniversalTemplate
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPADerivationSoundnessUniversalTemplate).

Definition coqRestrictedPAOpenShellContextTruthLawInstanceRoot
    : TemplateRawProof :=
  rawCoqTemplateAllEListRoot coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellContextTruthReplacements
    coqRestrictedPAAxiomContextsTruthTemplate
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAAxiomContextsTruthTemplate).

Definition coqRestrictedPAOpenShellContextTruthAfterWitnessRoot
    : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellWitnessedContextTemplate
    (tfImp coqRestrictedPAOpenShellContextBoundedTemplate
      (tfImp coqRestrictedPAOpenShellContextAdequateTemplate
        coqRestrictedPAOpenShellContextTruthTemplate))
    coqRestrictedPAOpenShellContextTruthLawInstanceRoot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellWitnessedContextTemplate).

Definition coqRestrictedPAOpenShellContextTruthAfterBoundedRoot
    : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellContextBoundedTemplate
    (tfImp coqRestrictedPAOpenShellContextAdequateTemplate
      coqRestrictedPAOpenShellContextTruthTemplate)
    coqRestrictedPAOpenShellContextTruthAfterWitnessRoot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellContextBoundedTemplate).

Definition coqRestrictedPAOpenShellContextTruthRoot : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellContextAdequateTemplate
    coqRestrictedPAOpenShellContextTruthTemplate
    coqRestrictedPAOpenShellContextTruthAfterBoundedRoot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellContextAdequateTemplate).

Definition coqRestrictedPAOpenShellAfterRestrictedRoot : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellRestrictedProofTemplate
    (tfImp coqRestrictedPAOpenShellEndpointTemplate
      (tfImp coqRestrictedPAOpenShellAdmissibleTemplate
        (tfImp coqRestrictedPAOpenShellContextTruthTemplate
          coqRestrictedPAOpenShellConclusionTruthTemplate)))
    coqRestrictedPAOpenShellSoundnessInstanceRoot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellRestrictedProofTemplate).

Definition coqRestrictedPAOpenShellAfterEndpointRoot : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellEndpointTemplate
    (tfImp coqRestrictedPAOpenShellAdmissibleTemplate
      (tfImp coqRestrictedPAOpenShellContextTruthTemplate
        coqRestrictedPAOpenShellConclusionTruthTemplate))
    coqRestrictedPAOpenShellAfterRestrictedRoot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellEndpointTemplate).

Definition coqRestrictedPAOpenShellAfterAdmissibleRoot : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellAdmissibleTemplate
    (tfImp coqRestrictedPAOpenShellContextTruthTemplate
      coqRestrictedPAOpenShellConclusionTruthTemplate)
    coqRestrictedPAOpenShellAfterEndpointRoot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellAdmissibleTemplate).

Definition coqRestrictedPAOpenShellConclusionTruthRoot : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellContextTruthTemplate
    coqRestrictedPAOpenShellConclusionTruthTemplate
    coqRestrictedPAOpenShellAfterAdmissibleRoot
    coqRestrictedPAOpenShellContextTruthRoot.

Definition coqRestrictedPAOpenShellBottomRoot : TemplateRawProof :=
  trpImpE coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellConclusionTruthTemplate tfBot
    (coqRestrictedPAOpenShellAssumptionRoot
      coqRestrictedPAOpenShellBottomRefutationTemplate)
    coqRestrictedPAOpenShellConclusionTruthRoot.

Definition coqRestrictedPAOpenShellClosedRoot : TemplateRawProof :=
  coqRestrictedPAOpenShellImpIListRoot []
    coqRestrictedPAOpenShellAssumptions tfBot
    coqRestrictedPAOpenShellBottomRoot.

Definition coqRestrictedPAOpenShellTheoremTemplate : TemplateFormula :=
  coqRestrictedPAOpenShellImpChain
    coqRestrictedPAOpenShellAssumptions tfBot.

(** The helper premise roots are literal members of the entered context. *)
Lemma coqRestrictedPAOpenShell_assumption_derives : forall formula,
  In formula coqRestrictedPAOpenShellAssumptions ->
  TemplateRawDerives coqRestrictedPAOpenShellInnerContext formula
    (coqRestrictedPAOpenShellAssumptionRoot formula).
Proof.
  intros formula hin.
  apply templateRawDerives_assumption.
  unfold coqRestrictedPAOpenShellInnerContext,
    coqRestrictedPAOpenShellAssumptions.
  cbn [coqRestrictedPAOpenShellEnteredContext] in *.
  repeat (first [left; reflexivity | right]).
Qed.

Lemma coqRestrictedPAOpenShell_soundness_instance_derives :
  TemplateRawDerives coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellSoundnessInstanceTemplate
    coqRestrictedPAOpenShellSoundnessInstanceRoot.
Proof.
  apply rawCoqTemplateAllEListRoot_derives.
  - vm_compute. exact I.
  - apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions. left. reflexivity.
Qed.

Lemma coqRestrictedPAOpenShell_context_truth_instance_derives :
  TemplateRawDerives coqRestrictedPAOpenShellInnerContext
    coqRestrictedPAOpenShellContextTruthLawInstanceTemplate
    coqRestrictedPAOpenShellContextTruthLawInstanceRoot.
Proof.
  apply rawCoqTemplateAllEListRoot_derives.
  - vm_compute. exact I.
  - apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    right. left. reflexivity.
Qed.

Theorem coqRestrictedPAOpenShell_bottom_derives :
  TemplateRawDerives coqRestrictedPAOpenShellInnerContext tfBot
    coqRestrictedPAOpenShellBottomRoot.
Proof.
  assert (hcontextLaw : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      (tfImp coqRestrictedPAOpenShellWitnessedContextTemplate
        (tfImp coqRestrictedPAOpenShellContextBoundedTemplate
          (tfImp coqRestrictedPAOpenShellContextAdequateTemplate
            coqRestrictedPAOpenShellContextTruthTemplate)))
      coqRestrictedPAOpenShellContextTruthLawInstanceRoot).
  {
    rewrite <- coqRestrictedPAOpenShell_context_truth_instance_shape.
    exact coqRestrictedPAOpenShell_context_truth_instance_derives.
  }
  assert (hwitness : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      coqRestrictedPAOpenShellWitnessedContextTemplate
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellWitnessedContextTemplate)).
  {
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    repeat right. left. reflexivity.
  }
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hcontextLaw hwitness) as hcontext1.
  assert (hbounded : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      coqRestrictedPAOpenShellContextBoundedTemplate
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellContextBoundedTemplate)).
  {
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    repeat right. left. reflexivity.
  }
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hcontext1 hbounded) as hcontext2.
  assert (hadequate : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      coqRestrictedPAOpenShellContextAdequateTemplate
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellContextAdequateTemplate)).
  {
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    repeat right. left. reflexivity.
  }
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hcontext2 hadequate) as hcontextTruth.
  assert (hsoundness : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      (tfImp coqRestrictedPAOpenShellRestrictedProofTemplate
        (tfImp coqRestrictedPAOpenShellEndpointTemplate
          (tfImp coqRestrictedPAOpenShellAdmissibleTemplate
            (tfImp coqRestrictedPAOpenShellContextTruthTemplate
              coqRestrictedPAOpenShellConclusionTruthTemplate))))
      coqRestrictedPAOpenShellSoundnessInstanceRoot).
  {
    rewrite <- coqRestrictedPAOpenShell_soundness_instance_shape.
    exact coqRestrictedPAOpenShell_soundness_instance_derives.
  }
  assert (hrestricted : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      coqRestrictedPAOpenShellRestrictedProofTemplate
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellRestrictedProofTemplate)).
  {
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    repeat right. left. reflexivity.
  }
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hsoundness hrestricted) as hsoundness1.
  assert (hendpoint : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      coqRestrictedPAOpenShellEndpointTemplate
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellEndpointTemplate)).
  {
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    repeat right. left. reflexivity.
  }
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hsoundness1 hendpoint) as hsoundness2.
  assert (hadmissible : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      coqRestrictedPAOpenShellAdmissibleTemplate
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellAdmissibleTemplate)).
  {
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    repeat right. left. reflexivity.
  }
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hsoundness2 hadmissible) as hsoundness3.
  pose proof (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hsoundness3 hcontextTruth) as hconclusionTruth.
  assert (hbottomLaw : TemplateRawDerives
      coqRestrictedPAOpenShellInnerContext
      (tfImp coqRestrictedPAOpenShellConclusionTruthTemplate tfBot)
      (coqRestrictedPAOpenShellAssumptionRoot
        coqRestrictedPAOpenShellBottomRefutationTemplate)).
  {
    rewrite <- coqRestrictedPAOpenShell_bottom_refutation_shape.
    apply coqRestrictedPAOpenShell_assumption_derives.
    unfold coqRestrictedPAOpenShellAssumptions.
    right. right. left. reflexivity.
  }
  exact (coqRestrictedPAOpenShell_templateRawDerives_impE _ _ _ _ _
    hbottomLaw hconclusionTruth).
Qed.

Theorem coqRestrictedPAOpenShell_closed_derives :
  TemplateRawDerives [] coqRestrictedPAOpenShellTheoremTemplate
    coqRestrictedPAOpenShellClosedRoot.
Proof.
  unfold coqRestrictedPAOpenShellClosedRoot,
    coqRestrictedPAOpenShellTheoremTemplate.
  apply coqRestrictedPAOpenShellImpIListRoot_derives.
  exact coqRestrictedPAOpenShell_bottom_derives.
Qed.

(** ------------------------------------------------------------------
    Direct-code compilation and same-context application. *)

Definition rawCoqRestrictedPAOpenShellTheoremCode
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    : M :=
  rawDirectTemplateFormula inputs
    coqRestrictedPAOpenShellTheoremTemplate.

Arguments rawCoqRestrictedPAOpenShellTheoremCode M inputs
  : clear implicits.

(** Compilation is finite recursion over [coqRestrictedPAOpenShellClosedRoot].
    The opaque truth leaves may be genuinely nonstandard formula codes; the
    direct translation contributes their represented shift and opening
    traces to each quantifier rule. *)
Theorem raw_codedPALocalProofOf_coqRestrictedPAOpenShell : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M),
  exists root : M,
    RawCodedPALocalProofOf M (raw_zero M)
      (rawCoqRestrictedPAOpenShellTheoremCode M inputs) root.
Proof.
  intros M hPA inputs.
  pose proof coqRestrictedPAOpenShell_closed_derives as hderives.
  destruct hderives as [hvalid [hcontext hconclusion]].
  exists (rawTemplateProofCode
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPAOpenShellClosedRoot).
  unfold rawCoqRestrictedPAOpenShellTheoremCode.
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCode
      (rawDirectStructuralTemplateTranslation M hPA inputs) [])
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqRestrictedPAOpenShellTheoremTemplate)
    (rawTemplateProofCode
      (rawDirectStructuralTemplateTranslation M hPA inputs)
      coqRestrictedPAOpenShellClosedRoot)).
  apply (raw_templateProof_localProof M hPA
    (rawDirectStructuralTemplateTranslation M hPA inputs)
    coqRestrictedPAOpenShellClosedRoot).
  exact hvalid.
Qed.

(** The sharp raw input after the finite logic has been compiled.  Six roots
    are direct projections/truth laws in the eventual candidate-field
    context.  The only genuinely arithmetic producers left are the full
    restricted-proof conjunction, bottom/zero admissibility, context
    boundedness, and context atomic adequacy.  They remain ordinary local PA
    proofs, not semantic facts. *)
Definition RawCoqRestrictedPAOpenShellRoots
    (M : RawPAModel) (inputs : RawCodedTemplateDirectStructuralInputs M)
    (context universalRoot contextTruthLawRoot bottomRefutationRoot
      restrictedProofRoot endpointRoot admissibleRoot witnessedContextRoot
      contextBoundedRoot contextAdequateRoot : M) : Prop :=
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessUniversalTemplate)
    universalRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAAxiomContextsTruthTemplate)
    contextTruthLawRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellBottomRefutationTemplate)
    bottomRefutationRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellRestrictedProofTemplate)
    restrictedProofRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellEndpointTemplate)
    endpointRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellAdmissibleTemplate)
    admissibleRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellWitnessedContextTemplate)
    witnessedContextRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextBoundedTemplate)
    contextBoundedRoot /\
  RawCodedPALocalProofOf M context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextAdequateTemplate)
    contextAdequateRoot.

Arguments RawCoqRestrictedPAOpenShellRoots M inputs context
  universalRoot contextTruthLawRoot bottomRefutationRoot
  restrictedProofRoot endpointRoot admissibleRoot witnessedContextRoot
  contextBoundedRoot contextAdequateRoot : clear implicits.

(** Apply a translated curried theorem to all nine roots.  Transport from
    the empty context is represented proof-tree rebuilding and therefore
    requires the exact all-head atomic-adequacy certificate for [context]. *)
Theorem raw_coqRestrictedPAOpenShell_bottom_of_roots : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (inputs : RawCodedTemplateDirectStructuralInputs M)
      context universalRoot contextTruthLawRoot bottomRefutationRoot
      restrictedProofRoot endpointRoot admissibleRoot witnessedContextRoot
      contextBoundedRoot contextAdequateRoot,
  RawContextAllAtomicallyAdequate M context ->
  RawCoqRestrictedPAOpenShellRoots M inputs context
    universalRoot contextTruthLawRoot bottomRefutationRoot
    restrictedProofRoot endpointRoot admissibleRoot witnessedContextRoot
    contextBoundedRoot contextAdequateRoot ->
  exists bottomRoot : M,
    RawCodedPALocalProofOf M context (rawFormulaBotCode M) bottomRoot.
Proof.
  intros M hPA inputs context universalRoot contextTruthLawRoot
    bottomRefutationRoot restrictedProofRoot endpointRoot admissibleRoot
    witnessedContextRoot contextBoundedRoot contextAdequateRoot
    hcontextAdequate hroots.
  destruct hroots as
    [huniversal [hcontextLaw [hbottomLaw [hrestricted [hendpoint
      [hadmissible [hwitnessed [hbounded hadequate]]]]]]]].
  destruct (raw_codedPALocalProofOf_coqRestrictedPAOpenShell
    M hPA inputs) as [emptyRoot hempty].
  destruct
    (raw_codedPALocalProof_emptyContext_to_atomicallyAdequateContext
      M hPA context
      (rawCoqRestrictedPAOpenShellTheoremCode M inputs)
      emptyRoot hcontextAdequate hempty)
    as [shellRoot hshell].
  unfold rawCoqRestrictedPAOpenShellTheoremCode,
    coqRestrictedPAOpenShellTheoremTemplate,
    coqRestrictedPAOpenShellAssumptions in hshell.
  cbn [coqRestrictedPAOpenShellImpChain] in hshell.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPADerivationSoundnessUniversalTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAAxiomContextsTruthTemplate;
         coqRestrictedPAOpenShellBottomRefutationTemplate;
         coqRestrictedPAOpenShellRestrictedProofTemplate;
         coqRestrictedPAOpenShellEndpointTemplate;
         coqRestrictedPAOpenShellAdmissibleTemplate;
         coqRestrictedPAOpenShellWitnessedContextTemplate;
         coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    shellRoot universalRoot hshell huniversal) as h1.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAAxiomContextsTruthTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellBottomRefutationTemplate;
         coqRestrictedPAOpenShellRestrictedProofTemplate;
         coqRestrictedPAOpenShellEndpointTemplate;
         coqRestrictedPAOpenShellAdmissibleTemplate;
         coqRestrictedPAOpenShellWitnessedContextTemplate;
         coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h1 hcontextLaw) as h2.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellBottomRefutationTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellRestrictedProofTemplate;
         coqRestrictedPAOpenShellEndpointTemplate;
         coqRestrictedPAOpenShellAdmissibleTemplate;
         coqRestrictedPAOpenShellWitnessedContextTemplate;
         coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h2 hbottomLaw) as h3.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellRestrictedProofTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellEndpointTemplate;
         coqRestrictedPAOpenShellAdmissibleTemplate;
         coqRestrictedPAOpenShellWitnessedContextTemplate;
         coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h3 hrestricted) as h4.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellEndpointTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellAdmissibleTemplate;
         coqRestrictedPAOpenShellWitnessedContextTemplate;
         coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h4 hendpoint) as h5.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellAdmissibleTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellWitnessedContextTemplate;
         coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h5 hadmissible) as h6.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellWitnessedContextTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellContextBoundedTemplate;
         coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h6 hwitnessed) as h7.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextBoundedTemplate)
    (rawDirectTemplateFormula inputs
      (coqRestrictedPAOpenShellImpChain
        [coqRestrictedPAOpenShellContextAdequateTemplate] tfBot))
    _ _ h7 hbounded) as h8.
  pose proof (raw_codedPALocalProofOf_impE M hPA context
    (rawDirectTemplateFormula inputs
      coqRestrictedPAOpenShellContextAdequateTemplate)
    (rawDirectTemplateFormula inputs tfBot)
    _ _ h8 hadequate) as h9.
  eexists. exact h9.
Qed.

End
  PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundnessDirectOpenShell.
