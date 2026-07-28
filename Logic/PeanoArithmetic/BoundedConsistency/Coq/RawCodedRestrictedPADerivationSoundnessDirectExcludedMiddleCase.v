(**
  The genuine excluded-middle constructor case for the direct strong step.

  The rule has no recursive proof children.  After the endpoint's eight
  witnesses have been opened, its branch records that the displayed
  conclusion is a coded disjunction

      a \/ (a -> Bot).

  All proof-theoretic work surrounding that fact is finite.  This module
  projects the three relevant constructor equations from the literal nested
  conjunction, feeds them to one sharply stated truth law, inserts the
  (unused) context-truth premise, and discharges the rule-case assumption.
  The result is therefore exactly the excluded-middle slot expected by
  [RawCoqRestrictedPADirectStrongStepRuleCaseImplicationRoots].

  The sole residual is intentionally not a case root or a conclusion proof.
  It is the object-level Tarski law

      BotCode(c) -> ImpCode(b,a,c) -> OrCode(q,a,b)
        -> Admissible(q) -> Truth(q)

  in the already opened endpoint context.  Proving this law from the native
  dynamic-truth row compiler is the remaining semantic task for this rule.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedProofConstructors
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedTemplateSyntax
  RawCodedTemplateProofCompiler
  RawCodedTemplateDirectStructuralTranslation
  RawCodedRestrictedPAConsistencyFromUniversalSoundness
  RawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier
  RawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

Import ListNotations.

Module
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedRestrictedPAConsistencyFromUniversalSoundness.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectRuleDispatchFrontier.
Import
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectStrongStepShell.

(** ------------------------------------------------------------------
    Exact contexts and literal witness formulas. *)

Definition coqRestrictedPADirectExcludedMiddleDeepContext
    (tail : TemplateContext) : TemplateContext :=
  rawCoqRestrictedPADirectEndpointDeepContext
    (rawCoqRestrictedPADirectStrongStepEndpointTail tail).

Definition coqRestrictedPADirectExcludedMiddleCaseTemplate
    : TemplateFormula :=
  rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleExcludedMiddle
    (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
    (tVar 6) (tVar 5) (tVar 4) (tVar 3)
    (tVar 2) (tVar 1) (tVar 0).

Definition coqRestrictedPADirectExcludedMiddleCaseContext
    (tail : TemplateContext) : TemplateContext :=
  coqRestrictedPADirectExcludedMiddleCaseTemplate ::
    coqRestrictedPADirectExcludedMiddleDeepContext tail.

(** The four rule fields, in the exact order used by
    [proofRuleConjunction].  The final reflexive equality is the source
    encoding's nonempty-conjunction terminator. *)
Definition coqRestrictedPADirectExcludedMiddleCodeEqualityTemplate
    : TemplateFormula :=
  embedPAFormula
    (pEq (liftTerm 8 (tVar 4))
      (proofLemCodeTerm (tVar 7) (tVar 6))).

Definition coqRestrictedPADirectExcludedMiddleBottomTemplate
    : TemplateFormula :=
  embedPAFormula (formulaBotCodeTermAt (tVar 4)).

Definition coqRestrictedPADirectExcludedMiddleImpTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaImpCodeTermAt (tVar 5) (tVar 6) (tVar 4)).

Definition coqRestrictedPADirectExcludedMiddleOrTemplate
    : TemplateFormula :=
  embedPAFormula
    (formulaOrCodeTermAt
      (liftTerm 8 (tVar 2)) (tVar 6) (tVar 5)).

Definition coqRestrictedPADirectExcludedMiddleTerminalTemplate
    : TemplateFormula :=
  embedPAFormula (pEq tZero tZero).

Definition coqRestrictedPADirectExcludedMiddleOrSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExcludedMiddleOrTemplate
    coqRestrictedPADirectExcludedMiddleTerminalTemplate.

Definition coqRestrictedPADirectExcludedMiddleImpSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExcludedMiddleImpTemplate
    coqRestrictedPADirectExcludedMiddleOrSuffixTemplate.

Definition coqRestrictedPADirectExcludedMiddleBottomSuffixTemplate
    : TemplateFormula :=
  tfAnd coqRestrictedPADirectExcludedMiddleBottomTemplate
    coqRestrictedPADirectExcludedMiddleImpSuffixTemplate.

Lemma coqRestrictedPADirectExcludedMiddle_case_shape :
  coqRestrictedPADirectExcludedMiddleCaseTemplate =
  tfAnd coqRestrictedPADirectExcludedMiddleCodeEqualityTemplate
    coqRestrictedPADirectExcludedMiddleBottomSuffixTemplate.
Proof. reflexivity. Qed.

(** The dispatcher renames the remaining implication suffix once for every
    endpoint witness.  These names keep the final theorem readable while
    retaining literal definitional equality with that suffix. *)
Definition coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessAdmissibleTemplate.

Definition coqRestrictedPADirectExcludedMiddleContextTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessContextTruthTemplate.

Definition coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate
    : TemplateFormula :=
  rawCoqTemplateRenameN 8
    coqRestrictedPADerivationSoundnessConclusionTruthTemplate.

Definition coqRestrictedPADirectExcludedMiddleRemainingTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
    (tfImp coqRestrictedPADirectExcludedMiddleContextTruthTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate).

Lemma coqRestrictedPADirectExcludedMiddle_remaining_shape :
  coqRestrictedPADirectExcludedMiddleRemainingTemplate =
  rawCoqTemplateRenameN 8
    rawCoqRestrictedPADirectStrongStepRemainingTemplate.
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    The one semantic residual. *)

Definition coqRestrictedPADirectExcludedMiddleTruthLawTemplate
    : TemplateFormula :=
  tfImp coqRestrictedPADirectExcludedMiddleBottomTemplate
    (tfImp coqRestrictedPADirectExcludedMiddleImpTemplate
      (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))).

(** The law is stated in the exact case context because that is where its
    four applications occur.  Its formula itself contains no endpoint
    disjunction, rule tag, restricted-proof premise, context-truth premise,
    or strong-step conclusion.  Thus this interface cannot simply be filled
    with the desired branch root without first proving the displayed Tarski
    implication. *)
Definition RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot
    (M : RawPAModel) (translation : RawCodedTemplateTranslation M)
    (tail : TemplateContext) : Prop :=
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectExcludedMiddleCaseContext tail))
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleTruthLawTemplate)
      root.

Arguments RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot
  M translation tail : clear implicits.

(** ------------------------------------------------------------------
    Small declarative proof combinators. *)

Lemma coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE1 : forall
    context left right child,
  TemplateRawDerives context (tfAnd left right) child ->
  TemplateRawDerives context left
    (trpAndE1 context left right child).
Proof.
  intros context left right child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE2 : forall
    context left right child,
  TemplateRawDerives context (tfAnd left right) child ->
  TemplateRawDerives context right
    (trpAndE2 context left right child).
Proof.
  intros context left right child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI : forall
    context antecedent consequent child,
  TemplateRawDerives (antecedent :: context) consequent child ->
  TemplateRawDerives context (tfImp antecedent consequent)
    (trpImpI context antecedent consequent child).
Proof.
  intros context antecedent consequent child
    [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

Lemma coqRestrictedPADirectExcludedMiddle_templateRawDerives_impE : forall
    context antecedent consequent implicationChild antecedentChild,
  TemplateRawDerives context (tfImp antecedent consequent)
    implicationChild ->
  TemplateRawDerives context antecedent antecedentChild ->
  TemplateRawDerives context consequent
    (trpImpE context antecedent consequent
      implicationChild antecedentChild).
Proof.
  intros context antecedent consequent implicationChild antecedentChild
    [himpValid [himpContext himpConclusion]]
    [hargValid [hargContext hargConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Projections from the literal excluded-middle conjunction. *)

Definition coqRestrictedPADirectExcludedMiddleCaseRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleCaseTemplate.

Definition coqRestrictedPADirectExcludedMiddleBottomSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleCodeEqualityTemplate
    coqRestrictedPADirectExcludedMiddleBottomSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleCaseRoot tail).

Definition coqRestrictedPADirectExcludedMiddleBottomRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleBottomTemplate
    coqRestrictedPADirectExcludedMiddleImpSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleBottomSuffixRoot tail).

Definition coqRestrictedPADirectExcludedMiddleImpSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleBottomTemplate
    coqRestrictedPADirectExcludedMiddleImpSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleBottomSuffixRoot tail).

Definition coqRestrictedPADirectExcludedMiddleImpRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleImpTemplate
    coqRestrictedPADirectExcludedMiddleOrSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleImpSuffixRoot tail).

Definition coqRestrictedPADirectExcludedMiddleOrSuffixRoot tail
    : TemplateRawProof :=
  trpAndE2 (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleImpTemplate
    coqRestrictedPADirectExcludedMiddleOrSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleImpSuffixRoot tail).

Definition coqRestrictedPADirectExcludedMiddleOrRoot tail
    : TemplateRawProof :=
  trpAndE1 (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleOrTemplate
    coqRestrictedPADirectExcludedMiddleTerminalTemplate
    (coqRestrictedPADirectExcludedMiddleOrSuffixRoot tail).

Lemma coqRestrictedPADirectExcludedMiddleCaseRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleCaseTemplate
    (coqRestrictedPADirectExcludedMiddleCaseRoot tail).
Proof. intros tail. apply templateRawDerives_assumption. left. reflexivity. Qed.

Lemma coqRestrictedPADirectExcludedMiddleBottomSuffixRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleBottomSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleBottomSuffixRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleBottomSuffixRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE2.
  rewrite <- coqRestrictedPADirectExcludedMiddle_case_shape.
  exact (coqRestrictedPADirectExcludedMiddleCaseRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleBottomRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleBottomTemplate
    (coqRestrictedPADirectExcludedMiddleBottomRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleBottomRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE1.
  exact (coqRestrictedPADirectExcludedMiddleBottomSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleImpSuffixRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleImpSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleImpSuffixRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleImpSuffixRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE2.
  exact (coqRestrictedPADirectExcludedMiddleBottomSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleImpRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleImpTemplate
    (coqRestrictedPADirectExcludedMiddleImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleImpRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE1.
  exact (coqRestrictedPADirectExcludedMiddleImpSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleOrSuffixRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleOrSuffixTemplate
    (coqRestrictedPADirectExcludedMiddleOrSuffixRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleOrSuffixRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE2.
  exact (coqRestrictedPADirectExcludedMiddleImpSuffixRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleOrRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    coqRestrictedPADirectExcludedMiddleOrTemplate
    (coqRestrictedPADirectExcludedMiddleOrRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleOrRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_andE1.
  exact (coqRestrictedPADirectExcludedMiddleOrSuffixRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    A finite tautology inserts the unused context-truth premise.

    The semantic law naturally yields [Admissible -> Truth].  The strong
    step, however, requires [Admissible -> ContextTruth -> Truth].  Rather
    than weakening a raw proof through two open contexts (which would add
    irrelevant binder-readiness obligations), we compile the ordinary PA
    tautology [(A -> C) -> A -> B -> C] once in the unchanged case context.
*)

Definition coqRestrictedPADirectExcludedMiddleLiftContext0 tail
    : TemplateContext :=
  tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate ::
    coqRestrictedPADirectExcludedMiddleCaseContext tail.

Definition coqRestrictedPADirectExcludedMiddleLiftContext1 tail
    : TemplateContext :=
  coqRestrictedPADirectExcludedMiddleAdmissibleTemplate ::
    coqRestrictedPADirectExcludedMiddleLiftContext0 tail.

Definition coqRestrictedPADirectExcludedMiddleLiftContext2 tail
    : TemplateContext :=
  coqRestrictedPADirectExcludedMiddleContextTruthTemplate ::
    coqRestrictedPADirectExcludedMiddleLiftContext1 tail.

Definition coqRestrictedPADirectExcludedMiddleLiftImpAssumptionRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectExcludedMiddleLiftContext2 tail)
    (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate).

Definition coqRestrictedPADirectExcludedMiddleLiftAdmissibleRoot tail
    : TemplateRawProof :=
  trpAss (coqRestrictedPADirectExcludedMiddleLiftContext2 tail)
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate.

Definition coqRestrictedPADirectExcludedMiddleLiftTruthRoot tail
    : TemplateRawProof :=
  trpImpE (coqRestrictedPADirectExcludedMiddleLiftContext2 tail)
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate
    (coqRestrictedPADirectExcludedMiddleLiftImpAssumptionRoot tail)
    (coqRestrictedPADirectExcludedMiddleLiftAdmissibleRoot tail).

Definition coqRestrictedPADirectExcludedMiddleLiftContextTruthImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleLiftContext1 tail)
    coqRestrictedPADirectExcludedMiddleContextTruthTemplate
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate
    (coqRestrictedPADirectExcludedMiddleLiftTruthRoot tail).

Definition coqRestrictedPADirectExcludedMiddleLiftAdmissibleImpRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleLiftContext0 tail)
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
    (tfImp coqRestrictedPADirectExcludedMiddleContextTruthTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)
    (coqRestrictedPADirectExcludedMiddleLiftContextTruthImpRoot tail).

Definition coqRestrictedPADirectExcludedMiddleLiftRoot tail
    : TemplateRawProof :=
  trpImpI (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)
    coqRestrictedPADirectExcludedMiddleRemainingTemplate
    (coqRestrictedPADirectExcludedMiddleLiftAdmissibleImpRoot tail).

Lemma coqRestrictedPADirectExcludedMiddleLiftImpAssumptionRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleLiftContext2 tail)
    (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)
    (coqRestrictedPADirectExcludedMiddleLiftImpAssumptionRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectExcludedMiddleLiftContext2,
    coqRestrictedPADirectExcludedMiddleLiftContext1,
    coqRestrictedPADirectExcludedMiddleLiftContext0.
  (** Do not simplify the inherited tail here: it contains the eight-times
      renamed strong-step suffix.  Three explicit list steps establish the
      membership without normalizing any of those large formulas. *)
  right. right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExcludedMiddleLiftAdmissibleRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleLiftContext2 tail)
    coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
    (coqRestrictedPADirectExcludedMiddleLiftAdmissibleRoot tail).
Proof.
  intro tail. apply templateRawDerives_assumption.
  unfold coqRestrictedPADirectExcludedMiddleLiftContext2,
    coqRestrictedPADirectExcludedMiddleLiftContext1.
  right. left. reflexivity.
Qed.

Lemma coqRestrictedPADirectExcludedMiddleLiftTruthRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleLiftContext2 tail)
    coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate
    (coqRestrictedPADirectExcludedMiddleLiftTruthRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleLiftTruthRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impE.
  - exact
      (coqRestrictedPADirectExcludedMiddleLiftImpAssumptionRoot_valid tail).
  - exact
      (coqRestrictedPADirectExcludedMiddleLiftAdmissibleRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleLiftContextTruthImpRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleLiftContext1 tail)
    (tfImp coqRestrictedPADirectExcludedMiddleContextTruthTemplate
      coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)
    (coqRestrictedPADirectExcludedMiddleLiftContextTruthImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleLiftContextTruthImpRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact (coqRestrictedPADirectExcludedMiddleLiftTruthRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleLiftAdmissibleImpRoot_valid :
    forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleLiftContext0 tail)
    coqRestrictedPADirectExcludedMiddleRemainingTemplate
    (coqRestrictedPADirectExcludedMiddleLiftAdmissibleImpRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleLiftAdmissibleImpRoot,
    coqRestrictedPADirectExcludedMiddleRemainingTemplate.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectExcludedMiddleLiftContextTruthImpRoot_valid tail).
Qed.

Lemma coqRestrictedPADirectExcludedMiddleLiftRoot_valid : forall tail,
  TemplateRawDerives
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)
    (tfImp
      (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
        coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)
      coqRestrictedPADirectExcludedMiddleRemainingTemplate)
    (coqRestrictedPADirectExcludedMiddleLiftRoot tail).
Proof.
  intro tail.
  unfold coqRestrictedPADirectExcludedMiddleLiftRoot.
  apply coqRestrictedPADirectExcludedMiddle_templateRawDerives_impI.
  exact
    (coqRestrictedPADirectExcludedMiddleLiftAdmissibleImpRoot_valid tail).
Qed.

(** ------------------------------------------------------------------
    Compiled constructor branch. *)

Theorem raw_codedPALocalProofOf_coqRestrictedPADirectExcludedMiddleCase :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (coqRestrictedPADirectExcludedMiddleDeepContext tail))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExcludedMiddleCaseTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExcludedMiddleRemainingTemplate))
      root.
Proof.
  intros M hPA inputs tail. cbn zeta.
  set (translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs).
  intros (lawRoot & hlaw).
  set (caseContextCode := rawTemplateContextCode translation
    (coqRestrictedPADirectExcludedMiddleCaseContext tail)).

  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExcludedMiddleBottomRoot tail)
    (proj1 (coqRestrictedPADirectExcludedMiddleBottomRoot_valid tail)))
    as hbottom.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExcludedMiddleImpRoot tail)
    (proj1 (coqRestrictedPADirectExcludedMiddleImpRoot_valid tail)))
    as himp.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExcludedMiddleOrRoot tail)
    (proj1 (coqRestrictedPADirectExcludedMiddleOrRoot_valid tail)))
    as hor.
  pose proof (raw_templateProof_localProof M hPA translation
    (coqRestrictedPADirectExcludedMiddleLiftRoot tail)
    (proj1 (coqRestrictedPADirectExcludedMiddleLiftRoot_valid tail)))
    as hlift.

  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleBottomTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleBottomRoot tail))) in hbottom.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleImpTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleImpRoot tail))) in himp.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleOrTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleOrRoot tail))) in hor.
  change (RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExcludedMiddleAdmissibleTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleRemainingTemplate))
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleLiftRoot tail))) in hlift.

  destruct (raw_codedPALocalProofOf_impE M hPA caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleBottomTemplate)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleImpTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
          (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
            coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))))
    lawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleBottomRoot tail))
    hlaw hbottom) as [hafterBottomCoverage hafterBottomEndpoint].
  set (afterBottomRoot := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleBottomTemplate)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleImpTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
          (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
            coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))))
    lawRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleBottomRoot tail))).
  assert (hafterBottom : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleImpTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
          (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
            coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))))
    afterBottomRoot).
  { exact (conj hafterBottomCoverage hafterBottomEndpoint). }

  destruct (raw_codedPALocalProofOf_impE M hPA caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleImpTemplate)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)))
    afterBottomRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleImpRoot tail))
    hafterBottom himp) as [hafterImpCoverage hafterImpEndpoint].
  set (afterImpRoot := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleImpTemplate)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)))
    afterBottomRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleImpRoot tail))).
  assert (hafterImp : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleOrTemplate
        (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate)))
    afterImpRoot).
  { exact (conj hafterImpCoverage hafterImpEndpoint). }

  destruct (raw_codedPALocalProofOf_impE M hPA caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleOrTemplate)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
        coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
    afterImpRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleOrRoot tail))
    hafterImp hor) as [htruthLawCoverage htruthLawEndpoint].
  set (truthLawRoot := rawProofImpERoot M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleOrTemplate)
    (rawTemplateFormula translation
      (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
        coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
    afterImpRoot
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleOrRoot tail))).
  assert (htruthLaw : RawCodedPALocalProofOf M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleAdmissibleTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
    truthLawRoot).
  {
    change (RawCodedPALocalProofOf M caseContextCode
      (rawTemplateFormula translation
        (tfImp coqRestrictedPADirectExcludedMiddleAdmissibleTemplate
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
      truthLawRoot).
    exact (conj htruthLawCoverage htruthLawEndpoint).
  }

  set (remainingRoot := rawProofImpERoot M caseContextCode
    (rawFormulaImpCode M
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleAdmissibleTemplate)
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleRemainingTemplate)
    (rawTemplateProofCode translation
      (coqRestrictedPADirectExcludedMiddleLiftRoot tail))
    truthLawRoot).
  assert (hremaining : RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleRemainingTemplate)
    remainingRoot).
  {
    unfold remainingRoot.
    exact (raw_codedPALocalProofOf_impE M hPA caseContextCode
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          coqRestrictedPADirectExcludedMiddleAdmissibleTemplate)
        (rawTemplateFormula translation
          coqRestrictedPADirectExcludedMiddleConclusionTruthTemplate))
      (rawTemplateFormula translation
        coqRestrictedPADirectExcludedMiddleRemainingTemplate)
      (rawTemplateProofCode translation
        (coqRestrictedPADirectExcludedMiddleLiftRoot tail))
      truthLawRoot hlift htruthLaw).
  }

  exists (rawProofImpIRoot M
    (rawTemplateContextCode translation
      (coqRestrictedPADirectExcludedMiddleDeepContext tail))
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleCaseTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleRemainingTemplate)
    remainingRoot).
  apply (raw_codedPALocalProofOf_impI M hPA
    (rawTemplateContextCode translation
      (coqRestrictedPADirectExcludedMiddleDeepContext tail))
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleCaseTemplate)
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleRemainingTemplate)
    remainingRoot).
  change (RawCodedPALocalProofOf M caseContextCode
    (rawTemplateFormula translation
      coqRestrictedPADirectExcludedMiddleRemainingTemplate)
    remainingRoot).
  exact hremaining.
Qed.

(** Literal dispatcher-slot form. *)
Corollary
    raw_coqRestrictedPADirectStrongStepExcludedMiddleCaseRoot :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M) tail,
  let translation :=
    rawDirectStructuralTemplateTranslation M hPA inputs in
  RawCoqRestrictedPADirectExcludedMiddleTruthLawRoot
    M translation tail ->
  exists root : M,
    RawCodedPALocalProofOf M
      (rawTemplateContextCode translation
        (rawCoqRestrictedPADirectEndpointWitnessBodyTemplate ::
          rawCoqRestrictedPADirectEndpointDeepTail
            (rawCoqRestrictedPADirectStrongStepEndpointTail tail)))
      (rawFormulaImpCode M
        (rawTemplateFormula translation
          (rawCoqRestrictedPAProofRuleCaseTemplate rawCoqRuleExcludedMiddle
            (liftTerm 8 (tVar 4)) (tVar 7) (liftTerm 8 (tVar 2))
            (tVar 6) (tVar 5) (tVar 4) (tVar 3)
            (tVar 2) (tVar 1) (tVar 0)))
        (rawTemplateFormula translation
          (rawCoqTemplateRenameN 8
            rawCoqRestrictedPADirectStrongStepRemainingTemplate)))
      root.
Proof.
  intros M hPA inputs tail. cbn zeta. intro hlaw.
  destruct
    (raw_codedPALocalProofOf_coqRestrictedPADirectExcludedMiddleCase
      M hPA inputs tail hlaw) as [root hroot].
  exists root.
  unfold coqRestrictedPADirectExcludedMiddleDeepContext in hroot.
  rewrite raw_coqRestrictedPADirectEndpointDeepContext_shape in hroot.
  rewrite <- coqRestrictedPADirectExcludedMiddle_remaining_shape.
  exact hroot.
Qed.

End
  PABoundedRawCodedRestrictedPADerivationSoundnessDirectExcludedMiddleCase.
