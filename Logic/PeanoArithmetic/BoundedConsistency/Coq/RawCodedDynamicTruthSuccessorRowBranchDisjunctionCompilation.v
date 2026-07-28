(**
  Compile the branch disjunction carried by a native dynamic-truth row.

  A successor row has the logical shape

      Ex^8 (domain /\ (branch_1 \/ ... \/ branch_k)).

  The collision matrix consumes instead the right-associated disjunction

      Ex^8 branch_1 \/ ... \/ Ex^8 branch_k.

  The proof below is a finite natural-deduction tree.  It first projects the
  branch disjunction while retaining all eight witnesses, then eliminates
  that disjunction beneath the existential tower.  In every case it
  reintroduces the very same eigenvariable as the outer witness.  Thus the
  construction neither chooses a branch metatheoretically nor appeals to a
  semantic completeness principle.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedPAProvability
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextShift
  RawCodedProofBinaryConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedTemplateSyntax
  RawCodedTemplateLogicalSchemas
  RawCodedTemplateProjectionSchemas
  RawCodedTemplateDisjunctionCaseSchemas
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateDirectStructuralTranslation
  RawCodedTemplateProofCompiler
  RawCodedTemplateProofCompilerSelfShiftTail
  RawCodedDynamicTruthUniversalLeafSourceTemplate
  RawCodedDynamicTruthUniversalLeafProofCompilation
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthPiTemplateDirectInputs
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthQFBranchExclusivity
  RawCodedDynamicTruthImpBranchExclusivity
  RawCodedDynamicTruthBooleanBranchExclusivity
  RawCodedDynamicTruthQuantifierBranchExclusivity
  RawCodedDynamicTruthQuantifierConditionalCellCompilation
  RawCodedDynamicTruthSigmaDomainProjectionProofCompilation
  RawCodedDynamicTruthPiDomainProjectionProofCompilation
  RawCodedDynamicTruthLocalCollisionMatrixAssembly.

Import ListNotations.

Module
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateLogicalSchemas.
Import PABoundedRawCodedTemplateProjectionSchemas.
Import PABoundedRawCodedTemplateDisjunctionCaseSchemas.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateDirectStructuralTranslation.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateProofCompilerSelfShiftTail.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthUniversalLeafProofCompilation.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthPiTemplateDirectInputs.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthQFBranchExclusivity.
Import PABoundedRawCodedDynamicTruthImpBranchExclusivity.
Import PABoundedRawCodedDynamicTruthBooleanBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierBranchExclusivity.
Import PABoundedRawCodedDynamicTruthQuantifierConditionalCellCompilation.
Import PABoundedRawCodedDynamicTruthSigmaDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthPiDomainProjectionProofCompilation.
Import PABoundedRawCodedDynamicTruthLocalCollisionMatrixAssembly.

(** ------------------------------------------------------------------
    A one-witness map over a finite right-associated disjunction. *)

Definition templatePreservedWitnessExists
    (body : TemplateFormula) : TemplateFormula :=
  tfEx (templateFormulaRename (templateUpRenaming S) body).

Definition templateRightDisjunctionPreservedWitnessTarget
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : TemplateFormula :=
  templateRightDisjunction
    (map templatePreservedWitnessExists prefix)
    (templatePreservedWitnessExists tail).

Fixpoint templateRightDisjunctionPreserveWitnessFrom
    (context : TemplateContext)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match prefix with
  | [] =>
      trpExI context
        (templateFormulaRename (templateUpRenaming S) tail)
        (ttVar 0) sourceProof
  | head :: rest =>
      let right := templateRightDisjunction rest tail in
      let targetRight :=
        templateRightDisjunctionPreservedWitnessTarget rest tail in
      let target := tfOr (templatePreservedWitnessExists head) targetRight in
      let leftContext := head :: context in
      let rightContext := right :: context in
      trpOrE context head right target sourceProof
        (trpOrI1 leftContext
          (templatePreservedWitnessExists head) targetRight
          (trpExI leftContext
            (templateFormulaRename (templateUpRenaming S) head)
            (ttVar 0) (trpAss leftContext head)))
        (trpOrI2 rightContext
          (templatePreservedWitnessExists head) targetRight
          (templateRightDisjunctionPreserveWitnessFrom
            rightContext rest tail (trpAss rightContext right)))
  end.

Theorem templateRightDisjunctionPreserveWitnessFrom_derives : forall
    context prefix tail sourceProof,
  TemplateRawDerives context
    (templateRightDisjunction prefix tail) sourceProof ->
  TemplateRawDerives context
    (templateRightDisjunctionPreservedWitnessTarget prefix tail)
    (templateRightDisjunctionPreserveWitnessFrom
      context prefix tail sourceProof).
Proof.
  intros context prefix.
  revert context.
  induction prefix as [|head rest ih];
    intros context tail sourceProof hsource.
  - cbn [templateRightDisjunctionPreserveWitnessFrom
      templateRightDisjunctionPreservedWitnessTarget
      templateRightDisjunction].
    destruct hsource as [hvalid [hcontext hconclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    rewrite templateFormulaOpen_binderShift_zero.
    repeat split; assumption.
  - cbn [templateRightDisjunctionPreserveWitnessFrom
      templateRightDisjunctionPreservedWitnessTarget
      templateRightDisjunction map].
    set (right := templateRightDisjunction rest tail).
    set (targetRight :=
      templateRightDisjunctionPreservedWitnessTarget rest tail).
    set (leftContext := head :: context).
    set (rightContext := right :: context).
    assert (hrightSource : TemplateRawDerives rightContext right
        (trpAss rightContext right)).
    { apply templateRawDerives_assumption. left. reflexivity. }
    pose proof (ih rightContext tail
      (trpAss rightContext right) hrightSource) as hright.
    destruct hsource as [hsourceValid
      [hsourceContext hsourceConclusion]].
    destruct hright as [hrightValid
      [hrightContext hrightConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    rewrite templateFormulaOpen_binderShift_zero.
    repeat split; try assumption; try reflexivity.
    left. reflexivity.
Qed.

(** Renaming is structural across the finite disjunction.  This is the
    endpoint equation required by existential elimination. *)
Lemma templateFormulaRename_rightDisjunction : forall
    renaming prefix tail,
  templateFormulaRename renaming
    (templateRightDisjunction prefix tail) =
  templateRightDisjunction
    (map (templateFormulaRename renaming) prefix)
    (templateFormulaRename renaming tail).
Proof.
  intros renaming prefix.
  induction prefix as [|head rest ih]; intro tail; cbn.
  - reflexivity.
  - now rewrite ih.
Qed.

(** ------------------------------------------------------------------
    Distribute an arbitrary existential tower over the finite Or tree. *)

Definition templateRepeatedExistsDisjunctionTarget
    (binderCount : nat)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : TemplateFormula :=
  templateRightDisjunction
    (map (templateRepeatedExists binderCount) prefix)
    (templateRepeatedExists binderCount tail).

Lemma templateRepeatedExistsDisjunctionTarget_successor_rename : forall
    binderCount prefix tail,
  templateRightDisjunctionPreservedWitnessTarget
    (map (templateRepeatedExists binderCount) prefix)
    (templateRepeatedExists binderCount tail) =
  templateFormulaRename S
    (templateRepeatedExistsDisjunctionTarget
      (S binderCount) prefix tail).
Proof.
  intros binderCount prefix tail.
  unfold templateRightDisjunctionPreservedWitnessTarget,
    templateRepeatedExistsDisjunctionTarget.
  rewrite templateFormulaRename_rightDisjunction.
  rewrite !map_map.
  cbn [templateRepeatedExists templatePreservedWitnessExists].
  reflexivity.
Qed.

Fixpoint templateRepeatedExistsDisjunctionFrom
    (binderCount : nat) (context : TemplateContext)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match binderCount with
  | 0 => sourceProof
  | S smaller =>
      let sourceBody := templateRepeatedExists smaller
        (templateRightDisjunction prefix tail) in
      let eigenContext := sourceBody :: templateContextShift context in
      let distributedBody :=
        templateRepeatedExistsDisjunctionFrom smaller eigenContext
          prefix tail (trpAss eigenContext sourceBody) in
      let preservedBody :=
        templateRightDisjunctionPreserveWitnessFrom eigenContext
          (map (templateRepeatedExists smaller) prefix)
          (templateRepeatedExists smaller tail) distributedBody in
      trpExE context sourceBody
        (templateRepeatedExistsDisjunctionTarget
          (S smaller) prefix tail)
        sourceProof preservedBody
  end.

Theorem templateRepeatedExistsDisjunctionFrom_derives : forall
    binderCount context prefix tail sourceProof,
  TemplateRawDerives context
    (templateRepeatedExists binderCount
      (templateRightDisjunction prefix tail)) sourceProof ->
  TemplateRawDerives context
    (templateRepeatedExistsDisjunctionTarget binderCount prefix tail)
    (templateRepeatedExistsDisjunctionFrom binderCount context
      prefix tail sourceProof).
Proof.
  induction binderCount as [|smaller ih];
    intros context prefix tail sourceProof hsource.
  - unfold templateRepeatedExistsDisjunctionTarget.
    cbn [templateRepeatedExistsDisjunctionFrom
      templateRepeatedExists] in *.
    now rewrite map_id.
  - cbn [templateRepeatedExistsDisjunctionFrom
      templateRepeatedExists].
    set (sourceBody := templateRepeatedExists smaller
      (templateRightDisjunction prefix tail)).
    set (eigenContext := sourceBody :: templateContextShift context).
    assert (hbodySource : TemplateRawDerives eigenContext sourceBody
        (trpAss eigenContext sourceBody)).
    { apply templateRawDerives_assumption. left. reflexivity. }
    pose proof (ih eigenContext prefix tail
      (trpAss eigenContext sourceBody) hbodySource) as hdistributed.
    pose proof (templateRightDisjunctionPreserveWitnessFrom_derives
      eigenContext
      (map (templateRepeatedExists smaller) prefix)
      (templateRepeatedExists smaller tail)
      (templateRepeatedExistsDisjunctionFrom smaller eigenContext
        prefix tail (trpAss eigenContext sourceBody))
      hdistributed) as hpreserved.
    destruct hsource as [hsourceValid
      [hsourceContext hsourceConclusion]].
    destruct hpreserved as [hpreservedValid
      [hpreservedContext hpreservedConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    rewrite templateRepeatedExistsDisjunctionTarget_successor_rename
      in hpreservedConclusion.
    repeat split; try assumption; try reflexivity.
Qed.

(** Project the branch component out of [domain /\ branches], retaining all
    witnesses, and feed it to the distribution tree above. *)
Definition templateRepeatedExistsBranchDisjunctionFrom
    (binderCount : nat) (context : TemplateContext)
    (domain : TemplateFormula)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  let branchDisjunction := templateRightDisjunction prefix tail in
  let projected :=
    templateRepeatedExistsSelectionFrom binderCount context
      [domain] branchDisjunction [] 1 sourceProof in
  templateRepeatedExistsDisjunctionFrom binderCount context
    prefix tail projected.

Theorem templateRepeatedExistsBranchDisjunctionFrom_derives : forall
    binderCount context domain prefix tail sourceProof,
  TemplateRawDerives context
    (templateRepeatedExists binderCount
      (tfAnd domain (templateRightDisjunction prefix tail))) sourceProof ->
  TemplateRawDerives context
    (templateRepeatedExistsDisjunctionTarget binderCount prefix tail)
    (templateRepeatedExistsBranchDisjunctionFrom binderCount context
      domain prefix tail sourceProof).
Proof.
  intros binderCount context domain prefix tail sourceProof hsource.
  unfold templateRepeatedExistsBranchDisjunctionFrom.
  apply templateRepeatedExistsDisjunctionFrom_derives.
  pose proof (templateRepeatedExistsSelectionFrom_derives
    binderCount context [domain]
    (templateRightDisjunction prefix tail) [] 1 sourceProof) as hproject.
  cbn [templateRightConjunction
    templateSelectedRightConjunction
    templateRightConjunctionSelect] in hproject.
  exact (hproject hsource).
Qed.

Definition templateRepeatedExistsBranchDisjunctionFormula
    (binderCount : nat) (domain : TemplateFormula)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : TemplateFormula :=
  tfImp
    (templateRepeatedExists binderCount
      (tfAnd domain (templateRightDisjunction prefix tail)))
    (templateRepeatedExistsDisjunctionTarget binderCount prefix tail).

Definition templateRepeatedExistsBranchDisjunctionProof
    (binderCount : nat) (domain : TemplateFormula)
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : TemplateRawProof :=
  let source := templateRepeatedExists binderCount
    (tfAnd domain (templateRightDisjunction prefix tail)) in
  let context := [source] in
  trpImpI [] source
    (templateRepeatedExistsDisjunctionTarget binderCount prefix tail)
    (templateRepeatedExistsBranchDisjunctionFrom binderCount context
      domain prefix tail (trpAss context source)).

Theorem templateRepeatedExistsBranchDisjunctionProof_derives : forall
    binderCount domain prefix tail,
  TemplateRawDerives []
    (templateRepeatedExistsBranchDisjunctionFormula
      binderCount domain prefix tail)
    (templateRepeatedExistsBranchDisjunctionProof
      binderCount domain prefix tail).
Proof.
  intros binderCount domain prefix tail.
  unfold templateRepeatedExistsBranchDisjunctionFormula,
    templateRepeatedExistsBranchDisjunctionProof.
  set (source := templateRepeatedExists binderCount
    (tfAnd domain (templateRightDisjunction prefix tail))).
  set (context := [source]).
  assert (hsource : TemplateRawDerives context source
      (trpAss context source)).
  { apply templateRawDerives_assumption. left. reflexivity. }
  pose proof (templateRepeatedExistsBranchDisjunctionFrom_derives
    binderCount context domain prefix tail
    (trpAss context source) hsource) as hbody.
  destruct hbody as [hbodyValid [hbodyContext hbodyConclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; try assumption; try reflexivity.
Qed.

(** ------------------------------------------------------------------
    Exact Sigma Or7 and Pi Or6 template instances. *)

Definition coqDynamicTruthSigmaBranchPrefix : list TemplateFormula :=
  [coqDynamicTruthSigmaQfLeafTemplate;
   coqDynamicTruthSigmaImpFalseLeftLeafTemplate;
   coqDynamicTruthSigmaImpTrueRightLeafTemplate;
   coqDynamicTruthSigmaAndLeafTemplate;
   coqDynamicTruthSigmaOrLeafTemplate;
   coqDynamicTruthSigmaExLeafTemplate].

Definition coqDynamicTruthPiBranchPrefix : list TemplateFormula :=
  [coqDynamicTruthPiQfLeafTemplate;
   coqDynamicTruthPiImpLeafTemplate;
   coqDynamicTruthPiAndLeafTemplate;
   coqDynamicTruthPiOrLeafTemplate;
   coqDynamicTruthPiAllLeafTemplate].

Definition coqDynamicTruthSigmaSuccessorRowBranchDisjunctionTarget
    : TemplateFormula :=
  templateRepeatedExistsDisjunctionTarget 8
    coqDynamicTruthSigmaBranchPrefix
    coqDynamicTruthSigmaUniversalLeafTemplate.

Definition coqDynamicTruthPiSuccessorRowBranchDisjunctionTarget
    : TemplateFormula :=
  templateRepeatedExistsDisjunctionTarget 8
    coqDynamicTruthPiBranchPrefix
    coqDynamicTruthPiExistentialLeafTemplate.

Definition coqDynamicTruthSigmaSuccessorRowBranchDisjunctionFormula
    : TemplateFormula :=
  tfImp coqDynamicTruthSigmaSuccessorRowTemplate
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionTarget.

Definition coqDynamicTruthPiSuccessorRowBranchDisjunctionFormula
    : TemplateFormula :=
  tfImp coqDynamicTruthPiSuccessorRowTemplate
    coqDynamicTruthPiSuccessorRowBranchDisjunctionTarget.

Definition coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof
    : TemplateRawProof :=
  templateRepeatedExistsBranchDisjunctionProof 8
    coqDynamicTruthSigmaDomainLeafTemplate
    coqDynamicTruthSigmaBranchPrefix
    coqDynamicTruthSigmaUniversalLeafTemplate.

Definition coqDynamicTruthPiSuccessorRowBranchDisjunctionProof
    : TemplateRawProof :=
  templateRepeatedExistsBranchDisjunctionProof 8
    coqDynamicTruthPiDomainLeafTemplate
    coqDynamicTruthPiBranchPrefix
    coqDynamicTruthPiExistentialLeafTemplate.

Theorem coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionFormula
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof.
Proof.
  unfold coqDynamicTruthSigmaSuccessorRowBranchDisjunctionFormula,
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof,
    coqDynamicTruthSigmaSuccessorRowTemplate,
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionTarget,
    coqDynamicTruthSigmaBranchesTemplate,
    coqDynamicTruthSigmaBranchPrefix.
  apply templateRepeatedExistsBranchDisjunctionProof_derives.
Qed.

Theorem coqDynamicTruthPiSuccessorRowBranchDisjunctionProof_derives :
  TemplateRawDerives []
    coqDynamicTruthPiSuccessorRowBranchDisjunctionFormula
    coqDynamicTruthPiSuccessorRowBranchDisjunctionProof.
Proof.
  unfold coqDynamicTruthPiSuccessorRowBranchDisjunctionFormula,
    coqDynamicTruthPiSuccessorRowBranchDisjunctionProof,
    coqDynamicTruthPiSuccessorRowTemplate,
    coqDynamicTruthPiSuccessorRowBranchDisjunctionTarget,
    coqDynamicTruthPiBranchesTemplate,
    coqDynamicTruthPiBranchPrefix.
  apply templateRepeatedExistsBranchDisjunctionProof_derives.
Qed.

(** ------------------------------------------------------------------
    Identification with the literal native row and matrix targets. *)

Lemma rawDirect_coqDynamicTruthSigmaBranchDisjunctionTarget_identified :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionTarget =
  rawDynamicTruthLocalSigmaOr7Code M concreteLowerApplication.
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  unfold coqDynamicTruthSigmaSuccessorRowBranchDisjunctionTarget,
    coqDynamicTruthSigmaBranchPrefix,
    templateRepeatedExistsDisjunctionTarget,
    rawDynamicTruthLocalSigmaOr7Code,
    rawDynamicTruthSigmaQFEx8BranchCode,
    rawDynamicTruthSigmaQFRowCode,
    rawDynamicTruthSigmaImpFalseLeftEx8BranchCode,
    rawDynamicTruthSigmaImpFalseLeftRowCode,
    rawDynamicTruthSigmaImpTrueRightEx8BranchCode,
    rawDynamicTruthSigmaImpTrueRightRowCode,
    rawDynamicTruthSigmaAndEx8BranchCode,
    rawDynamicTruthSigmaOrEx8BranchCode,
    rawDynamicTruthSigmaEx8BranchCode,
    rawDynamicTruthSigmaUniversalEx8BranchCode.
  cbn [map templateRightDisjunction templateRepeatedExists
    rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  try rewrite rawDirect_coqDynamicTruthSigmaUniversalLeafTemplate.
  rewrite (rawCoqDynamicTruthSigmaDirect_lowerApplication_identified
    identification).
  rewrite !rawFixedFormulaNumeralCode_eq_quoted by exact hPA.
  reflexivity.
Qed.

Lemma rawDirect_coqDynamicTruthPiBranchDisjunctionTarget_identified :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiSuccessorRowBranchDisjunctionTarget =
  rawDynamicTruthLocalPiOr6Code M concreteLowerApplication.
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  unfold coqDynamicTruthPiSuccessorRowBranchDisjunctionTarget,
    coqDynamicTruthPiBranchPrefix,
    templateRepeatedExistsDisjunctionTarget,
    rawDynamicTruthLocalPiOr6Code,
    rawDynamicTruthPiQFEx8BranchCode,
    rawDynamicTruthPiQFRowCode,
    rawDynamicTruthPiImpEx8BranchCode,
    rawDynamicTruthPiImpRowCode,
    rawDynamicTruthPiAndEx8BranchCode,
    rawDynamicTruthPiOrEx8BranchCode,
    rawDynamicTruthPiAllEx8BranchCode,
    rawDynamicTruthPiExistentialEx8BranchCode.
  cbn [map templateRightDisjunction templateRepeatedExists
    rawDirectTemplateFormula
    rawStructuralTemplateFormulaWith].
  repeat rewrite rawDirectTemplateFormula_quantifier_embedPA.
  try rewrite rawDirect_coqDynamicTruthPiExistentialLeafTemplate.
  rewrite (rawCoqDynamicTruthPiDirect_lowerApplication_identified
    identification).
  rewrite !rawDynamicTruthPiFixedFormulaNumeralCode_eq_quoted
    by exact hPA.
  reflexivity.
Qed.

Lemma rawDirect_coqDynamicTruthSigmaBranchDisjunctionFormula_identified :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthSigmaDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthSigmaSuccessorRowBranchDisjunctionFormula =
  rawFormulaImpCode M
    (rawDynamicTruthSigmaSuccessorRowCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthLocalSigmaOr7Code M concreteLowerApplication).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  unfold coqDynamicTruthSigmaSuccessorRowBranchDisjunctionFormula.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  rewrite (rawDirect_coqDynamicTruthSigmaSuccessorRowTemplate_identified
    M inputs concreteDomain concreteLowerApplication identification).
  rewrite (rawCoqDynamicTruthSigmaSuccessorRowTemplateCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
  rewrite (rawDirect_coqDynamicTruthSigmaBranchDisjunctionTarget_identified
    M hPA inputs concreteDomain concreteLowerApplication identification).
  reflexivity.
Qed.

Lemma rawDirect_coqDynamicTruthPiBranchDisjunctionFormula_identified :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    concreteDomain concreteLowerApplication,
  RawCoqDynamicTruthPiDirectTemplateIdentification M inputs
    concreteDomain concreteLowerApplication ->
  rawDirectTemplateFormula inputs
    coqDynamicTruthPiSuccessorRowBranchDisjunctionFormula =
  rawFormulaImpCode M
    (rawDynamicTruthPiSuccessorRowCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthLocalPiOr6Code M concreteLowerApplication).
Proof.
  intros M hPA inputs concreteDomain concreteLowerApplication
    identification.
  unfold coqDynamicTruthPiSuccessorRowBranchDisjunctionFormula.
  cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith].
  rewrite (rawDirect_coqDynamicTruthPiSuccessorRowTemplate_identified
    M inputs concreteDomain concreteLowerApplication identification).
  rewrite (rawCoqDynamicTruthPiSuccessorRowTemplateCode_eq_native
    M hPA concreteDomain concreteLowerApplication).
  rewrite (rawDirect_coqDynamicTruthPiBranchDisjunctionTarget_identified
    M hPA inputs concreteDomain concreteLowerApplication identification).
  reflexivity.
Qed.

(** ------------------------------------------------------------------
    Same-context compilation.

    These two records expose precisely the nontransparent resources used by
    the compiler.  The direct structural inputs carry the represented atomic
    shift/open traces; the identification record designates the domain and
    lower-level atom; and the context contributes only realizability and its
    own one-place shift. *)

Record RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
    (M : RawPAModel) (context concreteDomain concreteLowerApplication : M)
    : Type := {
  rawDynamicTruthSigmaBranchDisjunction_contextRealizable :
    RawContextListRealizable M context;
  rawDynamicTruthSigmaBranchDisjunction_contextSelfShift :
    RawContextShift M context context;
  rawDynamicTruthSigmaBranchDisjunction_directInputs :
    RawCodedTemplateDirectStructuralInputs M;
  rawDynamicTruthSigmaBranchDisjunction_identification :
    RawCoqDynamicTruthSigmaDirectTemplateIdentification M
      rawDynamicTruthSigmaBranchDisjunction_directInputs
      concreteDomain concreteLowerApplication
}.

Record RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
    (M : RawPAModel) (context concreteDomain concreteLowerApplication : M)
    : Type := {
  rawDynamicTruthPiBranchDisjunction_contextRealizable :
    RawContextListRealizable M context;
  rawDynamicTruthPiBranchDisjunction_contextSelfShift :
    RawContextShift M context context;
  rawDynamicTruthPiBranchDisjunction_directInputs :
    RawCodedTemplateDirectStructuralInputs M;
  rawDynamicTruthPiBranchDisjunction_identification :
    RawCoqDynamicTruthPiDirectTemplateIdentification M
      rawDynamicTruthPiBranchDisjunction_directInputs
      concreteDomain concreteLowerApplication
}.

Arguments rawDynamicTruthSigmaBranchDisjunction_contextRealizable
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthSigmaBranchDisjunction_contextSelfShift
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthSigmaBranchDisjunction_directInputs
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthSigmaBranchDisjunction_identification
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthPiBranchDisjunction_contextRealizable
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthPiBranchDisjunction_contextSelfShift
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthPiBranchDisjunction_directInputs
  {M context concreteDomain concreteLowerApplication} _.
Arguments rawDynamicTruthPiBranchDisjunction_identification
  {M context concreteDomain concreteLowerApplication} _.

Definition rawDynamicTruthSigmaSuccessorRowBranchDisjunctionImpRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context concreteDomain concreteLowerApplication : M)
    (compilation :
      RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
    context coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof.

Definition rawDynamicTruthPiSuccessorRowBranchDisjunctionImpRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context concreteDomain concreteLowerApplication : M)
    (compilation :
      RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication) : M :=
  rawTemplateProofCodeOnTail
    (rawDirectStructuralTemplateTranslation M hPA
      (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
    context coqDynamicTruthPiSuccessorRowBranchDisjunctionProof.

Arguments rawDynamicTruthSigmaSuccessorRowBranchDisjunctionImpRoot
  M hPA context concreteDomain concreteLowerApplication compilation
  : clear implicits.
Arguments rawDynamicTruthPiSuccessorRowBranchDisjunctionImpRoot
  M hPA context concreteDomain concreteLowerApplication compilation
  : clear implicits.

Theorem
    raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowBranchDisjunctionImp :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    context concreteDomain concreteLowerApplication
    (compilation :
      RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication),
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawDynamicTruthSigmaSuccessorRowCode M
        concreteDomain concreteLowerApplication)
      (rawDynamicTruthLocalSigmaOr7Code M concreteLowerApplication))
    (rawDynamicTruthSigmaSuccessorRowBranchDisjunctionImpRoot
      M hPA context concreteDomain concreteLowerApplication compilation).
Proof.
  intros M hPA context concreteDomain concreteLowerApplication compilation.
  unfold rawDynamicTruthSigmaSuccessorRowBranchDisjunctionImpRoot.
  rewrite <-
    (rawDirect_coqDynamicTruthSigmaBranchDisjunctionFormula_identified
      M hPA
      (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation)
      concreteDomain concreteLowerApplication
      (rawDynamicTruthSigmaBranchDisjunction_identification compilation)).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
      context [])
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
      coqDynamicTruthSigmaSuccessorRowBranchDisjunctionFormula)
    (rawTemplateProofCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthSigmaBranchDisjunction_directInputs compilation))
      context coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof)).
  apply (raw_templateProofOnTail_localProof M hPA).
  - exact (rawDynamicTruthSigmaBranchDisjunction_contextRealizable
      compilation).
  - exact (rawDynamicTruthSigmaBranchDisjunction_contextSelfShift
      compilation).
  - exact (proj1
      coqDynamicTruthSigmaSuccessorRowBranchDisjunctionProof_derives).
Qed.

Theorem
    raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowBranchDisjunctionImp :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    context concreteDomain concreteLowerApplication
    (compilation :
      RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication),
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M
      (rawDynamicTruthPiSuccessorRowCode M
        concreteDomain concreteLowerApplication)
      (rawDynamicTruthLocalPiOr6Code M concreteLowerApplication))
    (rawDynamicTruthPiSuccessorRowBranchDisjunctionImpRoot
      M hPA context concreteDomain concreteLowerApplication compilation).
Proof.
  intros M hPA context concreteDomain concreteLowerApplication compilation.
  unfold rawDynamicTruthPiSuccessorRowBranchDisjunctionImpRoot.
  rewrite <-
    (rawDirect_coqDynamicTruthPiBranchDisjunctionFormula_identified
      M hPA
      (rawDynamicTruthPiBranchDisjunction_directInputs compilation)
      concreteDomain concreteLowerApplication
      (rawDynamicTruthPiBranchDisjunction_identification compilation)).
  change (RawCodedPALocalProofOf M
    (rawTemplateContextCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
      context [])
    (rawTemplateFormula
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
      coqDynamicTruthPiSuccessorRowBranchDisjunctionFormula)
    (rawTemplateProofCodeOnTail
      (rawDirectStructuralTemplateTranslation M hPA
        (rawDynamicTruthPiBranchDisjunction_directInputs compilation))
      context coqDynamicTruthPiSuccessorRowBranchDisjunctionProof)).
  apply (raw_templateProofOnTail_localProof M hPA).
  - exact (rawDynamicTruthPiBranchDisjunction_contextRealizable
      compilation).
  - exact (rawDynamicTruthPiBranchDisjunction_contextSelfShift
      compilation).
  - exact (proj1
      coqDynamicTruthPiSuccessorRowBranchDisjunctionProof_derives).
Qed.

(** Applying the compiled implication is the sole final assembly node. *)
Definition rawDynamicTruthSigmaSuccessorRowBranchDisjunctionRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context concreteDomain concreteLowerApplication : M)
    (compilation :
      RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication)
    (sourceRoot : M) : M :=
  rawProofImpERoot M context
    (rawDynamicTruthSigmaSuccessorRowCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthLocalSigmaOr7Code M concreteLowerApplication)
    (rawDynamicTruthSigmaSuccessorRowBranchDisjunctionImpRoot
      M hPA context concreteDomain concreteLowerApplication compilation)
    sourceRoot.

Definition rawDynamicTruthPiSuccessorRowBranchDisjunctionRoot
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (context concreteDomain concreteLowerApplication : M)
    (compilation :
      RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication)
    (sourceRoot : M) : M :=
  rawProofImpERoot M context
    (rawDynamicTruthPiSuccessorRowCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthLocalPiOr6Code M concreteLowerApplication)
    (rawDynamicTruthPiSuccessorRowBranchDisjunctionImpRoot
      M hPA context concreteDomain concreteLowerApplication compilation)
    sourceRoot.

Arguments rawDynamicTruthSigmaSuccessorRowBranchDisjunctionRoot
  M hPA context concreteDomain concreteLowerApplication compilation
  sourceRoot : clear implicits.
Arguments rawDynamicTruthPiSuccessorRowBranchDisjunctionRoot
  M hPA context concreteDomain concreteLowerApplication compilation
  sourceRoot : clear implicits.

Theorem raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowBranchDisjunction :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    context concreteDomain concreteLowerApplication
    (compilation :
      RawDynamicTruthSigmaSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication)
    sourceRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthSigmaSuccessorRowCode M
      concreteDomain concreteLowerApplication) sourceRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalSigmaOr7Code M concreteLowerApplication)
    (rawDynamicTruthSigmaSuccessorRowBranchDisjunctionRoot
      M hPA context concreteDomain concreteLowerApplication
      compilation sourceRoot).
Proof.
  intros M hPA context concreteDomain concreteLowerApplication
    compilation sourceRoot hsource.
  unfold rawDynamicTruthSigmaSuccessorRowBranchDisjunctionRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthSigmaSuccessorRowCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthLocalSigmaOr7Code M concreteLowerApplication)).
  - exact
      (raw_codedPALocalProofOf_dynamicTruthSigmaSuccessorRowBranchDisjunctionImp
        M hPA context concreteDomain concreteLowerApplication compilation).
  - exact hsource.
Qed.

Theorem raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowBranchDisjunction :
  forall (M : RawPAModel) (hPA : RawPASatisfies M)
    context concreteDomain concreteLowerApplication
    (compilation :
      RawDynamicTruthPiSuccessorRowBranchDisjunctionCompilationInputs
        M context concreteDomain concreteLowerApplication)
    sourceRoot,
  RawCodedPALocalProofOf M context
    (rawDynamicTruthPiSuccessorRowCode M
      concreteDomain concreteLowerApplication) sourceRoot ->
  RawCodedPALocalProofOf M context
    (rawDynamicTruthLocalPiOr6Code M concreteLowerApplication)
    (rawDynamicTruthPiSuccessorRowBranchDisjunctionRoot
      M hPA context concreteDomain concreteLowerApplication
      compilation sourceRoot).
Proof.
  intros M hPA context concreteDomain concreteLowerApplication
    compilation sourceRoot hsource.
  unfold rawDynamicTruthPiSuccessorRowBranchDisjunctionRoot.
  apply (raw_codedPALocalProofOf_impE M hPA context
    (rawDynamicTruthPiSuccessorRowCode M
      concreteDomain concreteLowerApplication)
    (rawDynamicTruthLocalPiOr6Code M concreteLowerApplication)).
  - exact
      (raw_codedPALocalProofOf_dynamicTruthPiSuccessorRowBranchDisjunctionImp
        M hPA context concreteDomain concreteLowerApplication compilation).
  - exact hsource.
Qed.

End
  PABoundedRawCodedDynamicTruthSuccessorRowBranchDisjunctionCompilation.
