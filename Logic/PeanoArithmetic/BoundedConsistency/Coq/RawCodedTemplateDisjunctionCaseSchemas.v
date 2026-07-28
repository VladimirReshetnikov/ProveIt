(**
  Transparent finite-disjunction case schemas for model-coded proofs.

  A dynamic truth row is a right-associated disjunction: the Sigma row has
  seven alternatives and the Pi row has six.  Projecting only one selected
  alternative is not enough for the successor construction.  The represented
  proof must inspect the actual row and produce the same conclusion in every
  branch.

  This module records that purely logical step once.  The first construction
  eliminates a right-associated disjunction in an arbitrary context, provided
  that the context contains an implication from every branch to a common
  conclusion.  The second construction introduces those implications and
  packages the result as the closed tautology

      (A1 or ... or Ak) ->
        (A1 -> C) -> ... -> (Ak -> C) -> C.

  Both proof trees are transparent [TemplateRawProof] values.  Consequently a
  later dynamic-truth compiler may instantiate the branch formulas and compile
  the tree directly; no appeal to completeness or to a metatheoretic decision
  of the represented disjunction is hidden here.
*)

From Stdlib Require Import List.
From BoundedPAConsistency Require Import RawCodedTemplateSyntax.

Import ListNotations.

Module PABoundedRawCodedTemplateDisjunctionCaseSchemas.

Import PABoundedRawCodedTemplateSyntax.

(** ------------------------------------------------------------------
    Right-associated disjunctions. *)

Fixpoint templateRightDisjunction
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : TemplateFormula :=
  match prefix with
  | [] => tail
  | head :: rest => tfOr head (templateRightDisjunction rest tail)
  end.

(** Every branch is represented exactly once by [prefix ++ [tail]]. *)
Definition templateRightDisjunctionBranches
    (prefix : list TemplateFormula) (tail : TemplateFormula)
    : list TemplateFormula :=
  prefix ++ [tail].

(** ------------------------------------------------------------------
    Elimination under already available branch implications.

    Recursive calls add the right disjunct to the front of the context.  This
    is why the construction takes the complete context explicitly instead of
    pretending that natural-deduction weakening is definitional. *)

Fixpoint templateRightDisjunctionCasesFrom
    (context : TemplateContext)
    (prefix : list TemplateFormula) (tail conclusion : TemplateFormula)
    (sourceProof : TemplateRawProof) : TemplateRawProof :=
  match prefix with
  | [] =>
      trpImpE context tail conclusion
        (trpAss context (tfImp tail conclusion)) sourceProof
  | head :: rest =>
      let right := templateRightDisjunction rest tail in
      let leftContext := head :: context in
      let rightContext := right :: context in
      trpOrE context head right conclusion sourceProof
        (trpImpE leftContext head conclusion
          (trpAss leftContext (tfImp head conclusion))
          (trpAss leftContext head))
        (templateRightDisjunctionCasesFrom rightContext
          rest tail conclusion (trpAss rightContext right))
  end.

Theorem templateRightDisjunctionCasesFrom_derives : forall
    context prefix tail conclusion sourceProof,
  TemplateRawDerives context
    (templateRightDisjunction prefix tail) sourceProof ->
  (forall branch,
    In branch (templateRightDisjunctionBranches prefix tail) ->
    In (tfImp branch conclusion) context) ->
  TemplateRawDerives context conclusion
    (templateRightDisjunctionCasesFrom
      context prefix tail conclusion sourceProof).
Proof.
  intros context prefix.
  revert context.
  induction prefix as [|head rest ih];
    intros context tail conclusion sourceProof hsource hbranches.
  - cbn [templateRightDisjunctionCasesFrom
      templateRightDisjunctionBranches] in *.
    destruct hsource as [hsourceValid [hsourceContext hsourceConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; try assumption; try reflexivity.
    apply hbranches. left. reflexivity.
  - cbn [templateRightDisjunctionCasesFrom templateRightDisjunction].
    set (right := templateRightDisjunction rest tail).
    set (leftContext := head :: context).
    set (rightContext := right :: context).
    assert (hleftImplication :
        In (tfImp head conclusion) leftContext).
    { right. apply hbranches. unfold templateRightDisjunctionBranches.
      apply in_or_app. left. left. reflexivity. }
    assert (hleftBranch : In head leftContext).
    { left. reflexivity. }
    assert (hrightSource : TemplateRawDerives rightContext right
        (trpAss rightContext right)).
    { apply templateRawDerives_assumption. left. reflexivity. }
    assert (hrightBranches : forall branch,
        In branch (templateRightDisjunctionBranches rest tail) ->
        In (tfImp branch conclusion) rightContext).
    { intros branch hbranch. right. apply hbranches.
      unfold templateRightDisjunctionBranches in *.
      apply in_app_iff in hbranch as [hinRest | hinTail].
      - apply in_app_iff. left. right. exact hinRest.
      - apply in_app_iff. right. exact hinTail. }
    pose proof (ih rightContext tail conclusion
      (trpAss rightContext right) hrightSource hrightBranches) as hright.
    destruct hsource as [hsourceValid [hsourceContext hsourceConclusion]].
    destruct hright as [hrightValid [hrightContext hrightConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; try assumption; try reflexivity.
Qed.

(** ------------------------------------------------------------------
    A closed curried case rule.

    [available] stores, in reverse introduction order, the branches whose
    implications are already assumptions.  It has no semantic role in the
    proof term; threading it makes the context invariant explicit and keeps
    the validity proof honest. *)

Fixpoint templateCaseImplicationChain
    (branches : list TemplateFormula) (conclusion : TemplateFormula)
    : TemplateFormula :=
  match branches with
  | [] => conclusion
  | branch :: rest =>
      tfImp (tfImp branch conclusion)
        (templateCaseImplicationChain rest conclusion)
  end.

Fixpoint templateRightDisjunctionCaseImplicationsFrom
    (context : TemplateContext) (available remaining : list TemplateFormula)
    (prefix : list TemplateFormula) (tail conclusion : TemplateFormula)
    : TemplateRawProof :=
  match remaining with
  | [] =>
      templateRightDisjunctionCasesFrom context
        prefix tail conclusion
        (trpAss context (templateRightDisjunction prefix tail))
  | branch :: rest =>
      trpImpI context (tfImp branch conclusion)
        (templateCaseImplicationChain rest conclusion)
        (templateRightDisjunctionCaseImplicationsFrom
          (tfImp branch conclusion :: context)
          (branch :: available) rest prefix tail conclusion)
  end.

Lemma templateRightDisjunctionCaseImplicationsFrom_derives : forall
    context available remaining prefix tail conclusion,
  rev available ++ remaining =
    templateRightDisjunctionBranches prefix tail ->
  In (templateRightDisjunction prefix tail) context ->
  (forall branch, In branch available ->
    In (tfImp branch conclusion) context) ->
  TemplateRawDerives context
    (templateCaseImplicationChain remaining conclusion)
    (templateRightDisjunctionCaseImplicationsFrom
      context available remaining prefix tail conclusion).
Proof.
  intros context available remaining.
  revert context available.
  induction remaining as [|branch rest ih];
    intros context available prefix tail conclusion
      hall hdisjunction havailable.
  - cbn [templateCaseImplicationChain
      templateRightDisjunctionCaseImplicationsFrom].
    apply templateRightDisjunctionCasesFrom_derives.
    + apply templateRawDerives_assumption. exact hdisjunction.
    + intros selected hselected.
      apply havailable.
      apply (proj2 (in_rev available selected)).
      rewrite <- hall in hselected.
      rewrite app_nil_r in hselected.
      exact hselected.
  - cbn [templateCaseImplicationChain
      templateRightDisjunctionCaseImplicationsFrom].
    assert (hallNext :
        rev (branch :: available) ++ rest =
        templateRightDisjunctionBranches prefix tail).
    { cbn [rev]. rewrite <- app_assoc. cbn. exact hall. }
    assert (hdisjunctionNext :
        In (templateRightDisjunction prefix tail)
          (tfImp branch conclusion :: context)).
    { right. exact hdisjunction. }
    assert (havailableNext : forall selected,
        In selected (branch :: available) ->
        In (tfImp selected conclusion)
          (tfImp branch conclusion :: context)).
    { intros selected [<- | hin].
      - left. reflexivity.
      - right. now apply havailable. }
    pose proof (ih (tfImp branch conclusion :: context)
      (branch :: available) prefix tail conclusion
      hallNext hdisjunctionNext havailableNext) as hchild.
    destruct hchild as [hchildValid [hchildContext hchildConclusion]].
    unfold TemplateRawDerives.
    cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
    repeat split; assumption.
Qed.

Definition templateRightDisjunctionCaseRuleFormula
    (prefix : list TemplateFormula) (tail conclusion : TemplateFormula)
    : TemplateFormula :=
  tfImp (templateRightDisjunction prefix tail)
    (templateCaseImplicationChain
      (templateRightDisjunctionBranches prefix tail) conclusion).

Definition templateRightDisjunctionCaseRuleProof
    (prefix : list TemplateFormula) (tail conclusion : TemplateFormula)
    : TemplateRawProof :=
  let disjunction := templateRightDisjunction prefix tail in
  let branches := templateRightDisjunctionBranches prefix tail in
  trpImpI [] disjunction
    (templateCaseImplicationChain branches conclusion)
    (templateRightDisjunctionCaseImplicationsFrom
      [disjunction] [] branches prefix tail conclusion).

Theorem templateRightDisjunctionCaseRuleProof_derives : forall
    prefix tail conclusion,
  TemplateRawDerives []
    (templateRightDisjunctionCaseRuleFormula prefix tail conclusion)
    (templateRightDisjunctionCaseRuleProof prefix tail conclusion).
Proof.
  intros prefix tail conclusion.
  unfold templateRightDisjunctionCaseRuleFormula,
    templateRightDisjunctionCaseRuleProof.
  pose proof (templateRightDisjunctionCaseImplicationsFrom_derives
    [templateRightDisjunction prefix tail] []
    (templateRightDisjunctionBranches prefix tail)
    prefix tail conclusion) as hbody.
  cbn [rev] in hbody.
  specialize (hbody eq_refl (or_introl eq_refl)).
  assert (hempty : forall branch : TemplateFormula,
      In branch [] ->
      In (tfImp branch conclusion)
        [templateRightDisjunction prefix tail]).
  { intros branch hin. contradiction. }
  specialize (hbody hempty).
  destruct hbody as [hvalid [hcontext hconclusion]].
  unfold TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion].
  repeat split; assumption.
Qed.

(** Named arity wrappers match the two native successor-row shapes. *)
Definition templateOr7CaseRuleProof
    (first second third fourth fifth sixth seventh conclusion
      : TemplateFormula) : TemplateRawProof :=
  templateRightDisjunctionCaseRuleProof
    [first; second; third; fourth; fifth; sixth] seventh conclusion.

Definition templateOr6CaseRuleProof
    (first second third fourth fifth sixth conclusion : TemplateFormula)
    : TemplateRawProof :=
  templateRightDisjunctionCaseRuleProof
    [first; second; third; fourth; fifth] sixth conclusion.

Corollary templateOr7CaseRuleProof_derives : forall
    first second third fourth fifth sixth seventh conclusion,
  TemplateRawDerives []
    (templateRightDisjunctionCaseRuleFormula
      [first; second; third; fourth; fifth; sixth] seventh conclusion)
    (templateOr7CaseRuleProof first second third fourth
      fifth sixth seventh conclusion).
Proof.
  intros. apply templateRightDisjunctionCaseRuleProof_derives.
Qed.

Corollary templateOr6CaseRuleProof_derives : forall
    first second third fourth fifth sixth conclusion,
  TemplateRawDerives []
    (templateRightDisjunctionCaseRuleFormula
      [first; second; third; fourth; fifth] sixth conclusion)
    (templateOr6CaseRuleProof first second third fourth
      fifth sixth conclusion).
Proof.
  intros. apply templateRightDisjunctionCaseRuleProof_derives.
Qed.

End PABoundedRawCodedTemplateDisjunctionCaseSchemas.
