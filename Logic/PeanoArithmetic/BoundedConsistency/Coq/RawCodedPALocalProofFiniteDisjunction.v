(**
  Carrier-coded finite disjunction elimination without formula decoding.

  A dynamic-truth row stores its alternatives as a right-associated finite
  disjunction.  Its branch codes may be nonstandard elements of an arbitrary
  PA model, so a useful case rule cannot first decode them to Rocq formulae.
  This module instead compiles the propositional tautology

      (A1 \/ ... \/ Ak) ->
        (A1 -> C) -> ... -> (Ak -> C) -> C

  directly from a metatheoretic list of carrier codes.  The empty list is
  represented by bottom; its case rule is therefore [bottom -> C].  A
  singleton is represented by its sole element, and lists of length at least
  two use the expected right-associated Or tree.  Thus the six- and
  seven-branch dynamic rows receive their literal native shapes, without a
  trailing disjunction with bottom.

  Every temporary context below is [rawListCode] of an explicit
  metatheoretic list.  We prove those exact contexts realizable and prove
  membership of each assumption before constructing an assumption leaf.
  No formula-code adequacy premise is necessary: none of the propositional
  rules shifts or otherwise inspects a formula code.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofUnaryConstructors
  RawCodedProofBinaryConstructors
  RawCodedProofImpIConstructor
  RawCodedProofOrEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules.

Import ListNotations.

Module PABoundedRawCodedPALocalProofFiniteDisjunction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofUnaryConstructors.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.

(** ------------------------------------------------------------------
    Formula-code folds. *)

(** The special singleton clause prevents the native six- and seven-way
    disjunctions from acquiring an artificial final [or bottom]. *)
Fixpoint rawFiniteRightDisjunctionCode
    (M : RawPAModel) (branches : list M) : M :=
  match branches with
  | [] => rawFormulaBotCode M
  | branch :: [] => branch
  | branch :: tail =>
      rawFormulaOrCode M branch
        (rawFiniteRightDisjunctionCode M tail)
  end.

Arguments rawFiniteRightDisjunctionCode M branches : clear implicits.

(** Curried case hypotheses, in the same left-to-right order as [branches]. *)
Fixpoint rawFiniteDisjunctionCaseChainCode
    (M : RawPAModel) (branches : list M) (conclusion : M) : M :=
  match branches with
  | [] => conclusion
  | branch :: tail =>
      rawFormulaImpCode M (rawFormulaImpCode M branch conclusion)
        (rawFiniteDisjunctionCaseChainCode M tail conclusion)
  end.

Arguments rawFiniteDisjunctionCaseChainCode
  M branches conclusion : clear implicits.

Definition rawFiniteDisjunctionCaseRuleCode
    (M : RawPAModel) (branches : list M) (conclusion : M) : M :=
  rawFormulaImpCode M
    (rawFiniteRightDisjunctionCode M branches)
    (rawFiniteDisjunctionCaseChainCode M branches conclusion).

Arguments rawFiniteDisjunctionCaseRuleCode
  M branches conclusion : clear implicits.

(** Concrete shape checks used by the native Sigma and Pi row clients. *)
Lemma rawFiniteRightDisjunctionCode_six : forall
    (M : RawPAModel) a b c d e f,
  rawFiniteRightDisjunctionCode M [a; b; c; d; e; f] =
  rawFormulaOrCode M a
    (rawFormulaOrCode M b
      (rawFormulaOrCode M c
        (rawFormulaOrCode M d
          (rawFormulaOrCode M e f)))).
Proof. reflexivity. Qed.

Lemma rawFiniteRightDisjunctionCode_seven : forall
    (M : RawPAModel) a b c d e f g,
  rawFiniteRightDisjunctionCode M [a; b; c; d; e; f; g] =
  rawFormulaOrCode M a
    (rawFormulaOrCode M b
      (rawFormulaOrCode M c
        (rawFormulaOrCode M d
          (rawFormulaOrCode M e
            (rawFormulaOrCode M f g))))).
Proof. reflexivity. Qed.

(** ------------------------------------------------------------------
    Honest contexts and assumption leaves. *)

Lemma raw_contextList_rawListCode_realizable : forall
    (M : RawPAModel), RawPASatisfies M -> forall entries : list M,
  RawContextListRealizable M (rawListCode M entries).
Proof.
  intros M hPA entries.
  induction entries as [| head tail ih].
  - exact (raw_contextList_empty_realizable M hPA).
  - cbn [rawListCode].
    exact (raw_contextList_cons_realizable M hPA
      (rawListCode M tail) head ih).
Qed.

Lemma raw_contextList_rawListCode_member : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (entries : list M) member,
  In member entries ->
  RawContextListMember M (rawListCode M entries) member.
Proof.
  intros M hPA entries.
  induction entries as [| head tail ih]; intros member hmember.
  - contradiction.
  - cbn [rawListCode] in *.
    destruct hmember as [hmember | hmember].
    + subst member.
      exact (raw_contextList_cons_head_member M hPA
        (rawListCode M tail) head
        (raw_contextList_rawListCode_realizable M hPA tail)).
    + exact (raw_contextList_cons_tail_member M hPA
        (rawListCode M tail) head member
        (ih member hmember)).
Qed.

(** Unlike the head-only convenience theorem, this leaf may select any
    member of an explicit finite context.  Its membership proof is still an
    honest model-internal context traversal. *)
Theorem raw_codedPALocalProofOf_rawListCode_assumption : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (entries : list M) formulaCode,
  In formulaCode entries ->
  RawCodedPALocalProofOf M
    (rawListCode M entries) formulaCode
    (rawProofAssumptionRoot M
      (rawListCode M entries) formulaCode).
Proof.
  intros M hPA entries formulaCode hmember.
  split.
  - exact (raw_proofAssumption_ruleCoverage M hPA
      (rawListCode M entries) formulaCode
      (raw_contextList_rawListCode_member M hPA
        entries formulaCode hmember)).
  - exact (raw_proofAssumption_endpoint M
      (rawListCode M entries) formulaCode).
Qed.

(** ------------------------------------------------------------------
    The open finite case tree. *)

(** [context] contains the disjunction assumption and all curried case
    implications.  Recursive right branches add the remaining disjunction at
    the literal head required by Or-E. *)
Fixpoint rawFiniteDisjunctionEliminationRoot
    (M : RawPAModel) (branches : list M)
    (conclusion : M) (context : list M) : M :=
  match branches with
  | [] =>
      rawProofBotERoot M (rawListCode M context) conclusion
        (rawProofAssumptionRoot M
          (rawListCode M context) (rawFormulaBotCode M))
  | branch :: [] =>
      rawProofImpERoot M (rawListCode M context) branch conclusion
        (rawProofAssumptionRoot M (rawListCode M context)
          (rawFormulaImpCode M branch conclusion))
        (rawProofAssumptionRoot M (rawListCode M context) branch)
  | branch :: tail =>
      let remainder := rawFiniteRightDisjunctionCode M tail in
      let whole := rawFormulaOrCode M branch remainder in
      let leftContext := branch :: context in
      let rightContext := remainder :: context in
      rawProofOrERoot M (rawListCode M context)
        branch remainder conclusion
        (rawProofAssumptionRoot M (rawListCode M context) whole)
        (rawProofImpERoot M (rawListCode M leftContext)
          branch conclusion
          (rawProofAssumptionRoot M (rawListCode M leftContext)
            (rawFormulaImpCode M branch conclusion))
          (rawProofAssumptionRoot M
            (rawListCode M leftContext) branch))
        (rawFiniteDisjunctionEliminationRoot M tail
          conclusion rightContext)
  end.

Arguments rawFiniteDisjunctionEliminationRoot
  M branches conclusion context : clear implicits.

(** The premises are purely metatheoretic membership facts about the explicit
    [context] list.  No adequacy predicate on any carrier formula is used. *)
Theorem raw_codedPALocalProofOf_finiteDisjunctionElimination : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (branches : list M) conclusion context,
  In (rawFiniteRightDisjunctionCode M branches) context ->
  (forall branch,
    In branch branches ->
    In (rawFormulaImpCode M branch conclusion) context) ->
  RawCodedPALocalProofOf M
    (rawListCode M context) conclusion
    (rawFiniteDisjunctionEliminationRoot M
      branches conclusion context).
Proof.
  intros M hPA branches.
  induction branches as [| branch tail ih];
    intros conclusion context hdisjunction hcases.
  - cbn [rawFiniteRightDisjunctionCode
      rawFiniteDisjunctionEliminationRoot] in *.
    apply (raw_codedPALocalProofOf_botE M hPA
      (rawListCode M context)
      (rawProofAssumptionRoot M
        (rawListCode M context) (rawFormulaBotCode M))).
    exact (raw_codedPALocalProofOf_rawListCode_assumption M hPA
      context (rawFormulaBotCode M) hdisjunction).
  - destruct tail as [| next rest].
    + cbn [rawFiniteRightDisjunctionCode
        rawFiniteDisjunctionEliminationRoot] in *.
      apply (raw_codedPALocalProofOf_impE M hPA
        (rawListCode M context) branch conclusion).
      * exact (raw_codedPALocalProofOf_rawListCode_assumption M hPA
          context (rawFormulaImpCode M branch conclusion)
          (hcases branch (or_introl eq_refl))).
      * exact (raw_codedPALocalProofOf_rawListCode_assumption M hPA
          context branch hdisjunction).
    + cbn [rawFiniteRightDisjunctionCode
        rawFiniteDisjunctionEliminationRoot] in *.
      apply (raw_codedPALocalProofOf_orE M hPA
        (rawListCode M context) branch
        (rawFiniteRightDisjunctionCode M (next :: rest)) conclusion).
      * exact (raw_codedPALocalProofOf_rawListCode_assumption M hPA
          context
          (rawFormulaOrCode M branch
            (rawFiniteRightDisjunctionCode M (next :: rest)))
          hdisjunction).
      * apply (raw_codedPALocalProofOf_impE M hPA
          (rawListCode M (branch :: context)) branch conclusion).
        -- exact (raw_codedPALocalProofOf_rawListCode_assumption M hPA
             (branch :: context)
             (rawFormulaImpCode M branch conclusion)
             (or_intror (hcases branch (or_introl eq_refl)))).
        -- exact (raw_codedPALocalProofOf_rawListCode_assumption M hPA
             (branch :: context) branch (or_introl eq_refl)).
      * apply (ih conclusion
          (rawFiniteRightDisjunctionCode M (next :: rest) :: context)).
        -- exact (or_introl eq_refl).
        -- intros selected hselected.
           exact (or_intror
             (hcases selected (or_intror hselected))).
Qed.

(** ------------------------------------------------------------------
    Curried implication introduction and the closed case rule. *)

Fixpoint rawFiniteDisjunctionCaseIntroductionRoot
    (M : RawPAModel) (allBranches remaining : list M)
    (conclusion : M) (context : list M) : M :=
  match remaining with
  | [] =>
      rawFiniteDisjunctionEliminationRoot M
        allBranches conclusion context
  | branch :: tail =>
      let caseCode := rawFormulaImpCode M branch conclusion in
      rawProofImpIRoot M (rawListCode M context)
        caseCode
        (rawFiniteDisjunctionCaseChainCode M tail conclusion)
        (rawFiniteDisjunctionCaseIntroductionRoot M
          allBranches tail conclusion (caseCode :: context))
  end.

Arguments rawFiniteDisjunctionCaseIntroductionRoot
  M allBranches remaining conclusion context : clear implicits.

(** [remaining] records the implications not yet introduced.  The invariant
    says that every branch is either still pending or already has its case
    implication in the exact current context. *)
Lemma raw_codedPALocalProofOf_finiteDisjunctionCaseIntroduction : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (allBranches remaining : list M) conclusion context,
  In (rawFiniteRightDisjunctionCode M allBranches) context ->
  (forall branch,
    In branch allBranches ->
    In branch remaining \/
    In (rawFormulaImpCode M branch conclusion) context) ->
  RawCodedPALocalProofOf M
    (rawListCode M context)
    (rawFiniteDisjunctionCaseChainCode M remaining conclusion)
    (rawFiniteDisjunctionCaseIntroductionRoot M
      allBranches remaining conclusion context).
Proof.
  intros M hPA allBranches remaining.
  induction remaining as [| branch tail ih];
    intros conclusion context hdisjunction hinvariant.
  - cbn [rawFiniteDisjunctionCaseChainCode
      rawFiniteDisjunctionCaseIntroductionRoot] in *.
    apply (raw_codedPALocalProofOf_finiteDisjunctionElimination
      M hPA allBranches conclusion context hdisjunction).
    intros selected hselected.
    specialize (hinvariant selected hselected).
    destruct hinvariant as [himpossible | hpresent].
    + contradiction.
    + exact hpresent.
  - cbn [rawFiniteDisjunctionCaseChainCode
      rawFiniteDisjunctionCaseIntroductionRoot] in *.
    apply (raw_codedPALocalProofOf_impI M hPA
      (rawListCode M context)
      (rawFormulaImpCode M branch conclusion)
      (rawFiniteDisjunctionCaseChainCode M tail conclusion)).
    apply (ih conclusion
      (rawFormulaImpCode M branch conclusion :: context)).
    + exact (or_intror hdisjunction).
    + intros selected hselected.
      specialize (hinvariant selected hselected).
      destruct hinvariant as [hpending | hpresent].
      * destruct hpending as [heq | hpending].
        -- subst selected. right. exact (or_introl eq_refl).
        -- left. exact hpending.
      * right. exact (or_intror hpresent).
Qed.

Definition rawFiniteDisjunctionCaseRuleProofRoot
    (M : RawPAModel) (branches : list M) (conclusion : M) : M :=
  let disjunction := rawFiniteRightDisjunctionCode M branches in
  rawProofImpIRoot M (raw_zero M)
    disjunction
    (rawFiniteDisjunctionCaseChainCode M branches conclusion)
    (rawFiniteDisjunctionCaseIntroductionRoot M
      branches branches conclusion [disjunction]).

Arguments rawFiniteDisjunctionCaseRuleProofRoot
  M branches conclusion : clear implicits.

(** Fully closed carrier-code compiler for the finite case tautology. *)
Theorem raw_codedPALocalProofOf_finiteDisjunctionCaseRule : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (branches : list M) conclusion,
  RawCodedPALocalProofOf M (raw_zero M)
    (rawFiniteDisjunctionCaseRuleCode M branches conclusion)
    (rawFiniteDisjunctionCaseRuleProofRoot M branches conclusion).
Proof.
  intros M hPA branches conclusion.
  unfold rawFiniteDisjunctionCaseRuleCode,
    rawFiniteDisjunctionCaseRuleProofRoot.
  apply (raw_codedPALocalProofOf_impI M hPA
    (raw_zero M)
    (rawFiniteRightDisjunctionCode M branches)
    (rawFiniteDisjunctionCaseChainCode M branches conclusion)).
  change (RawCodedPALocalProofOf M
    (rawListCode M [rawFiniteRightDisjunctionCode M branches])
    (rawFiniteDisjunctionCaseChainCode M branches conclusion)
    (rawFiniteDisjunctionCaseIntroductionRoot M
      branches branches conclusion
      [rawFiniteRightDisjunctionCode M branches])).
  apply (raw_codedPALocalProofOf_finiteDisjunctionCaseIntroduction
    M hPA branches branches conclusion
    [rawFiniteRightDisjunctionCode M branches]).
  - exact (or_introl eq_refl).
  - intros branch hbranch. left. exact hbranch.
Qed.

End PABoundedRawCodedPALocalProofFiniteDisjunction.
