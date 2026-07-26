(**
  Derived finite-disjunction elimination in an arbitrary coded context.

  [RawCodedPALocalProofFiniteDisjunction] compiles the closed curried case
  tautology.  Many clients already have a proof of the row and one proof of
  every branch implication in a common, possibly nonstandard, coded context.
  This module combines those proofs directly.

  The only subtlety is Or-E's literal child contexts.  A proof of [Ai -> C]
  over [Gamma] must be rebuilt over [Ai :: Gamma], and every remaining case
  proof must be rebuilt over [(Ai+1 or ...) :: Gamma].  We use the published
  guarded cons-transplant theorem for exactly those moves.  Consequently the
  new head codes, and only those codes, need atomic adequacy; [Gamma] needs an
  honest traversal whenever the row has at least two alternatives.

  [RawFiniteDisjunctionDerivedCaseResources] records that exact recursive
  boundary.  Empty and singleton rows require no transplant resource.  A
  nontrivial row records adequacy of its left branch, adequacy of its right
  disjunction, and the resources needed recursively by the tail.  No formula
  code is decoded, and no arbitrary weakening principle is assumed.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedProofAssumptionLeaf
  RawCodedProofBinaryConstructors
  RawCodedProofOrEConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofFiniteDisjunction.

Import ListNotations.

Module PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedProofAssumptionLeaf.
Import PABoundedRawCodedProofBinaryConstructors.
Import PABoundedRawCodedProofOrEConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.

(** A proof of every branch implication in one literal context. *)
Definition RawCodedPALocalFiniteDisjunctionCaseFamily
    (M : RawPAModel) (context : M)
    (branches : list M) (conclusion : M) : Prop :=
  forall branch,
    In branch branches ->
    exists root,
      RawCodedPALocalProofOf M context
        (rawFormulaImpCode M branch conclusion) root.

Arguments RawCodedPALocalFiniteDisjunctionCaseFamily
  M context branches conclusion : clear implicits.

(** Exact adequacy consumed by recursive cons transplants.  The singleton
    clause is [True]: modus ponens in the original context needs no context
    change. *)
Fixpoint RawFiniteDisjunctionConsTransplantAdequate
    (M : RawPAModel) (branches : list M) : Prop :=
  match branches with
  | [] => True
  | _ :: [] => True
  | branch :: tail =>
      RawCodedFormulaAtomicallyAdequate M branch /\
      RawCodedFormulaAtomicallyAdequate M
        (rawFiniteRightDisjunctionCode M tail) /\
      RawFiniteDisjunctionConsTransplantAdequate M tail
  end.

Arguments RawFiniteDisjunctionConsTransplantAdequate
  M branches : clear implicits.

(** Empty and singleton rows need neither a context traversal nor a
    transplant adequacy witness.  Every longer row needs both. *)
Definition RawFiniteDisjunctionDerivedCaseResources
    (M : RawPAModel) (branches : list M) (context : M) : Prop :=
  match branches with
  | [] => True
  | _ :: [] => True
  | _ :: _ :: _ =>
      RawContextListRealizable M context /\
      RawFiniteDisjunctionConsTransplantAdequate M branches
  end.

Arguments RawFiniteDisjunctionDerivedCaseResources
  M branches context : clear implicits.

(** The right Or-E child receives the tail disjunction at its head.  This
    lemma packages exactly the resources inherited by that recursive call.
    In the nontrivial-tail case its context traversal is obtained by honest
    cons extension, not postulated. *)
Lemma raw_finiteDisjunctionDerivedCaseResources_tail : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      branch tail context,
  RawFiniteDisjunctionDerivedCaseResources M
    (branch :: tail) context ->
  RawFiniteDisjunctionDerivedCaseResources M tail
    (rawListNode M
      (rawFiniteRightDisjunctionCode M tail) context).
Proof.
  intros M hPA branch tail context hresources.
  destruct tail as [| next rest].
  - exact I.
  - destruct rest as [| third more].
    + exact I.
    + cbn [RawFiniteDisjunctionDerivedCaseResources
        RawFiniteDisjunctionConsTransplantAdequate] in *.
      destruct hresources as [hcontext
        [hbranch [hremainder htail]]].
      split.
      * exact (raw_contextList_cons_realizable M hPA
          context
          (rawFiniteRightDisjunctionCode M (next :: third :: more))
          hcontext).
      * exact htail.
Qed.

(** Fully generic derived eliminator.  The result root is existential because
    guarded context insertion rebuilds each supplied case proof and chooses a
    new carrier proof code. *)
Theorem raw_codedPALocalProofOf_finiteDisjunctionDerivedCases : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (branches : list M) conclusion context rowRoot,
  RawFiniteDisjunctionDerivedCaseResources M branches context ->
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M branches) rowRoot ->
  RawCodedPALocalFiniteDisjunctionCaseFamily M
    context branches conclusion ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA branches.
  induction branches as [| branch tail ih];
    intros conclusion context rowRoot hresources hrow hcases.
  - cbn [rawFiniteRightDisjunctionCode] in hrow.
    eexists.
    exact (raw_codedPALocalProofOf_botE M hPA
      context rowRoot hrow conclusion).
  - destruct tail as [| next rest].
    + destruct (hcases branch (or_introl eq_refl))
        as [caseRoot hcase].
      cbn [rawFiniteRightDisjunctionCode] in hrow.
      eexists.
      exact (raw_codedPALocalProofOf_impE M hPA
        context branch conclusion caseRoot rowRoot hcase hrow).
    + cbn [RawFiniteDisjunctionDerivedCaseResources
        RawFiniteDisjunctionConsTransplantAdequate] in hresources.
      destruct hresources as
        [hcontext [hbranchAdequate [hremainderAdequate htailResources]]].
      set (remainder :=
        rawFiniteRightDisjunctionCode M (next :: rest)).

      destruct (hcases branch (or_introl eq_refl))
        as [branchCaseRoot hbranchCase].
      destruct (raw_codedPALocalProof_adequateConsTransplant
        M hPA context branch
        (rawFormulaImpCode M branch conclusion) branchCaseRoot
        hbranchAdequate hcontext hbranchCase)
        as [leftImpRoot hleftImp].
      pose proof (raw_codedPALocalProofOf_assumption
        M hPA context branch hcontext) as hleftAssumption.
      pose proof (raw_codedPALocalProofOf_impE M hPA
        (rawListNode M branch context) branch conclusion
        leftImpRoot
        (rawProofAssumptionRoot M
          (rawListNode M branch context) branch)
        hleftImp hleftAssumption) as hleft.

      assert (hrightContext : RawContextListRealizable M
          (rawListNode M remainder context)).
      {
        exact (raw_contextList_cons_realizable M hPA
          context remainder hcontext).
      }
      pose proof (raw_codedPALocalProofOf_assumption
        M hPA context remainder hcontext) as hrightRow.
      assert (hrightCases :
          RawCodedPALocalFiniteDisjunctionCaseFamily M
            (rawListNode M remainder context)
            (next :: rest) conclusion).
      {
        intros selected hselected.
        destruct (hcases selected (or_intror hselected))
          as [selectedRoot hselectedProof].
        exact (raw_codedPALocalProof_adequateConsTransplant
          M hPA context remainder
          (rawFormulaImpCode M selected conclusion) selectedRoot
          hremainderAdequate hcontext hselectedProof).
      }
      assert (hrightResources :
          RawFiniteDisjunctionDerivedCaseResources M
            (next :: rest) (rawListNode M remainder context)).
      {
        unfold remainder.
        apply (raw_finiteDisjunctionDerivedCaseResources_tail
          M hPA branch (next :: rest) context).
        cbn [RawFiniteDisjunctionDerivedCaseResources
          RawFiniteDisjunctionConsTransplantAdequate].
        exact (conj hcontext
          (conj hbranchAdequate
            (conj hremainderAdequate htailResources))).
      }
      destruct (ih conclusion (rawListNode M remainder context)
        (rawProofAssumptionRoot M
          (rawListNode M remainder context) remainder)
        hrightResources hrightRow hrightCases)
        as [rightRoot hright].
      exists (rawProofOrERoot M context branch remainder conclusion
        rowRoot
        (rawProofImpERoot M (rawListNode M branch context)
          branch conclusion leftImpRoot
          (rawProofAssumptionRoot M
            (rawListNode M branch context) branch))
        rightRoot).
      exact (raw_codedPALocalProofOf_orE M hPA
        context branch remainder conclusion rowRoot
        (rawProofImpERoot M (rawListNode M branch context)
          branch conclusion leftImpRoot
          (rawProofAssumptionRoot M
            (rawListNode M branch context) branch))
        rightRoot hrow hleft hright).
Qed.

(** Degenerate endpoints make explicit that the generic resource parameter
    is genuinely vacuous for zero and one branch. *)
Corollary raw_codedPALocalProofOf_emptyDisjunctionDerivedCase : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion rowRoot,
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M []) rowRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context conclusion rowRoot hrow.
  apply (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA [] conclusion context rowRoot I hrow).
  intros branch hbranch. contradiction.
Qed.

Corollary raw_codedPALocalProofOf_singletonDisjunctionDerivedCase : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context branch conclusion rowRoot caseRoot,
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M [branch]) rowRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M branch conclusion) caseRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context branch conclusion rowRoot caseRoot hrow hcase.
  apply (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA [branch] conclusion context rowRoot I hrow).
  intros selected hselected.
  destruct hselected as [heq | himpossible].
  - subst selected. exists caseRoot. exact hcase.
  - contradiction.
Qed.

(** Literal native-row wrappers.  Their resource and case-family arguments
    remain generic so callers may choose proof roots independently for equal
    or duplicated branch codes. *)
Corollary raw_codedPALocalProofOf_rightDisjunctionSixDerivedCases : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion a b c d e f rowRoot,
  RawFiniteDisjunctionDerivedCaseResources M
    [a; b; c; d; e; f] context ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M a
      (rawFormulaOrCode M b
        (rawFormulaOrCode M c
          (rawFormulaOrCode M d
            (rawFormulaOrCode M e f))))) rowRoot ->
  RawCodedPALocalFiniteDisjunctionCaseFamily M
    context [a; b; c; d; e; f] conclusion ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context conclusion a b c d e f rowRoot
    hresources hrow hcases.
  apply (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA [a; b; c; d; e; f] conclusion context rowRoot
    hresources).
  - rewrite rawFiniteRightDisjunctionCode_six. exact hrow.
  - exact hcases.
Qed.

Corollary raw_codedPALocalProofOf_rightDisjunctionSevenDerivedCases : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion a b c d e f g rowRoot,
  RawFiniteDisjunctionDerivedCaseResources M
    [a; b; c; d; e; f; g] context ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M a
      (rawFormulaOrCode M b
        (rawFormulaOrCode M c
          (rawFormulaOrCode M d
            (rawFormulaOrCode M e
              (rawFormulaOrCode M f g)))))) rowRoot ->
  RawCodedPALocalFiniteDisjunctionCaseFamily M
    context [a; b; c; d; e; f; g] conclusion ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context conclusion a b c d e f g rowRoot
    hresources hrow hcases.
  apply (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA [a; b; c; d; e; f; g] conclusion context rowRoot
    hresources).
  - rewrite rawFiniteRightDisjunctionCode_seven. exact hrow.
  - exact hcases.
Qed.

End PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.
