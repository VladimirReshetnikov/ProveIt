(**
  Pairwise finite-disjunction case analysis in one arbitrary coded context.

  Suppose [Gamma] contains proofs of two finite rows

      A1 or ... or Ak        B1 or ... or Bl

  and, for every pair of branches, a proof of

      Ai -> Bj -> C.

  This module assembles an existential local proof of [C] over the *same*
  literal context code [Gamma].  It first derives each [Ai -> C], then feeds
  those proofs to the finite derived-case eliminator for the left row.
  Beneath the temporary [Ai] assumption, the right row and all pair proofs
  are moved by guarded single-cons transplant.  No formula is decoded and no
  unrestricted weakening principle is used.

  The resource predicates are shape-sensitive.  Empty dimensions use bottom
  elimination directly, and a one-by-one matrix uses two applications of
  modus ponens in the original context.  Every other nonempty matrix records
  exactly:

  - the realizability and left-row adequacy needed to introduce each [Ai];
  - the finite-derived-case resources for the left row; and
  - the finite-derived-case resources for the right row.

  Right resources are transported to [Ai :: Gamma] by constructing the
  honest cons traversal; their adequacy component is unchanged.
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
  RawCodedProofImpIConstructor
  RawCodedPALocalProofExistential
  RawCodedPALocalProofComposition
  RawCodedPALocalProofPropositionalRules
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPALocalProofFiniteDisjunction
  RawCodedPALocalProofFiniteDisjunctionDerivedCases.

Import ListNotations.

Module PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.

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
Import PABoundedRawCodedProofImpIConstructor.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofComposition.
Import PABoundedRawCodedPALocalProofPropositionalRules.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPALocalProofFiniteDisjunction.
Import PABoundedRawCodedPALocalProofFiniteDisjunctionDerivedCases.

(** A proof of every curried pair implication in the common context. *)
Definition RawCodedPALocalFiniteDisjunctionPairFamily
    (M : RawPAModel) (context : M)
    (leftBranches rightBranches : list M) (conclusion : M) : Prop :=
  forall left,
    In left leftBranches ->
    forall right,
      In right rightBranches ->
      exists root,
        RawCodedPALocalProofOf M context
          (rawFormulaImpCode M left
            (rawFormulaImpCode M right conclusion)) root.

Arguments RawCodedPALocalFiniteDisjunctionPairFamily
  M context leftBranches rightBranches conclusion : clear implicits.

(** Resources needed to turn every left branch into a temporary context
    head.  A singleton still needs its head adequate and [context] realizable
    unless the whole matrix is one-by-one, which is optimized separately. *)
Definition RawFiniteDisjunctionMatrixLeftResources
    (M : RawPAModel) (leftBranches : list M) (context : M) : Prop :=
  match leftBranches with
  | [] => True
  | branch :: [] =>
      RawContextListRealizable M context /\
      RawCodedFormulaAtomicallyAdequate M branch
  | _ :: _ :: _ =>
      RawFiniteDisjunctionDerivedCaseResources M leftBranches context
  end.

Arguments RawFiniteDisjunctionMatrixLeftResources
  M leftBranches context : clear implicits.

(** The exact public resource boundary. *)
Definition RawFiniteDisjunctionMatrixResources
    (M : RawPAModel) (leftBranches rightBranches : list M)
    (context : M) : Prop :=
  match leftBranches, rightBranches with
  | [], _ => True
  | _, [] => True
  | _ :: [], _ :: [] => True
  | _ :: _, _ :: _ =>
      RawFiniteDisjunctionMatrixLeftResources M leftBranches context /\
      RawFiniteDisjunctionDerivedCaseResources M rightBranches context
  end.

Arguments RawFiniteDisjunctionMatrixResources
  M leftBranches rightBranches context : clear implicits.

(** Every member of a nontrivial left row is adequate under the recursive
    cons-transplant predicate from the derived-case layer. *)
Lemma raw_finiteDisjunctionConsTransplantAdequate_nontrivial_member :
  forall (M : RawPAModel) first second rest selected,
  RawFiniteDisjunctionConsTransplantAdequate M
    (first :: second :: rest) ->
  In selected (first :: second :: rest) ->
  RawCodedFormulaAtomicallyAdequate M selected.
Proof.
  intros M first second rest.
  revert first second.
  induction rest as [| third more ih];
    intros first second selected hresources hselected.
  - cbn [RawFiniteDisjunctionConsTransplantAdequate
      rawFiniteRightDisjunctionCode] in hresources.
    destruct hresources as [hfirst [hsecond _]].
    destruct hselected as [heq | [heq | himpossible]].
    + now subst selected.
    + now subst selected.
    + contradiction.
  - cbn [RawFiniteDisjunctionConsTransplantAdequate] in hresources.
    destruct hresources as [hfirst [_ htail]].
    destruct hselected as [heq | hselected].
    + now subst selected.
    + exact (ih second third selected htail hselected).
Qed.

Lemma raw_finiteDisjunctionMatrixLeftResources_context_realizable : forall
    (M : RawPAModel) branch tail context,
  RawFiniteDisjunctionMatrixLeftResources M
    (branch :: tail) context ->
  RawContextListRealizable M context.
Proof.
  intros M branch tail context hresources.
  destruct tail as [| second rest].
  - exact (proj1 hresources).
  - exact (proj1 hresources).
Qed.

Lemma raw_finiteDisjunctionMatrixLeftResources_member_adequate : forall
    (M : RawPAModel) branch tail context selected,
  RawFiniteDisjunctionMatrixLeftResources M
    (branch :: tail) context ->
  In selected (branch :: tail) ->
  RawCodedFormulaAtomicallyAdequate M selected.
Proof.
  intros M branch tail context selected hresources hselected.
  destruct tail as [| second rest].
  - destruct hselected as [heq | himpossible].
    + subst selected. exact (proj2 hresources).
    + contradiction.
  - apply (raw_finiteDisjunctionConsTransplantAdequate_nontrivial_member
      M branch second rest selected (proj2 hresources) hselected).
Qed.

Lemma raw_finiteDisjunctionMatrixLeftResources_derived : forall
    (M : RawPAModel) branch tail context,
  RawFiniteDisjunctionMatrixLeftResources M
    (branch :: tail) context ->
  RawFiniteDisjunctionDerivedCaseResources M
    (branch :: tail) context.
Proof.
  intros M branch tail context hresources.
  destruct tail as [| second rest].
  - exact I.
  - exact hresources.
Qed.

(** Changing only the context of a finite derived-case resource requires one
    honest cons traversal in the nontrivial case.  Empty and singleton rows
    carry no context field. *)
Lemma raw_finiteDisjunctionDerivedCaseResources_cons_context : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      branches context head,
  RawContextListRealizable M context ->
  RawFiniteDisjunctionDerivedCaseResources M branches context ->
  RawFiniteDisjunctionDerivedCaseResources M branches
    (rawListNode M head context).
Proof.
  intros M hPA branches context head hcontext hresources.
  destruct branches as [| first tail].
  - exact I.
  - destruct tail as [| second rest].
    + exact I.
    + cbn [RawFiniteDisjunctionDerivedCaseResources] in *.
      destruct hresources as [_ hadequacy].
      split.
      * exact (raw_contextList_cons_realizable M hPA
          context head hcontext).
      * exact hadequacy.
Qed.

(** ------------------------------------------------------------------
    Nondegenerate nested assembler. *)

Theorem raw_codedPALocalProofOf_finiteDisjunctionMatrix_nonempty : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftHead leftTail rightHead rightTail conclusion context
      leftRowRoot rightRowRoot,
  RawFiniteDisjunctionMatrixLeftResources M
    (leftHead :: leftTail) context ->
  RawFiniteDisjunctionDerivedCaseResources M
    (rightHead :: rightTail) context ->
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M (leftHead :: leftTail))
    leftRowRoot ->
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M (rightHead :: rightTail))
    rightRowRoot ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    (leftHead :: leftTail) (rightHead :: rightTail) conclusion ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA leftHead leftTail rightHead rightTail conclusion context
    leftRowRoot rightRowRoot hleftResources hrightResources
    hleftRow hrightRow hpairs.
  assert (hcontext : RawContextListRealizable M context).
  {
    exact (raw_finiteDisjunctionMatrixLeftResources_context_realizable
      M leftHead leftTail context hleftResources).
  }
  apply (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA (leftHead :: leftTail) conclusion context leftRowRoot
    (raw_finiteDisjunctionMatrixLeftResources_derived
      M leftHead leftTail context hleftResources)
    hleftRow).
  intros selected hselected.
  assert (hselectedAdequate :
      RawCodedFormulaAtomicallyAdequate M selected).
  {
    exact (raw_finiteDisjunctionMatrixLeftResources_member_adequate
      M leftHead leftTail context selected hleftResources hselected).
  }
  destruct (raw_codedPALocalProof_adequateConsTransplant
    M hPA context selected
    (rawFiniteRightDisjunctionCode M (rightHead :: rightTail))
    rightRowRoot hselectedAdequate hcontext hrightRow)
    as [liftedRightRowRoot hliftedRightRow].
  assert (hliftedRightResources :
      RawFiniteDisjunctionDerivedCaseResources M
        (rightHead :: rightTail) (rawListNode M selected context)).
  {
    exact (raw_finiteDisjunctionDerivedCaseResources_cons_context
      M hPA (rightHead :: rightTail) context selected
      hcontext hrightResources).
  }
  assert (hliftedRightCases :
      RawCodedPALocalFiniteDisjunctionCaseFamily M
        (rawListNode M selected context)
        (rightHead :: rightTail) conclusion).
  {
    intros right hright.
    destruct (hpairs selected hselected right hright)
      as [pairRoot hpair].
    destruct (raw_codedPALocalProof_adequateConsTransplant
      M hPA context selected
      (rawFormulaImpCode M selected
        (rawFormulaImpCode M right conclusion))
      pairRoot hselectedAdequate hcontext hpair)
      as [liftedPairRoot hliftedPair].
    pose proof (raw_codedPALocalProofOf_assumption
      M hPA context selected hcontext) as hselectedAssumption.
    exists (rawProofImpERoot M (rawListNode M selected context)
      selected (rawFormulaImpCode M right conclusion)
      liftedPairRoot
      (rawProofAssumptionRoot M
        (rawListNode M selected context) selected)).
    exact (raw_codedPALocalProofOf_impE M hPA
      (rawListNode M selected context)
      selected (rawFormulaImpCode M right conclusion)
      liftedPairRoot
      (rawProofAssumptionRoot M
        (rawListNode M selected context) selected)
      hliftedPair hselectedAssumption).
  }
  destruct (raw_codedPALocalProofOf_finiteDisjunctionDerivedCases
    M hPA (rightHead :: rightTail) conclusion
    (rawListNode M selected context) liftedRightRowRoot
    hliftedRightResources hliftedRightRow hliftedRightCases)
    as [childRoot hchild].
  exists (rawProofImpIRoot M context selected conclusion childRoot).
  exact (raw_codedPALocalProofOf_impI M hPA
    context selected conclusion childRoot hchild).
Qed.

(** ------------------------------------------------------------------
    Shape-sensitive public matrix endpoint. *)

Theorem raw_codedPALocalProofOf_finiteDisjunctionMatrix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (leftBranches rightBranches : list M) conclusion context
      leftRowRoot rightRowRoot,
  RawFiniteDisjunctionMatrixResources M
    leftBranches rightBranches context ->
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M leftBranches) leftRowRoot ->
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M rightBranches) rightRowRoot ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    leftBranches rightBranches conclusion ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA leftBranches rightBranches conclusion context
    leftRowRoot rightRowRoot hresources hleftRow hrightRow hpairs.
  destruct leftBranches as [| leftHead leftTail].
  - cbn [rawFiniteRightDisjunctionCode] in hleftRow.
    eexists.
    exact (raw_codedPALocalProofOf_botE M hPA
      context leftRowRoot hleftRow conclusion).
  - destruct rightBranches as [| rightHead rightTail].
    + cbn [rawFiniteRightDisjunctionCode] in hrightRow.
      eexists.
      exact (raw_codedPALocalProofOf_botE M hPA
        context rightRowRoot hrightRow conclusion).
    + destruct leftTail as [| leftSecond leftRest].
      * destruct rightTail as [| rightSecond rightRest].
        -- destruct (hpairs leftHead (or_introl eq_refl)
             rightHead (or_introl eq_refl)) as [pairRoot hpair].
           cbn [rawFiniteRightDisjunctionCode] in hleftRow, hrightRow.
           pose proof (raw_codedPALocalProofOf_impE M hPA
             context leftHead (rawFormulaImpCode M rightHead conclusion)
             pairRoot leftRowRoot hpair hleftRow) as hrightImplication.
           exists (rawProofImpERoot M context rightHead conclusion
             (rawProofImpERoot M context leftHead
               (rawFormulaImpCode M rightHead conclusion)
               pairRoot leftRowRoot)
             rightRowRoot).
           exact (raw_codedPALocalProofOf_impE M hPA
             context rightHead conclusion
             (rawProofImpERoot M context leftHead
               (rawFormulaImpCode M rightHead conclusion)
               pairRoot leftRowRoot)
             rightRowRoot hrightImplication hrightRow).
        -- destruct hresources as [hleftResources hrightResources].
           exact (raw_codedPALocalProofOf_finiteDisjunctionMatrix_nonempty
             M hPA leftHead [] rightHead (rightSecond :: rightRest)
             conclusion context leftRowRoot rightRowRoot
             hleftResources hrightResources hleftRow hrightRow hpairs).
      * destruct rightTail as [| rightSecond rightRest].
        -- destruct hresources as [hleftResources hrightResources].
           exact (raw_codedPALocalProofOf_finiteDisjunctionMatrix_nonempty
             M hPA leftHead (leftSecond :: leftRest) rightHead []
             conclusion context leftRowRoot rightRowRoot
             hleftResources hrightResources hleftRow hrightRow hpairs).
        -- destruct hresources as [hleftResources hrightResources].
           exact (raw_codedPALocalProofOf_finiteDisjunctionMatrix_nonempty
             M hPA leftHead (leftSecond :: leftRest)
             rightHead (rightSecond :: rightRest)
             conclusion context leftRowRoot rightRowRoot
             hleftResources hrightResources hleftRow hrightRow hpairs).
Qed.

(** Explicit zero/singleton endpoints expose the resource-free behavior. *)
Corollary raw_codedPALocalProofOf_finiteDisjunctionMatrix_left_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion leftRowRoot,
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M []) leftRowRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context conclusion leftRowRoot hleft.
  cbn [rawFiniteRightDisjunctionCode] in hleft.
  eexists. exact (raw_codedPALocalProofOf_botE
    M hPA context leftRowRoot hleft conclusion).
Qed.

Corollary raw_codedPALocalProofOf_finiteDisjunctionMatrix_right_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion rightRowRoot,
  RawCodedPALocalProofOf M context
    (rawFiniteRightDisjunctionCode M []) rightRowRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context conclusion rightRowRoot hright.
  cbn [rawFiniteRightDisjunctionCode] in hright.
  eexists. exact (raw_codedPALocalProofOf_botE
    M hPA context rightRowRoot hright conclusion).
Qed.

Corollary raw_codedPALocalProofOf_finiteDisjunctionMatrix_singletons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left right conclusion leftRowRoot rightRowRoot pairRoot,
  RawCodedPALocalProofOf M context left leftRowRoot ->
  RawCodedPALocalProofOf M context right rightRowRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaImpCode M left
      (rawFormulaImpCode M right conclusion)) pairRoot ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context left right conclusion
    leftRowRoot rightRowRoot pairRoot hleft hright hpair.
  pose proof (raw_codedPALocalProofOf_impE M hPA
    context left (rawFormulaImpCode M right conclusion)
    pairRoot leftRowRoot hpair hleft) as hrightImplication.
  eexists.
  exact (raw_codedPALocalProofOf_impE M hPA
    context right conclusion _ rightRowRoot hrightImplication hright).
Qed.

(** Native Sigma-by-Pi branch matrix: seven truth alternatives against six
    falsity alternatives. *)
Corollary raw_codedPALocalProofOf_rightDisjunctionSevenBySixMatrix : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context conclusion
      a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6
      leftRowRoot rightRowRoot,
  RawFiniteDisjunctionMatrixResources M
    [a1; a2; a3; a4; a5; a6; a7]
    [b1; b2; b3; b4; b5; b6] context ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M a1
      (rawFormulaOrCode M a2
        (rawFormulaOrCode M a3
          (rawFormulaOrCode M a4
            (rawFormulaOrCode M a5
              (rawFormulaOrCode M a6 a7)))))) leftRowRoot ->
  RawCodedPALocalProofOf M context
    (rawFormulaOrCode M b1
      (rawFormulaOrCode M b2
        (rawFormulaOrCode M b3
          (rawFormulaOrCode M b4
            (rawFormulaOrCode M b5 b6))))) rightRowRoot ->
  RawCodedPALocalFiniteDisjunctionPairFamily M context
    [a1; a2; a3; a4; a5; a6; a7]
    [b1; b2; b3; b4; b5; b6] conclusion ->
  exists resultRoot,
    RawCodedPALocalProofOf M context conclusion resultRoot.
Proof.
  intros M hPA context conclusion
    a1 a2 a3 a4 a5 a6 a7 b1 b2 b3 b4 b5 b6
    leftRowRoot rightRowRoot hresources hleft hright hpairs.
  apply (raw_codedPALocalProofOf_finiteDisjunctionMatrix
    M hPA
    [a1; a2; a3; a4; a5; a6; a7]
    [b1; b2; b3; b4; b5; b6]
    conclusion context leftRowRoot rightRowRoot hresources).
  - rewrite rawFiniteRightDisjunctionCode_seven. exact hleft.
  - rewrite rawFiniteRightDisjunctionCode_six. exact hright.
  - exact hpairs.
Qed.

End PABoundedRawCodedPALocalProofFiniteDisjunctionMatrix.
