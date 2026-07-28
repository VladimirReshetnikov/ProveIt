(**
  Honest prefix extension of independently witnessed PA contexts.

  A [RawCodedPAProofOf] certificate existentially chooses its own witnessed
  PA-axiom context.  Consequently two certificates cannot be put under a
  binary proof constructor merely by naming one of their contexts: every
  proof node stores its context literally.

  This file establishes the direction of context merge which is available
  from the existing one-head proof transformer.  Given witnessed contexts

      left = l_0 :: ... :: l_(n-1) :: nil
      right,

  PA-definable reverse traversal of [left] constructs, in lockstep, witnessed
  lists and axiom contexts of the shape [left ++ right].  At every reverse
  step [raw_codedPAAxiomWitnessContext_cons] preserves the witness/axiom row
  correspondence and the guarded one-head transplant rebuilds every proof
  coming from [right].  The construction works at a possibly nonstandard
  carrier-valued length; no context is decoded into a Rocq list.

  The opposite proof direction is isolated at the end of the file.  The
  constructed extension contains every member of [left], but turning that
  inclusion into a rebuilt proof over the extension is the genuine general
  weakening problem (in particular under binder-induced context shifts).
  [RawCodedPALocalProofWitnessedContextInclusionWeakening] states exactly that
  remaining syntactic operation, restricted to honest witnessed PA contexts.
  Assuming only this named operation, five fixed merge steps synchronize six
  ordinary proof certificates and discharge the master common-context lift.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  PolynomialPairInjectivity
  RawCodedAdditionLaws
  RawCodedSyntaxConstructors
  RawCodedAssignment
  RawCodedFixedLevelTruthTotality
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedContextFunctionality
  RawCodedRestrictedPAProof
  RawCodedPAAxiomWitness
  RawCodedPAProvability
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedPAAxiomWitnessContextCons
  RawCodedPALocalProofEmptyContextTransport
  RawCodedTruthCertificateMasterBaseBridge
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.

Module PABoundedRawCodedPALocalProofWitnessedContextMerge.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedPolynomialPairInjectivity.
Import PABoundedRawCodedAdditionLaws.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedContextFunctionality.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedPAAxiomWitnessContextCons.
Import PABoundedRawCodedPALocalProofEmptyContextTransport.
Import PABoundedRawCodedTruthCertificateMasterBaseBridge.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.

(** ------------------------------------------------------------------
    Two first-order-definable relations used by the reverse invariant. *)

(** Literal membership inclusion between two honest coded contexts.  This is
    intentionally only a relation on represented list membership; no semantic
    validity or decoding principle is hidden in it. *)
Definition RawContextListIncluded (M : RawPAModel)
    (source target : M) : Prop :=
  forall member : M,
    RawContextListMember M source member ->
    RawContextListMember M target member.

Arguments RawContextListIncluded M source target : clear implicits.

Definition contextListIncludedTermAt
    (source target : term) : formula :=
  pAll
    (pImp
      (contextListMemberTermAt (liftTerm 1 source) (tVar 0))
      (contextListMemberTermAt (liftTerm 1 target) (tVar 0))).

Lemma raw_sat_contextListIncludedTermAt_iff : forall
    (M : RawPAModel) e source target,
  raw_formula_sat M e (contextListIncludedTermAt source target) <->
  RawContextListIncluded M
    (raw_term_eval M e source) (raw_term_eval M e target).
Proof.
  intros M e source target.
  unfold contextListIncludedTermAt, RawContextListIncluded.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_contextListMemberTermAt_iff.
  repeat setoid_rewrite raw_restrictedPA_eval_liftTerm_one.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Uniform syntactic transport from one literal context to another.  The
    existential root is part of the relation, so using it always produces an
    actual rebuilt proof tree. *)
Definition RawCodedPALocalProofContextTransport (M : RawPAModel)
    (source target : M) : Prop :=
  forall conclusion root : M,
    RawCodedPALocalProofOf M source conclusion root ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M target conclusion transportedRoot.

Arguments RawCodedPALocalProofContextTransport M source target
  : clear implicits.

Definition codedPALocalProofContextTransportTermAt
    (source target : term) : formula :=
  pAll (pAll
    (pImp
      (codedPALocalProofForInsertTermAt
        (liftTerm 2 source) (tVar 1) (tVar 0))
      (pEx
        (codedPALocalProofForInsertTermAt
          (liftTerm 3 target) (tVar 2) (tVar 0))))).

Lemma raw_sat_codedPALocalProofContextTransportTermAt_iff : forall
    (M : RawPAModel) e source target,
  raw_formula_sat M e
    (codedPALocalProofContextTransportTermAt source target) <->
  RawCodedPALocalProofContextTransport M
    (raw_term_eval M e source) (raw_term_eval M e target).
Proof.
  intros M e source target.
  unfold codedPALocalProofContextTransportTermAt,
    RawCodedPALocalProofContextTransport.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPALocalProofForInsertTermAt_iff.
  repeat setoid_rewrite raw_emptyContextTransport_eval_liftTerm_two.
  repeat setoid_rewrite raw_emptyContextTransport_eval_liftTerm_three.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

(** Both halves of a witnessed package are honest list domains. *)
Lemma raw_codedPAAxiomWitnessContext_witnessList_realizable : forall
    (M : RawPAModel) witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextListRealizable M witnessList.
Proof.
  intros M witnessList context
    (bound & witnessTailCode & witnessTailStep & witnessHeadCode &
      witnessHeadStep & axiomTailCode & axiomTailStep & axiomHeadCode &
      axiomHeadStep & hwitnessed).
  unfold RawCodedPAAxiomWitnessContextWithTables in hwitnessed.
  destruct hwitnessed as [hwitnessTraversal _].
  exists bound, witnessTailCode, witnessTailStep,
    witnessHeadCode, witnessHeadStep.
  exact hwitnessTraversal.
Qed.

Lemma raw_codedPAAxiomWitnessContext_context_realizable : forall
    (M : RawPAModel) witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextListRealizable M context.
Proof.
  intros M witnessList context
    (bound & witnessTailCode & witnessTailStep & witnessHeadCode &
      witnessHeadStep & axiomTailCode & axiomTailStep & axiomHeadCode &
      axiomHeadStep & hwitnessed).
  unfold RawCodedPAAxiomWitnessContextWithTables in hwitnessed.
  destruct hwitnessed as [_ [hcontextTraversal _]].
  exists bound, axiomTailCode, axiomTailStep,
    axiomHeadCode, axiomHeadStep.
  exact hcontextTraversal.
Qed.

(** Elementary inclusion facts used in the represented successor step. *)
Lemma raw_contextListIncluded_refl : forall
    (M : RawPAModel) context,
  RawContextListIncluded M context context.
Proof.
  intros M context member hmember. exact hmember.
Qed.

Lemma raw_contextListIncluded_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall context,
  RawContextListIncluded M (raw_zero M) context.
Proof.
  intros M hPA context member hmember.
  exfalso. exact (raw_contextListMember_zero_false M hPA member hmember).
Qed.

Lemma raw_contextListIncluded_cons : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      source target sourceHead targetHead,
  RawContextListRealizable M source ->
  RawContextListRealizable M target ->
  sourceHead = targetHead ->
  RawContextListIncluded M source target ->
  RawContextListIncluded M
    (rawListNode M sourceHead source)
    (rawListNode M targetHead target).
Proof.
  intros M hPA source target sourceHead targetHead
    hsource htarget hheads hincluded member hmember.
  apply (proj2 (raw_contextListMember_cons_iff M hPA
    target targetHead member htarget)).
  destruct (proj1 (raw_contextListMember_cons_iff M hPA
    source sourceHead member hsource) hmember) as [-> | htail].
  - left. exact hheads.
  - right. exact (hincluded member htail).
Qed.

Lemma raw_contextListIncluded_cons_target : forall
    (M : RawPAModel), RawPASatisfies M -> forall source target head,
  RawContextListIncluded M source target ->
  RawContextListIncluded M source (rawListNode M head target).
Proof.
  intros M hPA source target head hincluded member hmember.
  exact (raw_contextList_cons_tail_member M hPA target head member
    (hincluded member hmember)).
Qed.

(** ------------------------------------------------------------------
    Reverse prefix construction. *)

(** At a complementary pair [index + current = bound], [witnessSuffix] and
    [axiomSuffix] name synchronized suffixes of the left witnessed package.
    The state constructs those suffixes in front of the fixed right package.
    Besides honest witness synchronization it retains membership from both
    inputs and a uniform proof transformer from the right context. *)
Definition RawCodedPAWitnessedPrefixMergeState
    (M : RawPAModel)
    (bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext current : M) : Prop :=
  forall index witnessSuffix axiomSuffix : M,
    raw_add M index current = bound ->
    RawCodedAssignmentLookup M
      witnessTailCode witnessTailStep index witnessSuffix ->
    RawCodedAssignmentLookup M
      axiomTailCode axiomTailStep index axiomSuffix ->
    RawContextListRealizable M witnessSuffix /\
    RawContextListRealizable M axiomSuffix /\
    exists mergedWitnessList mergedContext : M,
      RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
      RawContextListIncluded M witnessSuffix mergedWitnessList /\
      RawContextListIncluded M axiomSuffix mergedContext /\
      RawContextListIncluded M rightWitnessList mergedWitnessList /\
      RawContextListIncluded M rightContext mergedContext /\
      RawCodedPALocalProofContextTransport M rightContext mergedContext.

Arguments RawCodedPAWitnessedPrefixMergeState
  M bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext current : clear implicits.

Definition witnessedPrefixMergeAll3 (body : formula) : formula :=
  pAll (pAll (pAll body)).

Definition witnessedPrefixMergeImp3
    (first second third body : formula) : formula :=
  pImp first (pImp second (pImp third body)).

Definition witnessedPrefixMergeEx2 (body : formula) : formula :=
  pEx (pEx body).

Definition witnessedPrefixMergeAnd6
    (a b c d f g : formula) : formula :=
  pAnd a (pAnd b (pAnd c (pAnd d (pAnd f g)))).

Definition codedPAWitnessedPrefixMergeStateTermAt
    (bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext current : term) : formula :=
  witnessedPrefixMergeAll3
    (witnessedPrefixMergeImp3
      (pEq (tAdd (tVar 2) (liftTerm 3 current)) (liftTerm 3 bound))
      (codedAssignmentLookupTermAt
        (liftTerm 3 witnessTailCode) (liftTerm 3 witnessTailStep)
        (tVar 2) (tVar 1))
      (codedAssignmentLookupTermAt
        (liftTerm 3 axiomTailCode) (liftTerm 3 axiomTailStep)
        (tVar 2) (tVar 0))
      (pAnd
        (contextListRealizableTermAt (tVar 1))
        (pAnd
          (contextListRealizableTermAt (tVar 0))
          (witnessedPrefixMergeEx2
            (witnessedPrefixMergeAnd6
              (codedPAAxiomWitnessContextTermAt (tVar 1) (tVar 0))
              (contextListIncludedTermAt (tVar 3) (tVar 1))
              (contextListIncludedTermAt (tVar 2) (tVar 0))
              (contextListIncludedTermAt
                (liftTerm 5 rightWitnessList) (tVar 1))
              (contextListIncludedTermAt
                (liftTerm 5 rightContext) (tVar 0))
              (codedPALocalProofContextTransportTermAt
                (liftTerm 5 rightContext) (tVar 0))))))).

Lemma raw_sat_codedPAWitnessedPrefixMergeStateTermAt_iff : forall
    (M : RawPAModel) e
      bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext current,
  raw_formula_sat M e
    (codedPAWitnessedPrefixMergeStateTermAt
      bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext current) <->
  RawCodedPAWitnessedPrefixMergeState M
    (raw_term_eval M e bound)
    (raw_term_eval M e witnessTailCode)
    (raw_term_eval M e witnessTailStep)
    (raw_term_eval M e witnessHeadCode)
    (raw_term_eval M e witnessHeadStep)
    (raw_term_eval M e axiomTailCode)
    (raw_term_eval M e axiomTailStep)
    (raw_term_eval M e axiomHeadCode)
    (raw_term_eval M e axiomHeadStep)
    (raw_term_eval M e rightWitnessList)
    (raw_term_eval M e rightContext)
    (raw_term_eval M e current).
Proof.
  intros M e bound witnessTailCode witnessTailStep witnessHeadCode
    witnessHeadStep axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext current.
  unfold codedPAWitnessedPrefixMergeStateTermAt,
    witnessedPrefixMergeAll3, witnessedPrefixMergeImp3,
    witnessedPrefixMergeEx2, witnessedPrefixMergeAnd6,
    RawCodedPAWitnessedPrefixMergeState.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_contextListRealizableTermAt_iff.
  setoid_rewrite raw_sat_codedPAAxiomWitnessContextTermAt_iff.
  setoid_rewrite raw_sat_contextListIncludedTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofContextTransportTermAt_iff.
  repeat setoid_rewrite raw_emptyContextTransport_eval_liftTerm_three.
  repeat setoid_rewrite raw_contextList_eval_liftTerm_five.
  cbn [raw_term_eval scons]. split.
  - intros h index witnessSuffix axiomSuffix hsum
      hwitnessSuffix haxiomSuffix.
    assert (hsum' : raw_add M index
        (raw_term_eval M
          (scons M axiomSuffix
            (scons M witnessSuffix (scons M index e)))
          (liftTerm 3 current)) = raw_term_eval M e bound).
    { rewrite raw_emptyContextTransport_eval_liftTerm_three. exact hsum. }
    pose proof (h index witnessSuffix axiomSuffix hsum'
      hwitnessSuffix haxiomSuffix) as hresult.
    repeat rewrite raw_contextList_eval_liftTerm_five in hresult.
    exact hresult.
  - intros h index witnessSuffix axiomSuffix hsum
      hwitnessSuffix haxiomSuffix.
    rewrite raw_emptyContextTransport_eval_liftTerm_three in hsum.
    pose proof (h index witnessSuffix axiomSuffix hsum
      hwitnessSuffix haxiomSuffix) as hresult.
    repeat rewrite raw_contextList_eval_liftTerm_five.
    exact hresult.
Qed.

(** At stage zero the complementary index is [bound].  Both certified tail
    tables therefore identify the requested suffixes with their terminal
    zero rows, and the fixed right package is the required accumulator. *)
Lemma raw_codedPAWitnessedPrefixMergeState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftWitnessList leftContext bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext,
  RawContextListTraversal M leftWitnessList bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep ->
  RawContextListTraversal M leftContext bound
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  RawCodedPAWitnessedPrefixMergeState M
    bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext (raw_zero M).
Proof.
  intros M hPA leftWitnessList leftContext bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext
    hwitnessTraversal haxiomTraversal hright
    index witnessSuffix axiomSuffix hsum
    hwitnessSuffix haxiomSuffix.
  rewrite raw_add_zero_right in hsum by exact hPA. subst index.
  destruct hwitnessTraversal as
    [hwitnessRoot [hwitnessEnd [hwitnessDefined hwitnessRows]]].
  destruct haxiomTraversal as
    [haxiomRoot [haxiomEnd [haxiomDefined haxiomRows]]].
  assert (hwitnessSuffixEq : witnessSuffix = raw_zero M).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      witnessTailCode witnessTailStep bound
      witnessSuffix (raw_zero M) hwitnessSuffix hwitnessEnd).
  }
  assert (haxiomSuffixEq : axiomSuffix = raw_zero M).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      axiomTailCode axiomTailStep bound
      axiomSuffix (raw_zero M) haxiomSuffix haxiomEnd).
  }
  subst witnessSuffix. subst axiomSuffix.
  split; [exact (raw_contextList_empty_realizable M hPA) |].
  split; [exact (raw_contextList_empty_realizable M hPA) |].
  exists rightWitnessList, rightContext.
  repeat split.
  - exact hright.
  - exact (raw_contextListIncluded_zero M hPA rightWitnessList).
  - exact (raw_contextListIncluded_zero M hPA rightContext).
  - exact (raw_contextListIncluded_refl M rightWitnessList).
  - exact (raw_contextListIncluded_refl M rightContext).
  - intros conclusion root hproof. exists root. exact hproof.
Qed.

(** One reverse step reads the synchronized witness/axiom row, extends the
    accumulator by those literal heads, and composes its uniform right-proof
    transformer with one guarded proof-tree insertion. *)
Lemma raw_codedPAWitnessedPrefixMergeState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftWitnessList leftContext bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext current,
  RawContextListTraversal M leftWitnessList bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep ->
  RawContextListTraversal M leftContext bound
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep ->
  RawCodedPAAxiomWitnessContextRows M bound
    witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  RawCodedPAWitnessedPrefixMergeState M
    bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext current ->
  RawCodedPAWitnessedPrefixMergeState M
    bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext (raw_succ M current).
Proof.
  intros M hPA leftWitnessList leftContext bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext current
    hwitnessTraversal haxiomTraversal hrows hright hcurrent
    index witnessSuffix axiomSuffix hsum
    hwitnessSuffix haxiomSuffix.
  assert (hindex : rawLt M index bound).
  { exists current. exact hsum. }
  pose proof hwitnessTraversal as hwitnessTraversalFacts.
  pose proof haxiomTraversal as haxiomTraversalFacts.
  destruct hwitnessTraversalFacts as
    [hwitnessRoot [hwitnessEnd [hwitnessDefined hwitnessTraversalRows]]].
  destruct haxiomTraversalFacts as
    [haxiomRoot [haxiomEnd [haxiomDefined haxiomTraversalRows]]].
  destruct (hwitnessTraversalRows index hindex) as
    (rowWitnessSuffix & nextWitnessSuffix & witnessHead &
      hrowWitnessSuffix & hnextWitnessSuffix & hwitnessHead &
      hwitnessNode).
  destruct (haxiomTraversalRows index hindex) as
    (rowAxiomSuffix & nextAxiomSuffix & axiomHead &
      hrowAxiomSuffix & hnextAxiomSuffix & haxiomHead & haxiomNode).
  assert (hwitnessSuffixEq : witnessSuffix = rowWitnessSuffix).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      witnessTailCode witnessTailStep index
      witnessSuffix rowWitnessSuffix hwitnessSuffix hrowWitnessSuffix).
  }
  assert (haxiomSuffixEq : axiomSuffix = rowAxiomSuffix).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      axiomTailCode axiomTailStep index
      axiomSuffix rowAxiomSuffix haxiomSuffix hrowAxiomSuffix).
  }
  subst witnessSuffix. subst axiomSuffix.
  assert (hnextSum :
      raw_add M (raw_succ M index) current = bound).
  {
    rewrite raw_succ_add_pair by exact hPA.
    rewrite <- raw_add_succ by exact hPA. exact hsum.
  }
  destruct (hcurrent (raw_succ M index)
    nextWitnessSuffix nextAxiomSuffix hnextSum
    hnextWitnessSuffix hnextAxiomSuffix) as
    [hnextWitnessRealizable [hnextAxiomRealizable
      (mergedWitnessList & mergedContext & hmerged &
        hleftWitnessIncluded & hleftAxiomIncluded &
        hrightWitnessIncluded & hrightContextIncluded & htransport)]].
  assert (hmergedWitnessRealizable :
      RawContextListRealizable M mergedWitnessList).
  {
    exact (raw_codedPAAxiomWitnessContext_witnessList_realizable
      M mergedWitnessList mergedContext hmerged).
  }
  assert (hmergedContextRealizable :
      RawContextListRealizable M mergedContext).
  {
    exact (raw_codedPAAxiomWitnessContext_context_realizable
      M mergedWitnessList mergedContext hmerged).
  }
  assert (hwitnessRow :
      RawCodedPAAxiomWitness M witnessHead axiomHead).
  { exact (hrows index witnessHead axiomHead
      hindex hwitnessHead haxiomHead). }
  split.
  - rewrite hwitnessNode.
    exact (raw_contextList_cons_realizable M hPA
      nextWitnessSuffix witnessHead hnextWitnessRealizable).
  - split.
    + rewrite haxiomNode.
      exact (raw_contextList_cons_realizable M hPA
        nextAxiomSuffix axiomHead hnextAxiomRealizable).
    + exists (rawListNode M witnessHead mergedWitnessList),
        (rawListNode M axiomHead mergedContext).
      repeat split.
      * exact (raw_codedPAAxiomWitnessContext_cons M hPA
          mergedWitnessList mergedContext witnessHead axiomHead
          hmerged hwitnessRow).
      * rewrite hwitnessNode.
        exact (raw_contextListIncluded_cons M hPA
          nextWitnessSuffix mergedWitnessList witnessHead witnessHead
          hnextWitnessRealizable hmergedWitnessRealizable eq_refl
          hleftWitnessIncluded).
      * rewrite haxiomNode.
        exact (raw_contextListIncluded_cons M hPA
          nextAxiomSuffix mergedContext axiomHead axiomHead
          hnextAxiomRealizable hmergedContextRealizable eq_refl
          hleftAxiomIncluded).
      * exact (raw_contextListIncluded_cons_target M hPA
          rightWitnessList mergedWitnessList witnessHead
          hrightWitnessIncluded).
      * exact (raw_contextListIncluded_cons_target M hPA
          rightContext mergedContext axiomHead hrightContextIncluded).
      * intros conclusion root hproof.
        destruct (htransport conclusion root hproof)
          as [transportedRoot htransported].
        exact (raw_codedPALocalProof_adequateConsTransplant M hPA
          mergedContext axiomHead conclusion transportedRoot
          (raw_codedPAAxiomWitness_axiom_atomically_adequate
            M hPA witnessHead axiomHead hwitnessRow)
          hmergedContextRealizable htransported).
Qed.

(** PA's definable induction reaches every carrier-valued reverse stage. *)
Theorem raw_codedPAWitnessedPrefixMergeState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftWitnessList leftContext bound
      witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext,
  RawContextListTraversal M leftWitnessList bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep ->
  RawContextListTraversal M leftContext bound
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep ->
  RawCodedPAAxiomWitnessContextRows M bound
    witnessHeadCode witnessHeadStep axiomHeadCode axiomHeadStep ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  forall current,
    RawCodedPAWitnessedPrefixMergeState M
      bound witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
      axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
      rightWitnessList rightContext current.
Proof.
  intros M hPA leftWitnessList leftContext bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext
    hwitnessTraversal haxiomTraversal hrows hright.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => bound
    | 1 => witnessTailCode
    | 2 => witnessTailStep
    | 3 => witnessHeadCode
    | 4 => witnessHeadStep
    | 5 => axiomTailCode
    | 6 => axiomTailStep
    | 7 => axiomHeadCode
    | 8 => axiomHeadStep
    | 9 => rightWitnessList
    | _ => rightContext
    end).
  set (phi := codedPAWitnessedPrefixMergeStateTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
    (tVar 6) (tVar 7) (tVar 8) (tVar 9)
    (tVar 10) (tVar 11) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi. apply (proj2
        (raw_sat_codedPAWitnessedPrefixMergeStateTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9)
          (tVar 10) (tVar 11) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_codedPAWitnessedPrefixMergeState_zero M hPA
        leftWitnessList leftContext bound
        witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
        axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
        rightWitnessList rightContext
        hwitnessTraversal haxiomTraversal hright).
    - intros current hcurrentSat. unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedPAWitnessedPrefixMergeStateTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9)
          (tVar 10) (tVar 11) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedPAWitnessedPrefixMergeStateTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
          (tVar 6) (tVar 7) (tVar 8) (tVar 9)
          (tVar 10) (tVar 11) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedPAWitnessedPrefixMergeState_succ M hPA
        leftWitnessList leftContext bound
        witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
        axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
        rightWitnessList rightContext current
        hwitnessTraversal haxiomTraversal hrows hright hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedPAWitnessedPrefixMergeStateTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 5)
      (tVar 6) (tVar 7) (tVar 8) (tVar 9)
      (tVar 10) (tVar 11) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Public unconditional prefix merge.  The existential context is built by
    the represented reverse fold above.  It is an honest witnessed package,
    contains both inputs, and uniformly accepts every proof from the literal
    right-hand context. *)
Theorem raw_codedPAAxiomWitnessContext_prefixMerge : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftWitnessList leftContext rightWitnessList rightContext,
  RawCodedPAAxiomWitnessContext M leftWitnessList leftContext ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  exists mergedWitnessList mergedContext : M,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawContextListIncluded M leftWitnessList mergedWitnessList /\
    RawContextListIncluded M leftContext mergedContext /\
    RawContextListIncluded M rightWitnessList mergedWitnessList /\
    RawContextListIncluded M rightContext mergedContext /\
    RawCodedPALocalProofContextTransport M rightContext mergedContext.
Proof.
  intros M hPA leftWitnessList leftContext
    rightWitnessList rightContext hleft hright.
  destruct hleft as
    (bound & witnessTailCode & witnessTailStep & witnessHeadCode &
      witnessHeadStep & axiomTailCode & axiomTailStep & axiomHeadCode &
      axiomHeadStep & hleftTables).
  unfold RawCodedPAAxiomWitnessContextWithTables in hleftTables.
  destruct hleftTables as
    [hwitnessTraversal [haxiomTraversal hrows]].
  pose proof (raw_codedPAWitnessedPrefixMergeState_all M hPA
    leftWitnessList leftContext bound
    witnessTailCode witnessTailStep witnessHeadCode witnessHeadStep
    axiomTailCode axiomTailStep axiomHeadCode axiomHeadStep
    rightWitnessList rightContext
    hwitnessTraversal haxiomTraversal hrows hright bound) as hfinal.
  destruct hwitnessTraversal as
    [hwitnessRoot [hwitnessEnd [hwitnessDefined hwitnessRows]]].
  destruct haxiomTraversal as
    [haxiomRoot [haxiomEnd [haxiomDefined haxiomRows]]].
  destruct (hfinal (raw_zero M) leftWitnessList leftContext
    (raw_add_zero_left M hPA bound) hwitnessRoot haxiomRoot) as
    [hleftWitnessRealizable [hleftContextRealizable
      (mergedWitnessList & mergedContext & hmerged &
        hleftWitnessIncluded & hleftContextIncluded &
        hrightWitnessIncluded & hrightContextIncluded & htransport)]].
  exists mergedWitnessList, mergedContext.
  repeat split; assumption.
Qed.

(** Direct one-sided proof endpoint, useful independently of the unresolved
    opposite weakening direction. *)
Corollary raw_codedPALocalProof_witnessedContext_prefixMerge_right : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      leftWitnessList leftContext rightWitnessList rightContext
      conclusion root,
  RawCodedPAAxiomWitnessContext M leftWitnessList leftContext ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  RawCodedPALocalProofOf M rightContext conclusion root ->
  exists mergedWitnessList mergedContext transportedRoot : M,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawContextListIncluded M leftContext mergedContext /\
    RawContextListIncluded M rightContext mergedContext /\
    RawCodedPALocalProofOf M mergedContext conclusion transportedRoot.
Proof.
  intros M hPA leftWitnessList leftContext
    rightWitnessList rightContext conclusion root hleft hright hproof.
  destruct (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
    leftWitnessList leftContext rightWitnessList rightContext
    hleft hright) as
    (mergedWitnessList & mergedContext & hmerged &
      hleftWitnessIncluded & hleftContextIncluded &
      hrightWitnessIncluded & hrightContextIncluded & htransport).
  destruct (htransport conclusion root hproof)
    as [transportedRoot htransported].
  exists mergedWitnessList, mergedContext, transportedRoot.
  split; [exact hmerged |].
  split; [exact hleftContextIncluded |].
  split; [exact hrightContextIncluded |].
  exact htransported.
Qed.

(** ------------------------------------------------------------------
    The exact remaining direction and its consequences. *)

(** This is deliberately a [Definition], not an axiom.  It names the one
    proof-tree operation not supplied by the prefix construction: rebuild a
    proof from a witnessed source PA context over a witnessed target PA
    context which contains every source member.  Restricting both endpoints
    to witnessed contexts excludes malformed carrier lists, but binder rules
    still make the operation genuinely stronger than head insertion. *)
Definition RawCodedPALocalProofWitnessedContextInclusionWeakening
    (M : RawPAModel) : Prop :=
  forall sourceWitnessList sourceContext
      targetWitnessList targetContext conclusion root : M,
    RawCodedPAAxiomWitnessContext M sourceWitnessList sourceContext ->
    RawCodedPAAxiomWitnessContext M targetWitnessList targetContext ->
    RawContextListIncluded M sourceContext targetContext ->
    RawCodedPALocalProofOf M sourceContext conclusion root ->
    exists transportedRoot : M,
      RawCodedPALocalProofOf M targetContext conclusion transportedRoot.

Arguments RawCodedPALocalProofWitnessedContextInclusionWeakening M
  : clear implicits.

(** Reusable two-certificate/common-context merge.  The right proof direction
    is unconditional and comes from the represented prefix fold; the named
    inclusion weakening is used exactly once, for the left proof. *)
Theorem raw_codedPALocalProof_twoWitnessedContexts_commonContext_of_weakening :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofWitnessedContextInclusionWeakening M ->
  forall leftWitnessList leftContext leftConclusion leftRoot
      rightWitnessList rightContext rightConclusion rightRoot,
  RawCodedPAAxiomWitnessContext M leftWitnessList leftContext ->
  RawCodedPALocalProofOf M leftContext leftConclusion leftRoot ->
  RawCodedPAAxiomWitnessContext M rightWitnessList rightContext ->
  RawCodedPALocalProofOf M rightContext rightConclusion rightRoot ->
  exists mergedWitnessList mergedContext
      transportedLeftRoot transportedRightRoot : M,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawCodedPALocalProofOf M
      mergedContext leftConclusion transportedLeftRoot /\
    RawCodedPALocalProofOf M
      mergedContext rightConclusion transportedRightRoot.
Proof.
  intros M hPA hweakening
    leftWitnessList leftContext leftConclusion leftRoot
    rightWitnessList rightContext rightConclusion rightRoot
    hleft hleftProof hright hrightProof.
  destruct (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
    leftWitnessList leftContext rightWitnessList rightContext
    hleft hright) as
    (mergedWitnessList & mergedContext & hmerged &
      hleftWitnessIncluded & hleftContextIncluded &
      hrightWitnessIncluded & hrightContextIncluded & htransport).
  destruct (hweakening
    leftWitnessList leftContext mergedWitnessList mergedContext
    leftConclusion leftRoot hleft hmerged hleftContextIncluded hleftProof)
    as [transportedLeftRoot htransportedLeft].
  destruct (htransport rightConclusion rightRoot hrightProof)
    as [transportedRightRoot htransportedRight].
  exists mergedWitnessList, mergedContext,
    transportedLeftRoot, transportedRightRoot.
  split; [exact hmerged |].
  split; assumption.
Qed.

(** Accumulator form used by the fixed six-way fold.  It retains the uniform
    transport from the old common context, so every already synchronized root
    can be moved to the same newly returned context. *)
Lemma raw_codedPALocalProof_addWitnessedContext_of_weakening : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofWitnessedContextInclusionWeakening M ->
  forall newWitnessList newContext newConclusion newRoot
      baseWitnessList baseContext,
  RawCodedPAAxiomWitnessContext M newWitnessList newContext ->
  RawCodedPALocalProofOf M newContext newConclusion newRoot ->
  RawCodedPAAxiomWitnessContext M baseWitnessList baseContext ->
  exists mergedWitnessList mergedContext transportedNewRoot : M,
    RawCodedPAAxiomWitnessContext M mergedWitnessList mergedContext /\
    RawCodedPALocalProofContextTransport M baseContext mergedContext /\
    RawCodedPALocalProofOf M
      mergedContext newConclusion transportedNewRoot.
Proof.
  intros M hPA hweakening
    newWitnessList newContext newConclusion newRoot
    baseWitnessList baseContext hnew hnewProof hbase.
  destruct (raw_codedPAAxiomWitnessContext_prefixMerge M hPA
    newWitnessList newContext baseWitnessList baseContext hnew hbase) as
    (mergedWitnessList & mergedContext & hmerged &
      hnewWitnessIncluded & hnewContextIncluded &
      hbaseWitnessIncluded & hbaseContextIncluded & htransport).
  destruct (hweakening
    newWitnessList newContext mergedWitnessList mergedContext
    newConclusion newRoot hnew hmerged hnewContextIncluded hnewProof)
    as [transportedNewRoot htransportedNew].
  exists mergedWitnessList, mergedContext, transportedNewRoot.
  split; [exact hmerged |].
  split; assumption.
Qed.

(** Strip only the transparent outer certificate code.  The exact witnessed
    list, literal context, conclusion, and proof root are retained. *)
Lemma raw_codedPAProofOf_witnessedLocal_fields : forall
    (M : RawPAModel) conclusion certificate,
  RawCodedPAProofOf M conclusion certificate ->
  exists witnessList context root : M,
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawCodedPALocalProofOf M context conclusion root.
Proof.
  intros M conclusion certificate
    (witnessList & root & context & hcertificate & hwitnessed &
      hcoverage & hendpoint).
  exists witnessList, context, root.
  split; [exact hwitnessed |].
  split; assumption.
Qed.

(** The exact reduction requested by the native master-successor interface.
    Five metatheoretic steps are legitimate here because the master arity is
    the fixed standard number six.  Every step itself handles a potentially
    nonstandard witnessed context through the represented prefix theorem.
    Existing roots are all transported by one relation whose target context
    is literal, while the newly added root uses the named left weakening once.
*)
Theorem
    raw_sixFieldMasterOrdinaryProofsCommonContextLift_of_witnessedContextInclusionWeakening :
    forall (M : RawPAModel), RawPASatisfies M ->
  RawCodedPALocalProofWitnessedContextInclusionWeakening M ->
  RawSixFieldMasterOrdinaryProofsCommonContextLift M.
Proof.
  intros M hPA hweakening
    field1 field2 field3 field4 field5 finalField hordinary.
  unfold RawSixFieldMasterOrdinaryProofsOf in hordinary.
  destruct hordinary as
    (certificate1 & certificate2 & certificate3 & certificate4 &
      certificate5 & finalCertificate &
      hcertificate1 & hcertificate2 & hcertificate3 & hcertificate4 &
      hcertificate5 & hfinalCertificate).
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M field1 certificate1 hcertificate1) as
    (witnessList1 & context1 & root1 & hwitnessed1 & hproof1).
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M field2 certificate2 hcertificate2) as
    (witnessList2 & context2 & root2 & hwitnessed2 & hproof2).
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M field3 certificate3 hcertificate3) as
    (witnessList3 & context3 & root3 & hwitnessed3 & hproof3).
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M field4 certificate4 hcertificate4) as
    (witnessList4 & context4 & root4 & hwitnessed4 & hproof4).
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M field5 certificate5 hcertificate5) as
    (witnessList5 & context5 & root5 & hwitnessed5 & hproof5).
  destruct (raw_codedPAProofOf_witnessedLocal_fields
    M finalField finalCertificate hfinalCertificate) as
    (finalWitnessList & finalContext & finalRoot &
      hfinalWitnessed & hfinalProof).

  (** Add field 2 in front of field 1's context. *)
  destruct (raw_codedPALocalProof_addWitnessedContext_of_weakening
    M hPA hweakening
    witnessList2 context2 field2 root2
    witnessList1 context1 hwitnessed2 hproof2 hwitnessed1) as
    (witnessList12 & context12 & root2_12 &
      hwitnessed12 & htransport12 & hproof2_12).
  destruct (htransport12 field1 root1 hproof1) as
    [root1_12 hproof1_12].

  (** Add field 3 and move both accumulated roots together. *)
  destruct (raw_codedPALocalProof_addWitnessedContext_of_weakening
    M hPA hweakening
    witnessList3 context3 field3 root3
    witnessList12 context12 hwitnessed3 hproof3 hwitnessed12) as
    (witnessList123 & context123 & root3_123 &
      hwitnessed123 & htransport123 & hproof3_123).
  destruct (htransport123 field1 root1_12 hproof1_12) as
    [root1_123 hproof1_123].
  destruct (htransport123 field2 root2_12 hproof2_12) as
    [root2_123 hproof2_123].

  (** Add field 4. *)
  destruct (raw_codedPALocalProof_addWitnessedContext_of_weakening
    M hPA hweakening
    witnessList4 context4 field4 root4
    witnessList123 context123 hwitnessed4 hproof4 hwitnessed123) as
    (witnessList1234 & context1234 & root4_1234 &
      hwitnessed1234 & htransport1234 & hproof4_1234).
  destruct (htransport1234 field1 root1_123 hproof1_123) as
    [root1_1234 hproof1_1234].
  destruct (htransport1234 field2 root2_123 hproof2_123) as
    [root2_1234 hproof2_1234].
  destruct (htransport1234 field3 root3_123 hproof3_123) as
    [root3_1234 hproof3_1234].

  (** Add field 5. *)
  destruct (raw_codedPALocalProof_addWitnessedContext_of_weakening
    M hPA hweakening
    witnessList5 context5 field5 root5
    witnessList1234 context1234
    hwitnessed5 hproof5 hwitnessed1234) as
    (witnessList12345 & context12345 & root5_12345 &
      hwitnessed12345 & htransport12345 & hproof5_12345).
  destruct (htransport12345 field1 root1_1234 hproof1_1234) as
    [root1_12345 hproof1_12345].
  destruct (htransport12345 field2 root2_1234 hproof2_1234) as
    [root2_12345 hproof2_12345].
  destruct (htransport12345 field3 root3_1234 hproof3_1234) as
    [root3_12345 hproof3_12345].
  destruct (htransport12345 field4 root4_1234 hproof4_1234) as
    [root4_12345 hproof4_12345].

  (** Add the sixth/final field. *)
  destruct (raw_codedPALocalProof_addWitnessedContext_of_weakening
    M hPA hweakening
    finalWitnessList finalContext finalField finalRoot
    witnessList12345 context12345
    hfinalWitnessed hfinalProof hwitnessed12345) as
    (mergedWitnessList & mergedContext & mergedFinalRoot &
      hmergedWitnessed & hfinalTransport & hmergedFinalProof).
  destruct (hfinalTransport field1 root1_12345 hproof1_12345) as
    [mergedRoot1 hmergedProof1].
  destruct (hfinalTransport field2 root2_12345 hproof2_12345) as
    [mergedRoot2 hmergedProof2].
  destruct (hfinalTransport field3 root3_12345 hproof3_12345) as
    [mergedRoot3 hmergedProof3].
  destruct (hfinalTransport field4 root4_12345 hproof4_12345) as
    [mergedRoot4 hmergedProof4].
  destruct (hfinalTransport field5 root5_12345 hproof5_12345) as
    [mergedRoot5 hmergedProof5].

  unfold RawSixFieldMasterCommonContextProofsOf.
  exists mergedWitnessList, mergedContext,
    mergedRoot1, mergedRoot2, mergedRoot3,
    mergedRoot4, mergedRoot5, mergedFinalRoot.
  split; [exact hmergedWitnessed |].
  split; [exact hmergedProof1 |].
  split; [exact hmergedProof2 |].
  split; [exact hmergedProof3 |].
  split; [exact hmergedProof4 |].
  split; [exact hmergedProof5 |].
  exact hmergedFinalProof.
Qed.

End PABoundedRawCodedPALocalProofWitnessedContextMerge.
