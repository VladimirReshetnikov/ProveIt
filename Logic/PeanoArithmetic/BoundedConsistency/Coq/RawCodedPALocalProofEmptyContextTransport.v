(**
  Transporting a raw local PA proof from the empty context to a supplied
  witnessed PA-axiom context.

  There are two nonstandard-model issues which make the apparently familiar
  weakening argument nontrivial here.

  First, a proof node stores its context literally.  Weakening therefore has
  to rebuild the whole coded proof tree; reusing the old root is not sound.
  [RawCodedPALocalProofContextInsertUnconditional] already performs exactly
  that rebuilding for one atomically adequate context head, using represented
  strong induction on the (possibly nonstandard) proof code.

  Second, a witnessed context may have nonstandard coded length.  We must not
  decode it into a Rocq list and recurse metatheoretically.  The traversal
  certificate stores tails in the order

       Gamma = tail[0], ..., tail[bound] = nil.

  The represented invariant below walks this table backwards.  At stage
  [current] it handles every complementary index satisfying

       index + current = bound.

  Stage zero is the supplied proof over [tail[bound] = nil].  The successor
  step reads the certified row

       tail[index] = head[index] :: tail[S index]

  and applies the existing one-head transplant.  PA's own definable induction
  reaches [current = bound], where the complementary index is zero and hence
  the resulting context is the originally supplied [Gamma].  No Rocq
  recursion ranges over a carrier-valued context or proof.

  The one-head theorem has an honest atomic-adequacy guard because binder
  rules shift their contexts.  Existing represented PA-axiom self-shift gives
  [shift 0 1 axiom axiom] for every (including nonstandard) witness row;
  shift-target adequacy therefore discharges that guard without a semantic
  validity bridge.
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
  RawCodedFormulaShiftAtomicAdequacy
  RawCodedProofAtomicAdequacy
  RawCodedPAAxiomWitness
  RawCodedPAAxiomContextSelfShift
  RawCodedContextLists
  RawCodedContextStructure
  RawCodedRestrictedPAProof
  RawCodedPALocalProofExistential
  RawCodedPALocalProofContextInsertInduction
  RawCodedPALocalProofContextInsertUnconditional
  RawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.

Module PABoundedRawCodedPALocalProofEmptyContextTransport.

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
Import PABoundedRawCodedFormulaShiftAtomicAdequacy.
Import PABoundedRawCodedProofAtomicAdequacy.
Import PABoundedRawCodedPAAxiomWitness.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedContextLists.
Import PABoundedRawCodedContextStructure.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofContextInsertInduction.
Import PABoundedRawCodedPALocalProofContextInsertUnconditional.
Import PABoundedRawCodedDynamicTruthNativeMasterSuccessorFromProofTotals.

(** ------------------------------------------------------------------
    Atomic adequacy of every formula selected by an axiom witness. *)

(** The self-shift theorem is a fully represented syntactic construction.
    In its induction-witness branch, both the source formula and the closure
    count may be nonstandard; the theorem follows their operation traces and
    uses definable induction internally.  The shift-target theorem then turns
    that honest syntax trace into exactly the atomic-adequacy resource needed
    by proof context insertion. *)
Theorem raw_codedPAAxiomWitness_axiom_atomically_adequate : forall
    (M : RawPAModel), RawPASatisfies M -> forall witness axiom,
  RawCodedPAAxiomWitness M witness axiom ->
  RawCodedFormulaAtomicallyAdequate M axiom.
Proof.
  intros M hPA witness axiom hwitness.
  exact (raw_codedFormulaShift_target_atomically_adequate M hPA
    (raw_zero M) (rawNumeralValue M 1) axiom axiom
    (raw_codedPAAxiomWitness_axiom_selfShift
      M hPA witness axiom hwitness)).
Qed.

(** A witnessed context synchronizes witness and axiom head tables row by
    row.  Looking up the witness in a live axiom row and applying the theorem
    above yields an all-head adequacy certificate over the *same* axiom
    traversal tables. *)
Theorem raw_codedPAAxiomWitnessContext_context_all_atomically_adequate :
    forall (M : RawPAModel), RawPASatisfies M -> forall witnessList context,
  RawCodedPAAxiomWitnessContext M witnessList context ->
  RawContextAllAtomicallyAdequate M context.
Proof.
  intros M hPA witnessList context
    (bound & witnessTailCode & witnessTailStep & witnessHeadCode &
     witnessHeadStep & axiomTailCode & axiomTailStep & axiomHeadCode &
     axiomHeadStep & hwitnessed).
  unfold RawCodedPAAxiomWitnessContextWithTables in hwitnessed.
  destruct hwitnessed as [hwitnessTraversal [haxiomTraversal hrows]].
  exists bound, axiomTailCode, axiomTailStep, axiomHeadCode, axiomHeadStep.
  split; [exact haxiomTraversal |].
  intros index hindex axiom haxiomLookup.
  destruct hwitnessTraversal as
    [hwitnessRoot [hwitnessEnd [hwitnessHeadsDefined hwitnessRows]]].
  destruct (hwitnessHeadsDefined index hindex) as
    [witness hwitnessLookup].
  exact (raw_codedPAAxiomWitness_axiom_atomically_adequate M hPA
    witness axiom
    (hrows index witness axiom hindex hwitnessLookup haxiomLookup)).
Qed.

(** ------------------------------------------------------------------
    Represented reverse traversal of an adequate context. *)

(** The state includes realizability of the current suffix as well as the
    transported proof.  Carrying realizability is important: it is exactly
    the side condition needed by the next one-head insertion, and it avoids
    constructing separately re-indexed traversal tables for every suffix of
    the original context. *)
Definition RawCodedPALocalProofSuffixTransportState
    (M : RawPAModel)
    (bound tailCode tailStep target current : M) : Prop :=
  forall index suffix : M,
    raw_add M index current = bound ->
    RawCodedAssignmentLookup M tailCode tailStep index suffix ->
    RawContextListRealizable M suffix /\
    exists root : M, RawCodedPALocalProofOf M suffix target root.

Arguments RawCodedPALocalProofSuffixTransportState
  M bound tailCode tailStep target current : clear implicits.

(** This is the arithmetic formula to which [raw_definable_induction] is
    applied.  The existential root is inside the formula, so every induction
    stage produces an actual represented local proof, not merely a semantic
    assertion about its target. *)
Definition codedPALocalProofSuffixTransportStateTermAt
    (bound tailCode tailStep target current : term) : formula :=
  pAll (pAll
    (pImp
      (pEq (tAdd (tVar 1) (liftTerm 2 current)) (liftTerm 2 bound))
      (pImp
        (codedAssignmentLookupTermAt
          (liftTerm 2 tailCode) (liftTerm 2 tailStep)
          (tVar 1) (tVar 0))
        (pAnd
          (contextListRealizableTermAt (tVar 0))
          (pEx
            (codedPALocalProofForInsertTermAt
              (tVar 1) (liftTerm 3 target) (tVar 0))))))).

Lemma raw_emptyContextTransport_eval_liftTerm_two : forall
    (M : RawPAModel) a b (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b e)) (liftTerm 2 t) =
  raw_term_eval M e t.
Proof.
  intros M a b e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 2) with (S (S index)) by lia. reflexivity.
Qed.

Lemma raw_emptyContextTransport_eval_liftTerm_three : forall
    (M : RawPAModel) a b c (e : nat -> M) t,
  raw_term_eval M (scons M a (scons M b (scons M c e))) (liftTerm 3 t) =
  raw_term_eval M e t.
Proof.
  intros M a b c e t. unfold liftTerm.
  rewrite raw_term_eval_rename. apply raw_term_eval_ext. intro index.
  replace (index + 3) with (S (S (S index))) by lia. reflexivity.
Qed.

Lemma raw_sat_codedPALocalProofSuffixTransportStateTermAt_iff : forall
    (M : RawPAModel) e bound tailCode tailStep target current,
  raw_formula_sat M e
    (codedPALocalProofSuffixTransportStateTermAt
      bound tailCode tailStep target current) <->
  RawCodedPALocalProofSuffixTransportState M
    (raw_term_eval M e bound)
    (raw_term_eval M e tailCode) (raw_term_eval M e tailStep)
    (raw_term_eval M e target) (raw_term_eval M e current).
Proof.
  intros M e bound tailCode tailStep target current.
  unfold codedPALocalProofSuffixTransportStateTermAt,
    RawCodedPALocalProofSuffixTransportState.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedAssignmentLookupTermAt_iff.
  setoid_rewrite raw_sat_contextListRealizableTermAt_iff.
  setoid_rewrite raw_sat_codedPALocalProofForInsertTermAt_iff.
  repeat setoid_rewrite raw_emptyContextTransport_eval_liftTerm_two.
  repeat setoid_rewrite raw_emptyContextTransport_eval_liftTerm_three.
  cbn [raw_term_eval scons]. split.
  - intros h index suffix hsum hlookup.
    apply (h index suffix).
    + rewrite raw_emptyContextTransport_eval_liftTerm_two. exact hsum.
    + exact hlookup.
  - intros h index suffix hsum hlookup.
    rewrite raw_emptyContextTransport_eval_liftTerm_two in hsum.
    exact (h index suffix hsum hlookup).
Qed.

(** At [current = 0], the complement equation makes [index = bound].
    Functionality of the certified tail table then identifies the requested
    suffix with its terminal zero row, so the incoming empty-context proof is
    the required witness. *)
Lemma raw_codedPALocalProofSuffixTransportState_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context bound tailCode tailStep headCode headStep target root,
  RawContextListTraversal M context bound
    tailCode tailStep headCode headStep ->
  RawCodedPALocalProofOf M (raw_zero M) target root ->
  RawCodedPALocalProofSuffixTransportState M
    bound tailCode tailStep target (raw_zero M).
Proof.
  intros M hPA context bound tailCode tailStep headCode headStep
    target root htraversal hproof index suffix hsum hlookup.
  rewrite raw_add_zero_right in hsum by exact hPA. subst index.
  destruct htraversal as [hroot [hend [hheads hrows]]].
  assert (hsuffix : suffix = raw_zero M).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tailCode tailStep bound suffix (raw_zero M) hlookup hend).
  }
  subst suffix. split.
  - exact (raw_contextList_empty_realizable M hPA).
  - exists root. exact hproof.
Qed.

(** For the successor stage, the complement equation itself is the strict
    bound witness [index < bound].  The live traversal row exposes its head
    and next tail.  Arithmetic moves one successor from [current] to [index],
    allowing the induction hypothesis to produce a proof over [nextTail].
    The already represented proof-tree transformer then inserts [head]. *)
Lemma raw_codedPALocalProofSuffixTransportState_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context bound tailCode tailStep headCode headStep target current,
  RawContextListTraversal M context bound
    tailCode tailStep headCode headStep ->
  RawContextAllAtomicallyAdequateWithTables M
    bound headCode headStep ->
  RawCodedPALocalProofSuffixTransportState M
    bound tailCode tailStep target current ->
  RawCodedPALocalProofSuffixTransportState M
    bound tailCode tailStep target (raw_succ M current).
Proof.
  intros M hPA context bound tailCode tailStep headCode headStep
    target current htraversal hadequate hcurrent
    index suffix hsum hlookup.
  assert (hindex : rawLt M index bound).
  { exists current. exact hsum. }
  destruct htraversal as [hroot [hend [hheads hrows]]].
  destruct (hrows index hindex) as
    (rowTail & nextTail & head & hrowTail & hnextTail & hhead & hrow).
  assert (hsuffix : suffix = rowTail).
  {
    exact (raw_codedAssignmentLookup_functional M hPA
      tailCode tailStep index suffix rowTail hlookup hrowTail).
  }
  subst suffix.
  assert (hnextSum :
      raw_add M (raw_succ M index) current = bound).
  {
    rewrite raw_succ_add_pair by exact hPA.
    rewrite <- raw_add_succ by exact hPA. exact hsum.
  }
  destruct (hcurrent (raw_succ M index) nextTail
    hnextSum hnextTail) as [hnextRealizable [nextRoot hnextProof]].
  assert (hheadAdequate : RawCodedFormulaAtomicallyAdequate M head).
  { exact (hadequate index hindex head hhead). }
  destruct (raw_codedPALocalProof_adequateConsTransplant M hPA
    nextTail head target nextRoot hheadAdequate hnextRealizable hnextProof)
    as [newRoot hnewProof].
  rewrite hrow. split.
  - exact (raw_contextList_cons_realizable M hPA
      nextTail head hnextRealizable).
  - exists newRoot. exact hnewProof.
Qed.

(** Definable induction closes the reverse traversal for every carrier-valued
    stage, in particular the possibly nonstandard context length [bound]. *)
Theorem raw_codedPALocalProofSuffixTransportState_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context bound tailCode tailStep headCode headStep target root,
  RawContextListTraversal M context bound
    tailCode tailStep headCode headStep ->
  RawContextAllAtomicallyAdequateWithTables M
    bound headCode headStep ->
  RawCodedPALocalProofOf M (raw_zero M) target root ->
  forall current,
    RawCodedPALocalProofSuffixTransportState M
      bound tailCode tailStep target current.
Proof.
  intros M hPA context bound tailCode tailStep headCode headStep
    target root htraversal hadequate hproof.
  set (parameterEnv := fun n : nat =>
    match n with
    | 0 => bound
    | 1 => tailCode
    | 2 => tailStep
    | _ => target
    end).
  set (phi := codedPALocalProofSuffixTransportStateTermAt
    (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi. apply (proj2
        (raw_sat_codedPALocalProofSuffixTransportStateTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exact (raw_codedPALocalProofSuffixTransportState_zero M hPA
        context bound tailCode tailStep headCode headStep target root
        htraversal hproof).
    - intros current hcurrentSat. unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_codedPALocalProofSuffixTransportStateTermAt_iff M
          (scons M current parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
        hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_codedPALocalProofSuffixTransportStateTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      exact (raw_codedPALocalProofSuffixTransportState_succ M hPA
        context bound tailCode tailStep headCode headStep target current
        htraversal hadequate hcurrent).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_codedPALocalProofSuffixTransportStateTermAt_iff M
      (scons M current parameterEnv)
      (tVar 1) (tVar 2) (tVar 3) (tVar 4) (tVar 0))
    (hall current)) as hcurrent.
  unfold parameterEnv in hcurrent.
  cbn [raw_term_eval scons] in hcurrent. exact hcurrent.
Qed.

(** Generic endpoint: the witness relation is not logically needed once a
    context already carries an all-head atomic-adequacy certificate. *)
Theorem raw_codedPALocalProof_emptyContext_to_atomicallyAdequateContext :
    forall (M : RawPAModel), RawPASatisfies M -> forall context target root,
  RawContextAllAtomicallyAdequate M context ->
  RawCodedPALocalProofOf M (raw_zero M) target root ->
  exists transportedRoot : M,
    RawCodedPALocalProofOf M context target transportedRoot.
Proof.
  intros M hPA context target root
    (bound & tailCode & tailStep & headCode & headStep &
     htraversal & hadequate) hproof.
  pose proof (raw_codedPALocalProofSuffixTransportState_all M hPA
    context bound tailCode tailStep headCode headStep target root
    htraversal hadequate hproof bound) as hfinal.
  destruct htraversal as [hroot [hend [hheads hrows]]].
  destruct (hfinal (raw_zero M) context
    (raw_add_zero_left M hPA bound) hroot) as
    [_ [transportedRoot htransported]].
  exists transportedRoot. exact htransported.
Qed.

(** Exact public interface requested by the native master-successor adapter.
    The supplied witness list and context are preserved literally; only the
    proof root is rebuilt. *)
Theorem raw_codedPAEmptyContextToWitnessedContextTransport : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedPAEmptyContextToWitnessedContextTransport M.
Proof.
  intros M hPA witnessList context target root hwitnessed hproof.
  exact (raw_codedPALocalProof_emptyContext_to_atomicallyAdequateContext
    M hPA context target root
    (raw_codedPAAxiomWitnessContext_context_all_atomically_adequate
      M hPA witnessList context hwitnessed)
    hproof).
Qed.

End PABoundedRawCodedPALocalProofEmptyContextTransport.
