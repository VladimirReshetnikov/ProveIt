(**
  Syntax stability for opening after a represented replacement shift.

  An opening trace describes the target's outer constructors, but a variable
  at the cutoff may be replaced by an entire shifted term whose internal
  nodes do not occur as rows of that trace.  We therefore construct one exact
  support table containing both opening-target occurrences and the shifted
  replacement's certified support.  The latter is guarded by
  [liftedReplacement < enclosing]: if the replacement is too large for the
  target assignment, it cannot occur in the distinguished output or any
  supported subterm below that output.

  The characteristic support table is built by PA-definable induction, so
  all trace bounds and codes may be nonstandard carrier elements.
*)

From Stdlib Require Import List Arith Lia Classical.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability ListFormulas.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedProofDescent RawCodedSyntaxConstructors
  RawCodedAssignment RawCodedFixedLevelTruthTotality
  RawCodedTermEvaluationTraversal RawCodedTermEvaluationRealization
  RawCodedFormulaOperations RawCodedTermShiftSyntaxRealization
  RawCodedTermOpeningTotalityDischarge
  RawCodedFormulaSingleSubstitutionAtomicAdequacy.

Module PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.

Import PA.
Import PAListRepresentability.
Import PAListFormulas.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedTermEvaluationTraversal.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermShiftSyntaxRealization.
Import PABoundedRawCodedTermOpeningTotalityDischarge.
Import PABoundedRawCodedFormulaSingleSubstitutionAtomicAdequacy.

Definition RawTermOpeningAfterShiftSupportDesired (M : RawPAModel)
    (targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep code : M) : Prop :=
  RawTermShiftTargetOccurrence M targetCode targetStep traceBound code \/
  (rawLt M liftedReplacement enclosing /\
   rawLt M code (raw_succ M liftedReplacement) /\
   rawTermCodeSupported M
     replacementSupportCode replacementSupportStep code).

Arguments RawTermOpeningAfterShiftSupportDesired M
  targetCode targetStep traceBound liftedReplacement enclosing
  replacementSupportCode replacementSupportStep code : clear implicits.

Definition termOpeningAfterShiftSupportDesiredTermAt
    (targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep code : term) : formula :=
  pOr
    (termShiftTargetOccurrenceTermAt
      targetCode targetStep traceBound code)
    (pAnd3
      (Formula.ltTermAt liftedReplacement enclosing)
      (Formula.ltTermAt code (tSucc liftedReplacement))
      (termCodeSupportedTermAt
        replacementSupportCode replacementSupportStep code)).

Lemma raw_sat_termOpeningAfterShiftSupportDesiredTermAt_iff : forall
    (M : RawPAModel) e
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep code,
  raw_formula_sat M e
    (termOpeningAfterShiftSupportDesiredTermAt
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep code) <->
  RawTermOpeningAfterShiftSupportDesired M
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e traceBound)
    (raw_term_eval M e liftedReplacement) (raw_term_eval M e enclosing)
    (raw_term_eval M e replacementSupportCode)
    (raw_term_eval M e replacementSupportStep)
    (raw_term_eval M e code).
Proof.
  intros. unfold termOpeningAfterShiftSupportDesiredTermAt,
    RawTermOpeningAfterShiftSupportDesired, pAnd3.
  cbn [raw_formula_sat].
  rewrite raw_sat_termShiftTargetOccurrenceTermAt_iff,
    !raw_sat_ltTermAt_iff,
    raw_sat_termCodeSupportedTermAt_iff.
  reflexivity.
Qed.

Definition RawTermOpeningAfterShiftSupportPrefix (M : RawPAModel)
    (current targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep
      supportCode supportStep : M) : Prop :=
  RawCodedAssignmentDefinedThrough M supportCode supportStep current /\
  forall code : M,
    rawLt M code current ->
    (rawTermCodeSupported M supportCode supportStep code <->
     RawTermOpeningAfterShiftSupportDesired M
       targetCode targetStep traceBound liftedReplacement enclosing
       replacementSupportCode replacementSupportStep code).

Arguments RawTermOpeningAfterShiftSupportPrefix M current
  targetCode targetStep traceBound liftedReplacement enclosing
  replacementSupportCode replacementSupportStep supportCode supportStep
  : clear implicits.

Definition termOpeningAfterShiftSupportPrefixTermAt
    (current targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep
      supportCode supportStep : term) : formula :=
  pAnd
    (codedAssignmentDefinedThroughTermAt supportCode supportStep current)
    (pAll
      (pImp
        (Formula.ltTermAt (tVar 0) (liftTerm 1 current))
        (pAnd
          (pImp
            (termCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep) (tVar 0))
            (termOpeningAfterShiftSupportDesiredTermAt
              (liftTerm 1 targetCode) (liftTerm 1 targetStep)
              (liftTerm 1 traceBound) (liftTerm 1 liftedReplacement)
              (liftTerm 1 enclosing)
              (liftTerm 1 replacementSupportCode)
              (liftTerm 1 replacementSupportStep) (tVar 0)))
          (pImp
            (termOpeningAfterShiftSupportDesiredTermAt
              (liftTerm 1 targetCode) (liftTerm 1 targetStep)
              (liftTerm 1 traceBound) (liftTerm 1 liftedReplacement)
              (liftTerm 1 enclosing)
              (liftTerm 1 replacementSupportCode)
              (liftTerm 1 replacementSupportStep) (tVar 0))
            (termCodeSupportedTermAt
              (liftTerm 1 supportCode) (liftTerm 1 supportStep)
              (tVar 0)))))).

Lemma raw_sat_termOpeningAfterShiftSupportPrefixTermAt_iff : forall
    (M : RawPAModel) e current targetCode targetStep traceBound
      liftedReplacement enclosing replacementSupportCode
      replacementSupportStep supportCode supportStep,
  raw_formula_sat M e
    (termOpeningAfterShiftSupportPrefixTermAt current
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep supportCode supportStep)
  <->
  RawTermOpeningAfterShiftSupportPrefix M
    (raw_term_eval M e current)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e traceBound)
    (raw_term_eval M e liftedReplacement) (raw_term_eval M e enclosing)
    (raw_term_eval M e replacementSupportCode)
    (raw_term_eval M e replacementSupportStep)
    (raw_term_eval M e supportCode) (raw_term_eval M e supportStep).
Proof.
  intros. unfold termOpeningAfterShiftSupportPrefixTermAt,
    RawTermOpeningAfterShiftSupportPrefix.
  cbn [raw_formula_sat].
  rewrite raw_sat_codedAssignmentDefinedThroughTermAt_iff.
  setoid_rewrite raw_sat_ltTermAt_iff.
  setoid_rewrite raw_sat_termCodeSupportedTermAt_iff.
  setoid_rewrite raw_sat_termOpeningAfterShiftSupportDesiredTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_one_traversal.
  cbn [raw_term_eval scons]. tauto.
Qed.

Definition RawTermOpeningAfterShiftSupportPrefixRealizable
    (M : RawPAModel)
    (current targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep : M) : Prop :=
  exists supportCode supportStep : M,
    RawTermOpeningAfterShiftSupportPrefix M current
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep supportCode supportStep.

Arguments RawTermOpeningAfterShiftSupportPrefixRealizable M current
  targetCode targetStep traceBound liftedReplacement enclosing
  replacementSupportCode replacementSupportStep : clear implicits.

Definition termOpeningAfterShiftSupportPrefixRealizableTermAt
    (current targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep : term) : formula :=
  pEx (pEx
    (termOpeningAfterShiftSupportPrefixTermAt
      (liftTerm 2 current) (liftTerm 2 targetCode) (liftTerm 2 targetStep)
      (liftTerm 2 traceBound) (liftTerm 2 liftedReplacement)
      (liftTerm 2 enclosing) (liftTerm 2 replacementSupportCode)
      (liftTerm 2 replacementSupportStep) (tVar 1) (tVar 0))).

Lemma raw_sat_termOpeningAfterShiftSupportPrefixRealizableTermAt_iff :
  forall (M : RawPAModel) e current targetCode targetStep traceBound
    liftedReplacement enclosing replacementSupportCode replacementSupportStep,
  raw_formula_sat M e
    (termOpeningAfterShiftSupportPrefixRealizableTermAt current
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep) <->
  RawTermOpeningAfterShiftSupportPrefixRealizable M
    (raw_term_eval M e current)
    (raw_term_eval M e targetCode) (raw_term_eval M e targetStep)
    (raw_term_eval M e traceBound)
    (raw_term_eval M e liftedReplacement) (raw_term_eval M e enclosing)
    (raw_term_eval M e replacementSupportCode)
    (raw_term_eval M e replacementSupportStep).
Proof.
  intros. unfold termOpeningAfterShiftSupportPrefixRealizableTermAt,
    RawTermOpeningAfterShiftSupportPrefixRealizable.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_termOpeningAfterShiftSupportPrefixTermAt_iff.
  repeat setoid_rewrite raw_term_eval_liftTerm_two_traversal.
  cbn [raw_term_eval scons]. reflexivity.
Qed.

Lemma raw_termOpeningAfterShiftSupportPrefix_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep,
  RawTermOpeningAfterShiftSupportPrefix M (raw_zero M)
    targetCode targetStep traceBound liftedReplacement enclosing
    replacementSupportCode replacementSupportStep
    (raw_zero M) (raw_zero M).
Proof.
  intros M hPA targetCode targetStep traceBound liftedReplacement enclosing
    replacementSupportCode replacementSupportStep. split.
  - exact (raw_codedAssignment_empty_defined M hPA).
  - intros code hcode. exfalso.
    exact (raw_not_lt_zero M hPA code hcode).
Qed.

Lemma raw_termOpeningAfterShiftSupportPrefix_succ : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      current targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep
      oldSupportCode oldSupportStep,
  RawTermOpeningAfterShiftSupportPrefix M current
    targetCode targetStep traceBound liftedReplacement enclosing
    replacementSupportCode replacementSupportStep
    oldSupportCode oldSupportStep ->
  exists newSupportCode newSupportStep : M,
    RawTermOpeningAfterShiftSupportPrefix M (raw_succ M current)
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep
      newSupportCode newSupportStep.
Proof.
  intros M hPA current targetCode targetStep traceBound liftedReplacement
    enclosing replacementSupportCode replacementSupportStep
    oldSupportCode oldSupportStep [holdDefined holdExact].
  destruct (classic (RawTermOpeningAfterShiftSupportDesired M
    targetCode targetStep traceBound liftedReplacement enclosing
    replacementSupportCode replacementSupportStep current))
    as [hdesired | hnotDesired].
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      oldSupportCode oldSupportStep current (rawNumeralValue M 1)
      holdDefined) as
      (newSupportCode & newSupportStep & hnewDefined & hpreserve & hnewValue).
    exists newSupportCode, newSupportStep. split; [exact hnewDefined |].
    intros code hcode.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + split.
      * intro hnewSupported.
        destruct (holdDefined code hbefore) as [oldValue holdValue].
        assert (hpreserved : RawCodedAssignmentLookup M
            newSupportCode newSupportStep code oldValue).
        { exact (hpreserve code oldValue hbefore holdValue). }
        assert (holdValueOne : oldValue = rawNumeralValue M 1).
        {
          apply (raw_codedAssignmentLookup_functional M hPA
            newSupportCode newSupportStep code oldValue
            (rawNumeralValue M 1)); assumption.
        }
        apply (proj1 (holdExact code hbefore)).
        unfold rawTermCodeSupported.
        rewrite <- holdValueOne. exact holdValue.
      * intro hdesiredOld.
        unfold rawTermCodeSupported in *.
        exact (hpreserve code (rawNumeralValue M 1) hbefore
          (proj2 (holdExact code hbefore) hdesiredOld)).
    + split; [intros _; exact hdesired | intros _].
      unfold rawTermCodeSupported. exact hnewValue.
  - destruct (raw_codedAssignmentAppend_defined_exists M hPA
      oldSupportCode oldSupportStep current (raw_zero M)
      holdDefined) as
      (newSupportCode & newSupportStep & hnewDefined & hpreserve & hnewValue).
    exists newSupportCode, newSupportStep. split; [exact hnewDefined |].
    intros code hcode.
    destruct (raw_lt_succ_cases M hPA code current hcode)
      as [hbefore | ->].
    + split.
      * intro hnewSupported.
        destruct (holdDefined code hbefore) as [oldValue holdValue].
        assert (hpreserved : RawCodedAssignmentLookup M
            newSupportCode newSupportStep code oldValue).
        { exact (hpreserve code oldValue hbefore holdValue). }
        assert (holdValueOne : oldValue = rawNumeralValue M 1).
        {
          apply (raw_codedAssignmentLookup_functional M hPA
            newSupportCode newSupportStep code oldValue
            (rawNumeralValue M 1)); assumption.
        }
        apply (proj1 (holdExact code hbefore)).
        unfold rawTermCodeSupported.
        rewrite <- holdValueOne. exact holdValue.
      * intro hdesiredOld.
        unfold rawTermCodeSupported in *.
        exact (hpreserve code (rawNumeralValue M 1) hbefore
          (proj2 (holdExact code hbefore) hdesiredOld)).
    + split.
      * intro hnewSupported. exfalso.
        apply (raw_termShiftSyntax_zero_neq_one M hPA). symmetry.
        exact (raw_codedAssignmentLookup_functional M hPA
          newSupportCode newSupportStep current
          (rawNumeralValue M 1) (raw_zero M)
          hnewSupported hnewValue).
      * intro hdesired. exfalso. exact (hnotDesired hdesired).
Qed.

Theorem raw_termOpeningAfterShiftSupportPrefix_exists : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      targetCode targetStep traceBound liftedReplacement enclosing
      replacementSupportCode replacementSupportStep current,
  RawTermOpeningAfterShiftSupportPrefixRealizable M current
    targetCode targetStep traceBound liftedReplacement enclosing
    replacementSupportCode replacementSupportStep.
Proof.
  intros M hPA targetCode targetStep traceBound liftedReplacement enclosing
    replacementSupportCode replacementSupportStep.
  set (parameterEnv :=
    scons M targetCode
      (scons M targetStep
        (scons M traceBound
          (scons M liftedReplacement
            (scons M enclosing
              (scons M replacementSupportCode
                (scons M replacementSupportStep
                  (fun _ : nat => raw_zero M)))))))).
  set (phi := termOpeningAfterShiftSupportPrefixRealizableTermAt
    (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
    (tVar 5) (tVar 6) (tVar 7)).
  assert (hall : forall current,
      raw_formula_sat M (scons M current parameterEnv) phi).
  {
    apply (raw_definable_induction M hPA phi parameterEnv).
    - unfold phi.
      apply (proj2
        (raw_sat_termOpeningAfterShiftSupportPrefixRealizableTermAt_iff M
          (scons M (raw_zero M) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7))).
      unfold parameterEnv. cbn [raw_term_eval scons].
      exists (raw_zero M), (raw_zero M).
      exact (raw_termOpeningAfterShiftSupportPrefix_zero M hPA
        targetCode targetStep traceBound liftedReplacement enclosing
        replacementSupportCode replacementSupportStep).
    - intros current hcurrentSat.
      unfold phi in hcurrentSat |- *.
      pose proof (proj1
        (raw_sat_termOpeningAfterShiftSupportPrefixRealizableTermAt_iff M
          (scons M current parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7)) hcurrentSat) as hcurrent.
      apply (proj2
        (raw_sat_termOpeningAfterShiftSupportPrefixRealizableTermAt_iff M
          (scons M (raw_succ M current) parameterEnv)
          (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
          (tVar 5) (tVar 6) (tVar 7))).
      unfold parameterEnv in hcurrent |- *.
      cbn [raw_term_eval scons] in hcurrent |- *.
      destruct hcurrent as [oldSupportCode [oldSupportStep hold]].
      exact (raw_termOpeningAfterShiftSupportPrefix_succ M hPA current
        targetCode targetStep traceBound liftedReplacement enclosing
        replacementSupportCode replacementSupportStep
        oldSupportCode oldSupportStep hold).
  }
  intro current. unfold phi in hall.
  pose proof (proj1
    (raw_sat_termOpeningAfterShiftSupportPrefixRealizableTermAt_iff M
      (scons M current parameterEnv)
      (tVar 0) (tVar 1) (tVar 2) (tVar 3) (tVar 4)
      (tVar 5) (tVar 6) (tVar 7)) (hall current)) as hraw.
  unfold parameterEnv in hraw.
  cbn [raw_term_eval scons] in hraw. exact hraw.
Qed.

(** A syntax row can be transported to a larger support table once each
    recursive child supported by the old table is supported by the new one.
    Variable and zero rows contain no recursive support premise. *)
Lemma raw_termSyntaxStep_support_mono : forall
    (M : RawPAModel) code oldSupportCode oldSupportStep
      newSupportCode newSupportStep,
  RawTermSyntaxStep M code oldSupportCode oldSupportStep ->
  (forall child,
    rawLt M child code ->
    rawTermCodeSupported M oldSupportCode oldSupportStep child ->
    rawTermCodeSupported M newSupportCode newSupportStep child) ->
  RawTermSyntaxStep M code newSupportCode newSupportStep.
Proof.
  intros M code oldSupportCode oldSupportStep
    newSupportCode newSupportStep (left & right & hrow) hmono.
  exists left, right.
  destruct hrow as
    [hvar | [hzero | [hsucc | [hadd | hmul]]]].
  - left. exact hvar.
  - right. left. exact hzero.
  - right. right. left.
    destruct hsucc as [hcode [hleftSupported hleft]].
    split; [exact hcode |]. split.
    + exact (hmono left hleft hleftSupported).
    + exact hleft.
  - right. right. right. left.
    destruct hadd as
      [hcode [hleftSupported [hrightSupported [hleft hright]]]].
    split; [exact hcode |]. repeat split.
    + exact (hmono left hleft hleftSupported).
    + exact (hmono right hright hrightSupported).
    + exact hleft.
    + exact hright.
  - right. right. right. right.
    destruct hmul as
      [hcode [hleftSupported [hrightSupported [hleft hright]]]].
    split; [exact hcode |]. repeat split.
    + exact (hmono left hleft hleftSupported).
    + exact (hmono right hright hrightSupported).
    + exact hleft.
    + exact hright.
Qed.

Lemma raw_termOpening_code_lt_enclosing : forall
    (M : RawPAModel), RawPASatisfies M -> forall code root enclosing,
  rawLt M code (raw_succ M root) ->
  rawLt M root enclosing ->
  rawLt M code enclosing.
Proof.
  intros M hPA code root enclosing hcode hroot.
  destruct (raw_lt_succ_cases M hPA code root hcode)
    as [hbefore | ->].
  - exact (raw_assignment_lt_trans M hPA code root enclosing
      hbefore hroot).
  - exact hroot.
Qed.

(** The target of an opening trace is syntactically realizable whenever its
    inserted replacement arose from a represented shift of a realizable
    source term.  Disconnected trace rows are harmless: replacement support
    is guarded by the enclosing bound and the final combined support is
    truncated at [succ output]. *)
Theorem
    raw_codedTermOpeningTrace_target_syntax_realizable_after_shift : forall
    (M : RawPAModel), RawPASatisfies M -> forall
    replacement depth liftedReplacement
    shiftSourceCode shiftSourceStep shiftTargetCode shiftTargetStep
    shiftBound shiftRootIndex
    input output
    openingSourceCode openingSourceStep openingTargetCode openingTargetStep
    openingBound openingRootIndex
    replacementAssignmentCode replacementAssignmentStep
    targetAssignmentCode targetAssignmentStep enclosing,
  RawCodedTermShiftTrace M (raw_zero M) depth
    shiftSourceCode shiftSourceStep shiftTargetCode shiftTargetStep
    shiftBound shiftRootIndex replacement liftedReplacement ->
  RawCodedTermOpeningTrace M depth liftedReplacement
    openingSourceCode openingSourceStep openingTargetCode openingTargetStep
    openingBound openingRootIndex input output ->
  RawTermSyntaxRealizable M replacement
    replacementAssignmentCode replacementAssignmentStep ->
  rawLt M output enclosing ->
  RawCodedAssignmentDefinedThrough M
    targetAssignmentCode targetAssignmentStep enclosing ->
  RawTermSyntaxRealizable M output
    targetAssignmentCode targetAssignmentStep.
Proof.
  intros M hPA replacement depth liftedReplacement
    shiftSourceCode shiftSourceStep shiftTargetCode shiftTargetStep
    shiftBound shiftRootIndex input output
    openingSourceCode openingSourceStep openingTargetCode openingTargetStep
    openingBound openingRootIndex
    replacementAssignmentCode replacementAssignmentStep
    targetAssignmentCode targetAssignmentStep enclosing
    hshift hopening hreplacement houtputEnclosing hassignment.
  assert (hreplacementSupport : exists supportCode supportStep : M,
      rawLt M liftedReplacement enclosing ->
      RawTermSyntaxCertificateWithSupport M liftedReplacement
        targetAssignmentCode targetAssignmentStep supportCode supportStep).
  {
    destruct (classic (rawLt M liftedReplacement enclosing))
      as [hlifted | hnotLifted].
    - pose proof (raw_codedTermShiftTrace_target_syntax_realizable M hPA
        (raw_zero M) depth
        shiftSourceCode shiftSourceStep shiftTargetCode shiftTargetStep
        shiftBound shiftRootIndex replacement liftedReplacement
        targetAssignmentCode targetAssignmentStep enclosing
        hshift hlifted hassignment) as hsyntax.
      destruct hsyntax as [supportCode [supportStep hcertificate]].
      exists supportCode, supportStep. intros _. exact hcertificate.
    - exists (raw_zero M), (raw_zero M).
      intro hcontra. exfalso. exact (hnotLifted hcontra).
  }
  destruct hreplacementSupport as
    (replacementSupportCode & replacementSupportStep & hreplacementSupport).
  destruct (raw_termOpeningAfterShiftSupportPrefix_exists M hPA
    openingTargetCode openingTargetStep openingBound
    liftedReplacement enclosing replacementSupportCode
    replacementSupportStep (raw_succ M output)) as
    (supportCode & supportStep & hsupportDefined & hsupportExact).
  destruct hopening as
    (hsourceDefined & htargetDefined & hrootBelow & hrootLookup & hrows).
  exists supportCode, supportStep.
  unfold RawTermSyntaxCertificateWithSupport.
  split.
  - split; [exact hsupportDefined |].
    intros code hcodeBound hsupported.
    pose proof (proj1 (hsupportExact code hcodeBound) hsupported)
      as hdesired.
    destruct hdesired as [hoccurrence | hreplacementDesired].
    + destruct hoccurrence as [index [hindexBound htargetLookup]].
      destruct (hsourceDefined index hindexBound)
        as [source hsourceLookup].
      pose proof (hrows index source code hindexBound
        (conj hsourceLookup htargetLookup)) as hrow.
      unfold RawCodedTermOpeningTraversalRow,
        RawCodedTermOperationTraversalRow in hrow.
      destruct hrow as
        [hvariable | [hzero | [hsucc | [hadd | hmul]]]].
      * destruct hvariable as [inputIndex [hinput hcases]].
        destruct hcases as
          [[hlow htarget] |
           [[hatCutoff htarget] |
            (predecessor & hsuccessor & hhigh & htarget)]].
        -- exists inputIndex, (raw_zero M). left. exact htarget.
        -- assert (hliftedEnclosing : rawLt M liftedReplacement enclosing).
           {
             rewrite <- htarget.
             exact (raw_termOpening_code_lt_enclosing M hPA
               code output enclosing hcodeBound houtputEnclosing).
           }
           destruct (hreplacementSupport hliftedEnclosing) as
             [[hreplacementDefined hreplacementRows]
               [hreplacementAssignment hreplacementRoot]].
           apply (raw_termSyntaxStep_support_mono M code
             replacementSupportCode replacementSupportStep
             supportCode supportStep).
           ++ rewrite htarget.
              apply (hreplacementRows liftedReplacement
                (raw_assignment_lt_self_succ M hPA liftedReplacement)
                hreplacementRoot).
           ++ intros child hchild hchildSupported.
              apply (proj2 (hsupportExact child
                (raw_assignment_lt_trans M hPA child code
                  (raw_succ M output) hchild hcodeBound))).
              right. split; [exact hliftedEnclosing |]. split.
              (* The old replacement traversal bounds every supported child
                 by [succ liftedReplacement]; [code] is that root here. *)
              { rewrite htarget in hchild.
                exact (raw_assignment_lt_trans M hPA child
                  liftedReplacement (raw_succ M liftedReplacement)
                  hchild
                  (raw_assignment_lt_self_succ M hPA
                    liftedReplacement)). }
              { exact hchildSupported. }
        -- exists predecessor, (raw_zero M). left. exact htarget.
      * exists (raw_zero M), (raw_zero M). right; left.
        exact (proj2 hzero).
      * destruct hsucc as
          (childIndex & inputChild & outputChild &
           hchildIndex & hchildLookup & hinput & htarget).
        assert (hchildCode : rawLt M outputChild code).
        {
          rewrite htarget.
          exact (raw_termShiftSyntax_succ_child_lt M hPA outputChild).
        }
        assert (hchildBound : rawLt M outputChild (raw_succ M output)).
        {
          exact (raw_assignment_lt_trans M hPA
            outputChild code (raw_succ M output) hchildCode hcodeBound).
        }
        exists outputChild, (raw_zero M). right; right; left.
        split; [exact htarget |]. split.
        -- apply (proj2 (hsupportExact outputChild hchildBound)).
           left. exists childIndex. split.
           ++ exact (raw_assignment_lt_trans M hPA
                childIndex index openingBound hchildIndex hindexBound).
           ++ exact (proj2 hchildLookup).
        -- exact hchildCode.
      * destruct hadd as
          (leftIndex & inputLeft & outputLeft &
           rightIndex & inputRight & outputRight &
           hleftIndex & hleftLookup & hrightIndex & hrightLookup &
           hinput & htarget).
        assert (hleftCode : rawLt M outputLeft code).
        {
          rewrite htarget. unfold rawTermAddCode.
          exact (raw_termShiftSyntax_binary_left_lt M hPA _ _ _).
        }
        assert (hrightCode : rawLt M outputRight code).
        {
          rewrite htarget. unfold rawTermAddCode.
          exact (raw_termShiftSyntax_binary_right_lt M hPA _ _ _).
        }
        assert (hleftBound : rawLt M outputLeft (raw_succ M output)).
        {
          exact (raw_assignment_lt_trans M hPA
            outputLeft code (raw_succ M output) hleftCode hcodeBound).
        }
        assert (hrightBound : rawLt M outputRight (raw_succ M output)).
        {
          exact (raw_assignment_lt_trans M hPA
            outputRight code (raw_succ M output) hrightCode hcodeBound).
        }
        exists outputLeft, outputRight. right; right; right; left.
        split; [exact htarget |]. repeat split.
        -- apply (proj2 (hsupportExact outputLeft hleftBound)).
           left. exists leftIndex. split.
           ++ exact (raw_assignment_lt_trans M hPA
                leftIndex index openingBound hleftIndex hindexBound).
           ++ exact (proj2 hleftLookup).
        -- apply (proj2 (hsupportExact outputRight hrightBound)).
           left. exists rightIndex. split.
           ++ exact (raw_assignment_lt_trans M hPA
                rightIndex index openingBound hrightIndex hindexBound).
           ++ exact (proj2 hrightLookup).
        -- exact hleftCode.
        -- exact hrightCode.
      * destruct hmul as
          (leftIndex & inputLeft & outputLeft &
           rightIndex & inputRight & outputRight &
           hleftIndex & hleftLookup & hrightIndex & hrightLookup &
           hinput & htarget).
        assert (hleftCode : rawLt M outputLeft code).
        {
          rewrite htarget. unfold rawTermMulCode.
          exact (raw_termShiftSyntax_binary_left_lt M hPA _ _ _).
        }
        assert (hrightCode : rawLt M outputRight code).
        {
          rewrite htarget. unfold rawTermMulCode.
          exact (raw_termShiftSyntax_binary_right_lt M hPA _ _ _).
        }
        assert (hleftBound : rawLt M outputLeft (raw_succ M output)).
        {
          exact (raw_assignment_lt_trans M hPA
            outputLeft code (raw_succ M output) hleftCode hcodeBound).
        }
        assert (hrightBound : rawLt M outputRight (raw_succ M output)).
        {
          exact (raw_assignment_lt_trans M hPA
            outputRight code (raw_succ M output) hrightCode hcodeBound).
        }
        exists outputLeft, outputRight. right; right; right; right.
        split; [exact htarget |]. repeat split.
        -- apply (proj2 (hsupportExact outputLeft hleftBound)).
           left. exists leftIndex. split.
           ++ exact (raw_assignment_lt_trans M hPA
                leftIndex index openingBound hleftIndex hindexBound).
           ++ exact (proj2 hleftLookup).
        -- apply (proj2 (hsupportExact outputRight hrightBound)).
           left. exists rightIndex. split.
           ++ exact (raw_assignment_lt_trans M hPA
                rightIndex index openingBound hrightIndex hindexBound).
           ++ exact (proj2 hrightLookup).
        -- exact hleftCode.
        -- exact hrightCode.
    + destruct hreplacementDesired as
        [hliftedEnclosing [hcodeReplacement hreplacementSupported]].
      destruct (hreplacementSupport hliftedEnclosing) as
        [[hreplacementDefined hreplacementRows]
          [hreplacementAssignment hreplacementRoot]].
      apply (raw_termSyntaxStep_support_mono M code
        replacementSupportCode replacementSupportStep
        supportCode supportStep).
      * exact (hreplacementRows code
          hcodeReplacement hreplacementSupported).
      * intros child hchild hchildSupported.
        apply (proj2 (hsupportExact child
          (raw_assignment_lt_trans M hPA child code
            (raw_succ M output) hchild hcodeBound))).
        right. split; [exact hliftedEnclosing |]. split.
        { exact (raw_assignment_lt_trans M hPA child code
            (raw_succ M liftedReplacement) hchild hcodeReplacement). }
        { exact hchildSupported. }
  - split.
    + intros code hcodeBound hsupported index hvariable.
      apply hassignment.
      assert (hindexCode : rawLt M index code).
      {
        rewrite hvariable.
        exact (raw_termShiftSyntax_var_index_lt M hPA index).
      }
      exact (raw_assignment_lt_trans M hPA index code enclosing
        hindexCode
        (raw_termOpening_code_lt_enclosing M hPA
          code output enclosing hcodeBound houtputEnclosing)).
    + apply (proj2 (hsupportExact output
        (raw_assignment_lt_self_succ M hPA output))).
      left. exists openingRootIndex. split; [exact hrootBelow |].
      exact (proj2 hrootLookup).
Qed.

(** The exact interface consumed by formula atomic adequacy is now an
    unconditional consequence of the raw PA axioms. *)
Theorem raw_codedTermOpeningAfterShiftSyntaxStable_of_PA : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCodedTermOpeningAfterShiftSyntaxStable M.
Proof.
  intros M hPA replacement depth input liftedReplacement output
    (shiftSourceCode & shiftSourceStep & shiftTargetCode & shiftTargetStep &
     shiftBound & shiftRootIndex & hshift)
    (openingSourceCode & openingSourceStep &
     openingTargetCode & openingTargetStep &
     openingBound & openingRootIndex & hopening)
    replacementAssignmentCode replacementAssignmentStep hreplacement
    targetAssignmentCode targetAssignmentStep enclosing
    houtput hassignment.
  exact
    (raw_codedTermOpeningTrace_target_syntax_realizable_after_shift M hPA
      replacement depth liftedReplacement
      shiftSourceCode shiftSourceStep shiftTargetCode shiftTargetStep
      shiftBound shiftRootIndex input output
      openingSourceCode openingSourceStep openingTargetCode openingTargetStep
      openingBound openingRootIndex
      replacementAssignmentCode replacementAssignmentStep
      targetAssignmentCode targetAssignmentStep enclosing
      hshift hopening hreplacement houtput hassignment).
Qed.

(** Both former term-level premises of the three-substitution client are now
    supplied internally. *)
Corollary raw_codedFormulaSingleSubstitution_three_exists_total :
  forall (M : RawPAModel), RawPASatisfies M -> forall source,
  RawCodedFormulaAtomicallyAdequate M source ->
  forall replacement1 assignmentCode1 assignmentStep1,
  RawTermSyntaxRealizable M replacement1 assignmentCode1 assignmentStep1 ->
  forall replacement2 assignmentCode2 assignmentStep2,
  RawTermSyntaxRealizable M replacement2 assignmentCode2 assignmentStep2 ->
  forall replacement3 assignmentCode3 assignmentStep3,
  RawTermSyntaxRealizable M replacement3 assignmentCode3 assignmentStep3 ->
  exists target1 target2 target3,
    RawCodedFormulaSingleSubstitution M replacement1 source target1 /\
    RawCodedFormulaAtomicallyAdequate M target1 /\
    RawCodedFormulaSingleSubstitution M replacement2 target1 target2 /\
    RawCodedFormulaAtomicallyAdequate M target2 /\
    RawCodedFormulaSingleSubstitution M replacement3 target2 target3 /\
    RawCodedFormulaAtomicallyAdequate M target3.
Proof.
  intros M hPA source hsource
    replacement1 assignmentCode1 assignmentStep1 hreplacement1
    replacement2 assignmentCode2 assignmentStep2 hreplacement2
    replacement3 assignmentCode3 assignmentStep3 hreplacement3.
  exact (raw_codedFormulaSingleSubstitution_three_exists M hPA
    (raw_codedTermOpening_total M hPA)
    (raw_codedTermOpeningAfterShiftSyntaxStable_of_PA M hPA)
    source hsource
    replacement1 assignmentCode1 assignmentStep1 hreplacement1
    replacement2 assignmentCode2 assignmentStep2 hreplacement2
    replacement3 assignmentCode3 assignmentStep3 hreplacement3).
Qed.

End PABoundedRawCodedTermOpeningAfterShiftSyntaxStability.
