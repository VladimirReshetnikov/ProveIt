(**
  Deep closure of the two native lower-predicate applications.

  The Sigma and Pi successor rows do not invoke their preceding ternary
  predicate through the public application relation syntactically.  Instead,
  each row stores the equivalent fixed chain of three one-place openings with
  replacements [#11], [#2], and [#0].  The first two replacements are exactly
  the protected shifts of the intended arguments [#9] and [#1]; the last
  argument [#0] needs no protection.  Cross-trace functionality therefore
  identifies every native lower application with the relational application

       predicate(#9, #1, #0).

  Once written in that form, deep ternary shift and opening interchange show
  that the result is fixed by every operation whose displayed cutoff is at
  least twenty six.  At such a cutoff all three quoted variables are fixed.
  Functionality of ternary application then identifies the commuting target
  with the original native output.  Atomic adequacy is supplied independently
  by the final trace of the native three-opening chain.
*)

From Stdlib Require Import Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaRankStep
  RawCodedFormulaOperations
  RawCodedTermEvaluationRealization
  RawCodedFixedLevelTruthTotality
  RawCodedFormulaShiftTotality
  RawCodedTermOperationsStandardAdequacy
  RawCodedScopedFormulaDiagonalSubstitution
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedTernaryPredicateDeepClosure
  RawCodedTernaryPredicateDeepClosureShiftInterchange
  RawCodedTernaryPredicateDeepClosureOpeningCommuting
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPiUniversalLeafSourceTemplate
  RawCodedDynamicTruthGlobalSuccessorRootClosure
  RawCodedDynamicTruthGlobalSuccessorDeepClosure.

Module PABoundedRawCodedDynamicTruthLowerApplicationDeepClosure.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaRankStep.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermEvaluationRealization.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedScopedFormulaDiagonalSubstitution.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedTernaryPredicateDeepClosure.
Import PABoundedRawCodedTernaryPredicateDeepClosureShiftInterchange.
Import PABoundedRawCodedTernaryPredicateDeepClosureOpeningCommuting.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiUniversalLeafSourceTemplate.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorRootClosure.
Import PABoundedRawCodedDynamicTruthGlobalSuccessorDeepClosure.

(** ------------------------------------------------------------------
    Reinterpretation of the native fixed traces. *)

(** The protected shifts in a ternary application send [#9] to [#11] and
    [#1] to [#2].  After these two exact standard shift traces are installed,
    the three substitution premises are literally those stored by the native
    Sigma-row lower-application graph. *)
Lemma raw_dynamicTruthCoqLowerApplication_as_ternaryApplication : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawDynamicTruthCoqLowerApplication M predicate output ->
  RawCodedTernaryApplication M predicate
    (rawQuotedTermCode M (tVar 9))
    (rawQuotedTermCode M (tVar 1))
    (rawQuotedTermCode M (tVar 0))
    output.
Proof.
  intros M hPA predicate output
    (firstResult & secondResult & hfirst & hsecond & hthird).
  exists
    (rawQuotedTermCode M dynamicTruthCoqLowerFirstReplacement),
    (rawQuotedTermCode M dynamicTruthCoqLowerSecondReplacement),
    firstResult, secondResult.
  repeat split.
  - pose proof (raw_codedTermShift_standard M hPA 0 2 (tVar 9))
      as hshift.
    cbn [standardTermShift] in hshift.
    exact hshift.
  - pose proof (raw_codedTermShift_standard M hPA 0 1 (tVar 1))
      as hshift.
    cbn [standardTermShift] in hshift.
    exact hshift.
  - rewrite (rawQuotedTermCode_standard M hPA
      dynamicTruthCoqLowerFirstReplacement).
    exact hfirst.
  - rewrite (rawQuotedTermCode_standard M hPA
      dynamicTruthCoqLowerSecondReplacement).
    exact hsecond.
  - rewrite <- (rawQuotedTermCode_standard M hPA
      dynamicTruthCoqLowerThirdReplacement) in hthird.
    exact hthird.
Qed.

(** The Pi-facing graph has the same three replacement terms.  Its existing
    polarity equivalence lets us reuse the preceding trace identification
    instead of duplicating the cross-trace argument. *)
Lemma raw_dynamicTruthPiCoqLowerApplication_as_ternaryApplication : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawDynamicTruthPiCoqLowerApplication M predicate output ->
  RawCodedTernaryApplication M predicate
    (rawQuotedTermCode M (tVar 9))
    (rawQuotedTermCode M (tVar 1))
    (rawQuotedTermCode M (tVar 0))
    output.
Proof.
  intros M hPA predicate output hlower.
  apply (raw_dynamicTruthCoqLowerApplication_as_ternaryApplication
    M hPA predicate output).
  exact (proj1 (raw_dynamicTruthPiCoqLowerApplication_iff_sigma
    M predicate output) hlower).
Qed.

(** ------------------------------------------------------------------
    Identity operations on the three quoted arguments. *)

(** A standard term scoped below [scope <= 26] is fixed by every shift whose
    carrier-valued cutoff lies above the displayed root twenty six.  Factoring
    this elementary weakening out keeps the two closure halves symmetric. *)
Lemma raw_codedTermShift_standard_identity_from_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      scope cutoff amount input,
  StandardTermScoped scope input ->
  scope <= 26 ->
  rawLe M (rawNumeralValue M 26) cutoff ->
  RawCodedTermShift M cutoff amount
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA scope cutoff amount input hscoped hscope hcutoff.
  apply (raw_codedTermShift_standard_scoped_identity
    M hPA scope cutoff amount input hscoped).
  exact (raw_le_trans M hPA
    (rawNumeralValue M scope) (rawNumeralValue M 26) cutoff
    (rawLe_numerals_of_le M hPA scope 26 hscope) hcutoff).
Qed.

(** For substitution, honest syntax of the arbitrary replacement first
    supplies its lift to [depth].  Since the quoted argument lies below that
    depth, the following opening is the identity.  Notice that no standardness
    assumption is made about the replacement or depth. *)
Lemma
    raw_codedFormulaSubstitutionAtom_standard_identity_from_twenty_six :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      replacement assignmentCode assignmentStep depth scope input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  StandardTermScoped scope input ->
  scope <= 26 ->
  rawLe M (rawNumeralValue M 26) depth ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA replacement assignmentCode assignmentStep
    depth scope input hreplacement hscoped hscope hdepth.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    replacement assignmentCode assignmentStep hreplacement
    (raw_zero M) depth) as [liftedReplacement hlift].
  exists liftedReplacement. split.
  - exact hlift.
  - apply (raw_codedTermOpening_standard_identity_below
      M hPA scope depth liftedReplacement input hscoped).
    exact (raw_le_trans M hPA
      (rawNumeralValue M scope) (rawNumeralValue M 26) depth
      (rawLe_numerals_of_le M hPA scope 26 hscope) hdepth).
Qed.

(** A relation-level lower application of the fixed variables is deeply
    closed from twenty six whenever its predicate is a deeply closed ternary
    predicate.  This common argument is deliberately separated from the two
    native wrappers below. *)
Theorem raw_fixedLowerTernaryApplication_deep_closed_from_twenty_six : forall
    (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawCodedTernaryApplication M predicate
    (rawQuotedTermCode M (tVar 9))
    (rawQuotedTermCode M (tVar 1))
    (rawQuotedTermCode M (tVar 0)) output ->
  RawCodedFormulaAtomicallyAdequate M output ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) output.
Proof.
  intros M hPA predicate output hpredicate happlication hadequate.
  split; [exact hadequate |]. split.
  - intros cutoff amount hcutoff.
    assert (hfirst : RawCodedTermShift M cutoff amount
        (rawQuotedTermCode M (tVar 9))
        (rawQuotedTermCode M (tVar 9))).
    {
      apply (raw_codedTermShift_standard_identity_from_twenty_six
        M hPA 10 cutoff amount (tVar 9)).
      - intros index hfree. cbn in hfree. lia.
      - lia.
      - exact hcutoff.
    }
    assert (hsecond : RawCodedTermShift M cutoff amount
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 1))).
    {
      apply (raw_codedTermShift_standard_identity_from_twenty_six
        M hPA 2 cutoff amount (tVar 1)).
      - intros index hfree. cbn in hfree. lia.
      - lia.
      - exact hcutoff.
    }
    assert (hthird : RawCodedTermShift M cutoff amount
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M (tVar 0))).
    {
      apply (raw_codedTermShift_standard_identity_from_twenty_six
        M hPA 1 cutoff amount (tVar 0)).
      - intros index hfree. cbn in hfree. lia.
      - lia.
      - exact hcutoff.
    }
    destruct
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA predicate hpredicate
        cutoff amount
        (rawQuotedTermCode M (tVar 9))
        (rawQuotedTermCode M (tVar 9))
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M (tVar 0))
        output hfirst hsecond hthird happlication)
      as (target & htargetApplication & hshift).
    pose proof (raw_codedTernaryApplication_functional M hPA
      predicate
      (rawQuotedTermCode M (tVar 9))
      (rawQuotedTermCode M (tVar 1))
      (rawQuotedTermCode M (tVar 0))
      target output htargetApplication happlication) as htarget.
    subst target. exact hshift.
  - intros replacement assignmentCode assignmentStep depth
      hreplacement hdepth.
    assert (hfirst : RawCodedFormulaSubstitutionAtom M replacement depth
        (rawQuotedTermCode M (tVar 9))
        (rawQuotedTermCode M (tVar 9))).
    {
      apply
        (raw_codedFormulaSubstitutionAtom_standard_identity_from_twenty_six
          M hPA replacement assignmentCode assignmentStep depth
          10 (tVar 9) hreplacement).
      - intros index hfree. cbn in hfree. lia.
      - lia.
      - exact hdepth.
    }
    assert (hsecond : RawCodedFormulaSubstitutionAtom M replacement depth
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 1))).
    {
      apply
        (raw_codedFormulaSubstitutionAtom_standard_identity_from_twenty_six
          M hPA replacement assignmentCode assignmentStep depth
          2 (tVar 1) hreplacement).
      - intros index hfree. cbn in hfree. lia.
      - lia.
      - exact hdepth.
    }
    assert (hthird : RawCodedFormulaSubstitutionAtom M replacement depth
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M (tVar 0))).
    {
      apply
        (raw_codedFormulaSubstitutionAtom_standard_identity_from_twenty_six
          M hPA replacement assignmentCode assignmentStep depth
          1 (tVar 0) hreplacement).
      - intros index hfree. cbn in hfree. lia.
      - lia.
      - exact hdepth.
    }
    destruct
      (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete
        M hPA predicate hpredicate
        replacement depth
        (rawQuotedTermCode M (tVar 9))
        (rawQuotedTermCode M (tVar 9))
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 1))
        (rawQuotedTermCode M (tVar 0))
        (rawQuotedTermCode M (tVar 0))
        output hfirst hsecond hthird happlication)
      as (target & htargetApplication & hopening).
    pose proof (raw_codedTernaryApplication_functional M hPA
      predicate
      (rawQuotedTermCode M (tVar 9))
      (rawQuotedTermCode M (tVar 1))
      (rawQuotedTermCode M (tVar 0))
      target output htargetApplication happlication) as htarget.
    subst target. exact hopening.
Qed.

(** ------------------------------------------------------------------
    Public native-row corollaries. *)

Theorem raw_dynamicTruthCoqLowerApplication_deep_closed_from_twenty_six :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawDynamicTruthCoqLowerApplication M predicate output ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) output.
Proof.
  intros M hPA predicate output hpredicate hlower.
  apply (raw_fixedLowerTernaryApplication_deep_closed_from_twenty_six
    M hPA predicate output hpredicate).
  - exact (raw_dynamicTruthCoqLowerApplication_as_ternaryApplication
      M hPA predicate output hlower).
  - exact (raw_dynamicTruthSigmaLower_target_atomically_adequate
      M hPA predicate output hlower).
Qed.

Theorem raw_dynamicTruthPiCoqLowerApplication_deep_closed_from_twenty_six :
  forall (M : RawPAModel), RawPASatisfies M -> forall predicate output,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  RawDynamicTruthPiCoqLowerApplication M predicate output ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M 26) output.
Proof.
  intros M hPA predicate output hpredicate hlower.
  apply (raw_fixedLowerTernaryApplication_deep_closed_from_twenty_six
    M hPA predicate output hpredicate).
  - exact (raw_dynamicTruthPiCoqLowerApplication_as_ternaryApplication
      M hPA predicate output hlower).
  - exact (raw_dynamicTruthPiLower_target_atomically_adequate
      M hPA predicate output hlower).
Qed.

End PABoundedRawCodedDynamicTruthLowerApplicationDeepClosure.
