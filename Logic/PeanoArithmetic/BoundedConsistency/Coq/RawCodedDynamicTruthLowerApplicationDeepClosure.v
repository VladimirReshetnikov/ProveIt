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

(** A standard term whose own scope is below an arbitrary displayed root is
    fixed by every shift whose carrier-valued cutoff lies above that root.
    Keeping [scope] separate from [rootScope] avoids forcing clients to weaken
    their metatheoretic scoping derivations before invoking this lemma. *)
Lemma raw_codedTermShift_standard_identity_from_root_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      rootScope scope cutoff amount input,
  StandardTermScoped scope input ->
  scope <= rootScope ->
  rawLe M (rawNumeralValue M rootScope) cutoff ->
  RawCodedTermShift M cutoff amount
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA rootScope scope cutoff amount input
    hscoped hscope hcutoff.
  apply (raw_codedTermShift_standard_scoped_identity
    M hPA scope cutoff amount input hscoped).
  exact (raw_le_trans M hPA
    (rawNumeralValue M scope) (rawNumeralValue M rootScope) cutoff
    (rawLe_numerals_of_le M hPA scope rootScope hscope) hcutoff).
Qed.

(** For substitution, honest syntax of the arbitrary replacement first
    supplies its lift to [depth].  Since the quoted argument lies below that
    depth, the following opening is the identity.  Notice that no standardness
    assumption is made about the replacement or depth. *)
Lemma raw_codedFormulaSubstitutionAtom_standard_identity_from_root_scope :
  forall (M : RawPAModel), RawPASatisfies M -> forall
      rootScope replacement assignmentCode assignmentStep depth scope input,
  RawTermSyntaxRealizable M replacement assignmentCode assignmentStep ->
  StandardTermScoped scope input ->
  scope <= rootScope ->
  rawLe M (rawNumeralValue M rootScope) depth ->
  RawCodedFormulaSubstitutionAtom M replacement depth
    (rawQuotedTermCode M input) (rawQuotedTermCode M input).
Proof.
  intros M hPA rootScope replacement assignmentCode assignmentStep
    depth scope input hreplacement hscoped hscope hdepth.
  destruct (raw_codedTermShift_exists_of_syntax_realizable M hPA
    replacement assignmentCode assignmentStep hreplacement
    (raw_zero M) depth) as [liftedReplacement hlift].
  exists liftedReplacement. split.
  - exact hlift.
  - apply (raw_codedTermOpening_standard_identity_below
    M hPA scope depth liftedReplacement input hscoped).
    exact (raw_le_trans M hPA
      (rawNumeralValue M scope) (rawNumeralValue M rootScope) depth
      (rawLe_numerals_of_le M hPA scope rootScope hscope) hdepth).
Qed.

(** Applying a deeply closed ternary predicate to three quoted standard terms
    produces a formula deeply closed above any common root of their scopes.
    The three scopes remain independent: this is useful when the arguments
    occupy very different de Bruijn ranges, as in the native lower rows. *)
Theorem raw_standardTernaryApplication_deep_closed_from_root_scope : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      rootScope predicate
      firstScope firstInput secondScope secondInput thirdScope thirdInput
      output,
  RawCodedTernaryPredicateDeepClosed M predicate ->
  StandardTermScoped firstScope firstInput ->
  firstScope <= rootScope ->
  StandardTermScoped secondScope secondInput ->
  secondScope <= rootScope ->
  StandardTermScoped thirdScope thirdInput ->
  thirdScope <= rootScope ->
  RawCodedTernaryApplication M predicate
    (rawQuotedTermCode M firstInput)
    (rawQuotedTermCode M secondInput)
    (rawQuotedTermCode M thirdInput) output ->
  RawCodedFormulaAtomicallyAdequate M output ->
  RawCodedFormulaDeepClosedFrom M (rawNumeralValue M rootScope) output.
Proof.
  intros M hPA rootScope predicate
    firstScope firstInput secondScope secondInput thirdScope thirdInput
    output hpredicate
    hfirstScoped hfirstScope
    hsecondScoped hsecondScope
    hthirdScoped hthirdScope
    happlication hadequate.
  split; [exact hadequate |]. split.
  - intros cutoff amount hcutoff.
    assert (hfirst : RawCodedTermShift M cutoff amount
        (rawQuotedTermCode M firstInput)
        (rawQuotedTermCode M firstInput)).
    {
      exact (raw_codedTermShift_standard_identity_from_root_scope
        M hPA rootScope firstScope cutoff amount firstInput
        hfirstScoped hfirstScope hcutoff).
    }
    assert (hsecond : RawCodedTermShift M cutoff amount
        (rawQuotedTermCode M secondInput)
        (rawQuotedTermCode M secondInput)).
    {
      exact (raw_codedTermShift_standard_identity_from_root_scope
        M hPA rootScope secondScope cutoff amount secondInput
        hsecondScoped hsecondScope hcutoff).
    }
    assert (hthird : RawCodedTermShift M cutoff amount
        (rawQuotedTermCode M thirdInput)
        (rawQuotedTermCode M thirdInput)).
    {
      exact (raw_codedTermShift_standard_identity_from_root_scope
        M hPA rootScope thirdScope cutoff amount thirdInput
        hthirdScoped hthirdScope hcutoff).
    }
    destruct
      (raw_codedTernaryApplicationShiftInterchange_of_deepClosed
        M hPA predicate hpredicate
        cutoff amount
        (rawQuotedTermCode M firstInput)
        (rawQuotedTermCode M firstInput)
        (rawQuotedTermCode M secondInput)
        (rawQuotedTermCode M secondInput)
        (rawQuotedTermCode M thirdInput)
        (rawQuotedTermCode M thirdInput)
        output hfirst hsecond hthird happlication)
      as (target & htargetApplication & hshift).
    pose proof (raw_codedTernaryApplication_functional M hPA
      predicate
      (rawQuotedTermCode M firstInput)
      (rawQuotedTermCode M secondInput)
      (rawQuotedTermCode M thirdInput)
      target output htargetApplication happlication) as htarget.
    subst target. exact hshift.
  - intros replacement assignmentCode assignmentStep depth
      hreplacement hdepth.
    assert (hfirst : RawCodedFormulaSubstitutionAtom M replacement depth
        (rawQuotedTermCode M firstInput)
        (rawQuotedTermCode M firstInput)).
    {
      exact
        (raw_codedFormulaSubstitutionAtom_standard_identity_from_root_scope
          M hPA rootScope replacement assignmentCode assignmentStep depth
          firstScope firstInput hreplacement
          hfirstScoped hfirstScope hdepth).
    }
    assert (hsecond : RawCodedFormulaSubstitutionAtom M replacement depth
        (rawQuotedTermCode M secondInput)
        (rawQuotedTermCode M secondInput)).
    {
      exact
        (raw_codedFormulaSubstitutionAtom_standard_identity_from_root_scope
          M hPA rootScope replacement assignmentCode assignmentStep depth
          secondScope secondInput hreplacement
          hsecondScoped hsecondScope hdepth).
    }
    assert (hthird : RawCodedFormulaSubstitutionAtom M replacement depth
        (rawQuotedTermCode M thirdInput)
        (rawQuotedTermCode M thirdInput)).
    {
      exact
        (raw_codedFormulaSubstitutionAtom_standard_identity_from_root_scope
          M hPA rootScope replacement assignmentCode assignmentStep depth
          thirdScope thirdInput hreplacement
          hthirdScoped hthirdScope hdepth).
    }
    destruct
      (raw_codedTernaryApplicationOpeningInterchange_of_deepClosed_concrete
        M hPA predicate hpredicate
        replacement depth
        (rawQuotedTermCode M firstInput)
        (rawQuotedTermCode M firstInput)
        (rawQuotedTermCode M secondInput)
        (rawQuotedTermCode M secondInput)
        (rawQuotedTermCode M thirdInput)
        (rawQuotedTermCode M thirdInput)
        output hfirst hsecond hthird happlication)
      as (target & htargetApplication & hopening).
    pose proof (raw_codedTernaryApplication_functional M hPA
      predicate
      (rawQuotedTermCode M firstInput)
      (rawQuotedTermCode M secondInput)
      (rawQuotedTermCode M thirdInput)
      target output htargetApplication happlication) as htarget.
    subst target. exact hopening.
Qed.

(** Compatibility wrappers for the original fixed root.  Their proofs expose
    that twenty six is merely a client-chosen common upper scope. *)
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
  exact (raw_codedTermShift_standard_identity_from_root_scope
    M hPA 26 scope cutoff amount input hscoped hscope hcutoff).
Qed.

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
  exact
    (raw_codedFormulaSubstitutionAtom_standard_identity_from_root_scope
      M hPA 26 replacement assignmentCode assignmentStep depth scope input
      hreplacement hscoped hscope hdepth).
Qed.

(** The historical lower-row theorem is now just the instance for the three
    variables [#9], [#1], and [#0] below the displayed root twenty six. *)
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
  apply (raw_standardTernaryApplication_deep_closed_from_root_scope
    M hPA 26 predicate
    10 (tVar 9) 2 (tVar 1) 1 (tVar 0) output hpredicate).
  - intros index hfree. cbn in hfree. lia.
  - lia.
  - intros index hfree. cbn in hfree. lia.
  - lia.
  - intros index hfree. cbn in hfree. lia.
  - lia.
  - exact happlication.
  - exact hadequate.
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
