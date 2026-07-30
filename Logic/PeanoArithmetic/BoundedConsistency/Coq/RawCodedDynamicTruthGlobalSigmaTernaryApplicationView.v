(**
  Normalize application of a graph-selected global Sigma predicate.

  A paired dynamic-truth successor first constructs two local row codes and
  then wraps them in the ten-witness global traversal formula.  Clients of
  the direct soundness compiler, however, see only a dependent ternary
  application selector for the resulting global Sigma code.  This module
  joins those two views without decoding any carrier element.

  The main equivalence retains the actual local row witnesses, the two
  wrapper equations, and the represented five-operation application trace.
  Its expanded form additionally exposes the numeral, domain, and lower-Pi
  application from which the local Sigma row was assembled.  These are the
  concrete ingredients needed to append the Or row in the eventual
  proof-producing truth-law compiler.
*)

From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import Representability.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedFormulaOperations
  RawCodedNumeralTermCode
  RawCodedTemplateTernaryApplication
  RawCodedTemplateTernaryApplicationFunctionality
  RawCodedDynamicTruthSigmaSuccessorRowGraph
  RawCodedDynamicTruthPiSuccessorRowGraph
  RawCodedDynamicTruthPairedSuccessorRowGraph
  RawCodedDynamicTruthPairedGlobalSuccessorGraph.

Module PABoundedRawCodedDynamicTruthGlobalSigmaTernaryApplicationView.

Import PA.
Import PAListRepresentability.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedTemplateTernaryApplication.
Import PABoundedRawCodedTemplateTernaryApplicationFunctionality.
Import PABoundedRawCodedDynamicTruthSigmaSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPiSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedSuccessorRowGraph.
Import PABoundedRawCodedDynamicTruthPairedGlobalSuccessorGraph.

(** The structured relational view.  The application predicate is written
    as the transparent global-wrapper polynomial rather than the opaque
    public [nextSigma] name.  The wrapper equation below proves that these
    are the same carrier code. *)
Definition RawDynamicTruthGlobalSigmaTernaryApplicationViewAt
    (M : RawPAModel)
    (previousSigma previousPi lowerLevel nextSigma nextPi
      first second third output : M) : Prop :=
  exists localSigma localPi : M,
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigma previousPi lowerLevel localSigma localPi /\
    nextSigma = rawDynamicTruthGlobalFormulaCode M
      tZero localSigma localPi /\
    nextPi = rawDynamicTruthGlobalFormulaCode M
      (Term.numeral 1) localSigma localPi /\
    RawCodedTernaryApplication M
      (rawDynamicTruthGlobalFormulaCode M tZero localSigma localPi)
      first second third output.

Arguments RawDynamicTruthGlobalSigmaTernaryApplicationViewAt
  M previousSigma previousPi lowerLevel nextSigma nextPi
    first second third output : clear implicits.

(** A successor edge and an application of its public Sigma coordinate are
    exactly the structured view above.  This bidirectional statement is the
    preferred normalization interface: later clients need not destruct the
    paired wrapper and separately rewrite a dependent application trace. *)
Theorem raw_dynamicTruthGlobalSigmaTernaryApplication_view_iff : forall
    (M : RawPAModel) previousSigma previousPi lowerLevel nextSigma nextPi
      first second third output,
  (RawDynamicTruthPairedGlobalSuccessorAt M
      previousSigma previousPi lowerLevel nextSigma nextPi /\
   RawCodedTernaryApplication M nextSigma
      first second third output) <->
  RawDynamicTruthGlobalSigmaTernaryApplicationViewAt M
    previousSigma previousPi lowerLevel nextSigma nextPi
    first second third output.
Proof.
  intros M previousSigma previousPi lowerLevel nextSigma nextPi
    first second third output.
  unfold RawDynamicTruthGlobalSigmaTernaryApplicationViewAt,
    RawDynamicTruthPairedGlobalSuccessorAt,
    RawDynamicTruthPairedGlobalWrapperAt.
  split.
  - intros [[localSigma [localPi [hrows [hnextSigma hnextPi]]]]
    happlication].
    exists localSigma, localPi.
    split; [exact hrows |].
    split; [exact hnextSigma |].
    split; [exact hnextPi |].
    rewrite hnextSigma in happlication.
    exact happlication.
  - intros [localSigma [localPi
      [hrows [hnextSigma [hnextPi happlication]]]]].
    split.
    + exists localSigma, localPi. split; [exact hrows |].
      split; assumption.
    + rewrite hnextSigma.
      exact happlication.
Qed.

(** Every honest selector supplies the application half of the equivalence.
    The result preserves the local rows chosen by the *same* successor edge;
    it does not select or recompute an unrelated global predicate. *)
Corollary raw_dynamicTruthGlobalSigmaTernaryApplication_selector_view :
  forall (M : RawPAModel)
    previousSigma previousPi lowerLevel nextSigma nextPi
    (selector : RawCodedTernaryApplicationSelector M nextSigma)
    first second third,
  RawDynamicTruthPairedGlobalSuccessorAt M
    previousSigma previousPi lowerLevel nextSigma nextPi ->
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  RawDynamicTruthGlobalSigmaTernaryApplicationViewAt M
    previousSigma previousPi lowerLevel nextSigma nextPi
    first second third
    (rawTernaryApplicationOutput selector first second third).
Proof.
  intros M previousSigma previousPi lowerLevel nextSigma nextPi
    selector first second third hsuccessor hfirst hsecond hthird.
  apply (proj1
    (raw_dynamicTruthGlobalSigmaTernaryApplication_view_iff M
      previousSigma previousPi lowerLevel nextSigma nextPi
      first second third
      (rawTernaryApplicationOutput selector first second third))).
  split; [exact hsuccessor |].
  exact (rawTernaryApplicationOutput_trace selector
    first second third hfirst hsecond hthird).
Qed.

(** Expand the local Sigma coordinate all the way to the native row-code
    polynomial.  In particular, [lowerApplication] is an application of the
    preceding global Pi predicate and [domain] is the represented successor
    rank domain selected at the same possibly nonstandard [lowerLevel]. *)
Theorem
    raw_dynamicTruthGlobalSigmaTernaryApplication_view_exposes_sigma_row :
  forall (M : RawPAModel)
    previousSigma previousPi lowerLevel nextSigma nextPi
    first second third output,
  RawDynamicTruthGlobalSigmaTernaryApplicationViewAt M
    previousSigma previousPi lowerLevel nextSigma nextPi
    first second third output ->
  exists localSigma localPi upperNumeral domain lowerApplication : M,
    RawNumeralTermCodeAt M (raw_succ M lowerLevel) upperNumeral /\
    RawCodedFormulaSingleSubstitution M upperNumeral
      (rawNumeralValue M dynamicTruthSigmaRowDomainTemplateCode) domain /\
    RawDynamicTruthCoqLowerApplication M
      previousPi lowerApplication /\
    localSigma = rawDynamicTruthSigmaSuccessorRowCode M
      domain lowerApplication /\
    RawDynamicTruthPiSuccessorRowAt M
      previousSigma lowerLevel localPi /\
    nextSigma = rawDynamicTruthGlobalFormulaCode M
      tZero localSigma localPi /\
    nextPi = rawDynamicTruthGlobalFormulaCode M
      (Term.numeral 1) localSigma localPi /\
    RawCodedTernaryApplication M
      (rawDynamicTruthGlobalFormulaCode M tZero localSigma localPi)
      first second third output.
Proof.
  intros M previousSigma previousPi lowerLevel nextSigma nextPi
    first second third output
    [localSigma [localPi
      [[hsigmaRow hpiRow]
       [hnextSigma [hnextPi happlication]]]]].
  destruct hsigmaRow as
    (upperNumeral & domain & lowerApplication &
     hnumeral & hdomain & hlower & hlocalSigma).
  exists localSigma, localPi, upperNumeral, domain, lowerApplication.
  repeat split; assumption.
Qed.

(** If a later syntactic construction presents any application trace for
    the normalized wrapper code, functionality identifies its endpoint with
    the dependent selector output.  This packages the otherwise repeated
    rewrite through [nextSigma] followed by five-trace functionality. *)
Corollary raw_dynamicTruthGlobalSigmaTernaryApplication_selector_unique :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    previousSigma previousPi lowerLevel nextSigma
    (selector : RawCodedTernaryApplicationSelector M nextSigma)
    first second third candidate,
  RawCodedTermSyntax M first ->
  RawCodedTermSyntax M second ->
  RawCodedTermSyntax M third ->
  (exists localSigma localPi : M,
    RawDynamicTruthPairedSuccessorRowAt M
      previousSigma previousPi lowerLevel localSigma localPi /\
    nextSigma = rawDynamicTruthGlobalFormulaCode M
      tZero localSigma localPi /\
    RawCodedTernaryApplication M
      (rawDynamicTruthGlobalFormulaCode M tZero localSigma localPi)
      first second third candidate) ->
  rawTernaryApplicationOutput selector first second third = candidate.
Proof.
  intros M hPA previousSigma previousPi lowerLevel nextSigma
    selector first second third candidate hfirst hsecond hthird
    [localSigma [localPi [_hrows [hnextSigma hcand]]]].
  apply (rawTernaryApplicationOutput_unique M hPA
    nextSigma selector first second third candidate
    hfirst hsecond hthird).
  rewrite hnextSigma.
  exact hcand.
Qed.

End PABoundedRawCodedDynamicTruthGlobalSigmaTernaryApplicationView.
