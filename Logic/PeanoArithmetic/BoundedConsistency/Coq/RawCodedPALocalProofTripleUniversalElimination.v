(**
  Three successive universal eliminations in one carrier-coded context.

  The dynamic local field stores both of its public laws under exactly three
  universal binders: formula code, assignment-code table, and assignment-step
  table.  Consumers must instantiate those binders without decoding any of
  the intervening carrier formula codes and without changing the witnessed
  PA context.

  This module packages that purely proof-theoretic operation.  The caller
  supplies the three represented single-substitution traces, including the
  two facts that the first two results still have an outer universal
  constructor.  Three checked [All-E] nodes then produce the final instance.
  Companion theorems first project either side of a conjunction, which is the
  exact shape needed for the decision/exclusivity bundle.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedFormulaOperations
  RawCodedProofAllEConstructor
  RawCodedProofAndEConstructors
  RawCodedPALocalProofExistential
  RawCodedPALocalProofConjunction
  RawCodedPALocalProofUniversalElimination.

Module PABoundedRawCodedPALocalProofTripleUniversalElimination.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofAllEConstructor.
Import PABoundedRawCodedProofAndEConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedPALocalProofConjunction.
Import PABoundedRawCodedPALocalProofUniversalElimination.

(** The literal proof root obtained by eliminating three nested binders.
    Naming it keeps later constructor calculations transparent. *)
Definition rawProofTripleAllERoot (M : RawPAModel)
    (context outerBody middleBody innerBody
      firstReplacement secondReplacement thirdReplacement child : M) : M :=
  rawProofAllERoot M context innerBody thirdReplacement
    (rawProofAllERoot M context middleBody secondReplacement
      (rawProofAllERoot M context outerBody firstReplacement child)).

Arguments rawProofTripleAllERoot
  M context outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement child
  : clear implicits.

(** Eliminate three universal binders while retaining [context] literally.

    The first substitution targets [All middleBody], and the second targets
    [All innerBody].  Recording those constructor equalities in the premises
    prevents an arbitrary substitution output from being treated as another
    universal formula. *)
Theorem raw_codedPALocalProofOf_tripleAllE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context outerBody middleBody innerBody
      firstReplacement secondReplacement thirdReplacement conclusion child,
  RawCodedPALocalProofOf M context
    (rawFormulaAllCode M outerBody) child ->
  RawCodedFormulaSingleSubstitution M firstReplacement outerBody
    (rawFormulaAllCode M middleBody) ->
  RawCodedFormulaSingleSubstitution M secondReplacement middleBody
    (rawFormulaAllCode M innerBody) ->
  RawCodedFormulaSingleSubstitution M thirdReplacement innerBody conclusion ->
  RawCodedPALocalProofOf M context conclusion
    (rawProofTripleAllERoot M context outerBody middleBody innerBody
      firstReplacement secondReplacement thirdReplacement child).
Proof.
  intros M hPA context outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement conclusion child
    hchild hfirst hsecond hthird.
  unfold rawProofTripleAllERoot.
  pose proof (raw_codedPALocalProofOf_allE M hPA
    context outerBody firstReplacement
    (rawFormulaAllCode M middleBody) child hchild hfirst) as hafterFirst.
  pose proof (raw_codedPALocalProofOf_allE M hPA
    context middleBody secondReplacement
    (rawFormulaAllCode M innerBody)
    (rawProofAllERoot M context outerBody firstReplacement child)
    hafterFirst hsecond) as hafterSecond.
  exact (raw_codedPALocalProofOf_allE M hPA
    context innerBody thirdReplacement conclusion
    (rawProofAllERoot M context middleBody secondReplacement
      (rawProofAllERoot M context outerBody firstReplacement child))
    hafterSecond hthird).
Qed.

(** Project the left conjunct and instantiate its three binders. *)
Theorem raw_codedPALocalProofOf_andE1_tripleAllE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context outerBody middleBody innerBody right
      firstReplacement secondReplacement thirdReplacement conclusion child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M (rawFormulaAllCode M outerBody) right) child ->
  RawCodedFormulaSingleSubstitution M firstReplacement outerBody
    (rawFormulaAllCode M middleBody) ->
  RawCodedFormulaSingleSubstitution M secondReplacement middleBody
    (rawFormulaAllCode M innerBody) ->
  RawCodedFormulaSingleSubstitution M thirdReplacement innerBody conclusion ->
  exists projectedRoot,
    RawCodedPALocalProofOf M context conclusion projectedRoot.
Proof.
  intros M hPA context outerBody middleBody innerBody right
    firstReplacement secondReplacement thirdReplacement conclusion child
    hchild hfirst hsecond hthird.
  pose proof (raw_codedPALocalProofOf_andE1 M hPA context
    (rawFormulaAllCode M outerBody) right child hchild) as hprojected.
  exists (rawProofTripleAllERoot M context outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement
    (rawProofAndERoot M RawAndLeft context
      (rawFormulaAllCode M outerBody) right child)).
  exact (raw_codedPALocalProofOf_tripleAllE M hPA
    context outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement conclusion
    (rawProofAndERoot M RawAndLeft context
      (rawFormulaAllCode M outerBody) right child)
    hprojected hfirst hsecond hthird).
Qed.

(** Project the right conjunct and instantiate its three binders. *)
Theorem raw_codedPALocalProofOf_andE2_tripleAllE : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context left outerBody middleBody innerBody
      firstReplacement secondReplacement thirdReplacement conclusion child,
  RawCodedPALocalProofOf M context
    (rawFormulaAndCode M left (rawFormulaAllCode M outerBody)) child ->
  RawCodedFormulaSingleSubstitution M firstReplacement outerBody
    (rawFormulaAllCode M middleBody) ->
  RawCodedFormulaSingleSubstitution M secondReplacement middleBody
    (rawFormulaAllCode M innerBody) ->
  RawCodedFormulaSingleSubstitution M thirdReplacement innerBody conclusion ->
  exists projectedRoot,
    RawCodedPALocalProofOf M context conclusion projectedRoot.
Proof.
  intros M hPA context left outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement conclusion child
    hchild hfirst hsecond hthird.
  pose proof (raw_codedPALocalProofOf_andE2 M hPA context
    left (rawFormulaAllCode M outerBody) child hchild) as hprojected.
  exists (rawProofTripleAllERoot M context outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement
    (rawProofAndERoot M RawAndRight context
      left (rawFormulaAllCode M outerBody) child)).
  exact (raw_codedPALocalProofOf_tripleAllE M hPA
    context outerBody middleBody innerBody
    firstReplacement secondReplacement thirdReplacement conclusion
    (rawProofAndERoot M RawAndRight context
      left (rawFormulaAllCode M outerBody) child)
    hprojected hfirst hsecond hthird).
Qed.

End PABoundedRawCodedPALocalProofTripleUniversalElimination.
