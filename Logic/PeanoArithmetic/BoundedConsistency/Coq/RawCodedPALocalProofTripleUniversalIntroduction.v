(**
  Three represented universal introductions in one coded context.

  Several native field compilers close a body over the same three variables.
  The raw natural-deduction rule shifts the proof context at each [All-I]
  node, so one self-shift witness for the literal context is the complete
  reusable hypothesis.  Factoring the construction here avoids rebuilding
  the same coverage/endpoint argument in every field-specific module.
*)

From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedContextShift
  RawCodedProofEndpoints
  RawCodedProofRuleCoverage
  RawCodedProofAllIConstructor
  RawCodedPALocalProofExistential.

Module PABoundedRawCodedPALocalProofTripleUniversalIntroduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedContextShift.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedProofAllIConstructor.
Import PABoundedRawCodedPALocalProofExistential.

Definition rawPALocalProofClose3Root
    (M : RawPAModel) (context body child : M) : M :=
  rawProofAllIRoot M context
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M context
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M context body child)).

Arguments rawPALocalProofClose3Root M context body child : clear implicits.

(** Three universal introductions across their actual successive contexts.
    This is strictly more general than the historical self-shift root: a
    temporary template prefix is renamed at every binder and therefore
    naturally yields four different represented context codes. *)
Definition rawPALocalProofClose3BetweenRoot
    (M : RawPAModel) (context0 context1 context2 body child : M) : M :=
  rawProofAllIRoot M context0
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M context1
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M context2 body child)).

Arguments rawPALocalProofClose3BetweenRoot
  M context0 context1 context2 body child : clear implicits.

Theorem raw_codedPALocalProofOf_close3_between : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context0 context1 context2 context3 body child,
  RawContextShift M context0 context1 ->
  RawContextShift M context1 context2 ->
  RawContextShift M context2 context3 ->
  RawCodedPALocalProofOf M context3 body child ->
  RawCodedPALocalProofOf M context0
    (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M body)))
    (rawPALocalProofClose3BetweenRoot M
      context0 context1 context2 body child).
Proof.
  intros M hPA context0 context1 context2 context3 body child
    hshift01 hshift12 hshift23 [hcoverage hendpoint].
  pose proof (raw_proofAllI_ruleCoverage M hPA
    context2 context3 body child hshift23 hcoverage hendpoint)
    as hcoverage1.
  pose proof (raw_proofAllI_endpoint M context2 body child)
    as hendpoint1.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    context1 context2 (rawFormulaAllCode M body)
    (rawProofAllIRoot M context2 body child)
    hshift12 hcoverage1 hendpoint1) as hcoverage2.
  pose proof (raw_proofAllI_endpoint M context1
    (rawFormulaAllCode M body)
    (rawProofAllIRoot M context2 body child)) as hendpoint2.
  pose proof (raw_proofAllI_ruleCoverage M hPA
    context0 context1
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M context1
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M context2 body child))
    hshift01 hcoverage2 hendpoint2) as hcoverage3.
  pose proof (raw_proofAllI_endpoint M context0
    (rawFormulaAllCode M (rawFormulaAllCode M body))
    (rawProofAllIRoot M context1
      (rawFormulaAllCode M body)
      (rawProofAllIRoot M context2 body child))) as hendpoint3.
  split; assumption.
Qed.

Theorem raw_codedPALocalProofOf_close3_on : forall
    (M : RawPAModel), RawPASatisfies M -> forall context body child,
  RawContextShift M context context ->
  RawCodedPALocalProofOf M context body child ->
  RawCodedPALocalProofOf M context
    (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M body)))
    (rawPALocalProofClose3Root M context body child).
Proof.
  intros M hPA context body child hshift hchild.
  change (RawCodedPALocalProofOf M context
    (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M body)))
    (rawPALocalProofClose3BetweenRoot M
      context context context body child)).
  exact (raw_codedPALocalProofOf_close3_between M hPA
    context context context context body child
    hshift hshift hshift hchild).
Qed.

Corollary raw_codedPALocalProofOf_close3_empty : forall
    (M : RawPAModel), RawPASatisfies M -> forall body child,
  RawCodedPALocalProofOf M (raw_zero M) body child ->
  RawCodedPALocalProofOf M (raw_zero M)
    (rawFormulaAllCode M
      (rawFormulaAllCode M (rawFormulaAllCode M body)))
    (rawPALocalProofClose3Root M (raw_zero M) body child).
Proof.
  intros M hPA body child hchild.
  exact (raw_codedPALocalProofOf_close3_on M hPA
    (raw_zero M) body child (raw_contextShift_empty M hPA) hchild).
Qed.

End PABoundedRawCodedPALocalProofTripleUniversalIntroduction.
