(**
  Coverage-certified disjunction-introduction constructors.

  The two introduction rules have the same encoded payload and conclusion;
  they differ only in whether the recursive child proves the left or the
  right disjunct.  [RawOrInjection] records that choice once, allowing the
  descent, traversal, and support-extension arguments to be shared.

  As for the other raw unary constructors, list-code injectivity is essential
  in a nonstandard model.  It rules out an alternative constructor view of
  the parent and pins every recursive view to the supplied child.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofUnaryCoverage.

Import ListNotations.

Module PABoundedRawCodedProofOrIConstructors.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofUnaryCoverage.

Inductive RawOrInjection : Type :=
| RawOrLeft
| RawOrRight.

Definition rawOrInjectionTag (injection : RawOrInjection) : nat :=
  match injection with
  | RawOrLeft => 8
  | RawOrRight => 9
  end.

Definition rawOrInjectionPremise (M : RawPAModel)
    (injection : RawOrInjection) (left right : M) : M :=
  match injection with
  | RawOrLeft => left
  | RawOrRight => right
  end.

Definition rawProofOrIRoot (M : RawPAModel)
    (injection : RawOrInjection)
    (context left right child : M) : M :=
  rawListCode M
    [rawNumeralValue M (rawOrInjectionTag injection);
      context; left; right; child].

Arguments rawOrInjectionPremise M injection left right : clear implicits.
Arguments rawProofOrIRoot M injection context left right child
  : clear implicits.

Lemma raw_proofOrIRoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child,
  rawLt M child
    (rawProofOrIRoot M injection context left right child).
Proof.
  intros M hPA injection context left right child.
  unfold rawProofOrIRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** Any constructor-shaped view of the parent recovers both its side tag and
    all four payload fields.  This single fact excludes the other sixteen
    endpoint and constructor rows below. *)
Lemma raw_proofOrIRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child tag payload,
  rawProofOrIRoot M injection context left right child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = rawOrInjectionTag injection /\
  payload = [context; left; right; child].
Proof.
  intros M hPA injection context left right child tag payload hcode.
  unfold rawProofOrIRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M (rawOrInjectionTag injection);
      context; left; right; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead :
      rawNumeralValue M (rawOrInjectionTag injection) =
      rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; left; right; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

(** Both disjunction-introduction rows are unary.  Constructor-tag
    injectivity shows that the child exposed by any matching recursive row
    is exactly the advertised child. *)
Lemma raw_proofOrIRoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofOrIRoot M injection context left right child =
    rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA injection context left right child
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofOrIRoot in hcode.
  all: destruct injection.
  all: cbn [rawOrInjectionTag] in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofOrIRoot_constructor : forall
    (M : RawPAModel) injection context left right child,
  RawProofConstructorCode M
    (rawProofOrIRoot M injection context left right child)
    context left right (raw_zero M) (raw_zero M)
    child (raw_zero M) (raw_zero M).
Proof.
  intros M [|] context left right child;
    unfold RawProofConstructorCode, rawProofOrIRoot,
      rawOrInjectionTag.
  - do 8 right. left. reflexivity.
  - do 9 right. left. reflexivity.
Qed.

Lemma raw_proofOrI_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofOrIRoot M injection context left right child)
    supportCode supportStep.
Proof.
  intros M hPA injection context left right child
    supportCode supportStep hchildSupported.
  split.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    apply raw_proofOrIRoot_constructor.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofOrIRoot M injection context left right child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofOrIRoot_recursive_children M hPA
        injection context left right child
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofOrIRoot_child_lt M hPA
          injection context left right child).
      * constructor.
Qed.

(** Every endpoint view of the parent collapses to its chosen introduction
    row.  Once the payload is fixed, the child endpoint is precisely the
    only local-rule premise. *)
Lemma raw_proofOrI_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child,
  RawProofEndpoint M child context
    (rawOrInjectionPremise M injection left right) ->
  RawProofEndpointRuleComplete M
    (rawProofOrIRoot M injection context left right child).
Proof.
  intros M hPA injection context left right child hchildEndpoint
    endpointContext endpointConclusion hendpoint.
  destruct injection.
  - destruct hendpoint as
      (rowContext & a & b & c & t & child1 & child2 & child3 &
        hcontext & hcases).
    subst rowContext.
    unfold RawProofEndpointCases in hcases.
    repeat match type of hcases with
    | _ \/ _ => destruct hcases as [hcases | hcases]
    end; try contradiction.
    all: destruct hcases as [hhead hrest].
    all: pose proof (raw_proofOrIRoot_list_view M hPA
      RawOrLeft context left right child _ _ hhead) as hview.
    all: destruct hview as [htag hpayload].
    all: cbn [rawOrInjectionTag] in htag.
    all: try discriminate htag.
    inversion hpayload; subst endpointContext a b child1.
    subst endpointConclusion.
    exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofRuleValidCases, rawProofOrIRoot,
      rawOrInjectionTag, rawOrInjectionPremise in *.
    do 8 right. left.
    repeat split; assumption || reflexivity.
  - destruct hendpoint as
      (rowContext & a & b & c & t & child1 & child2 & child3 &
        hcontext & hcases).
    subst rowContext.
    unfold RawProofEndpointCases in hcases.
    repeat match type of hcases with
    | _ \/ _ => destruct hcases as [hcases | hcases]
    end; try contradiction.
    all: destruct hcases as [hhead hrest].
    all: pose proof (raw_proofOrIRoot_list_view M hPA
      RawOrRight context left right child _ _ hhead) as hview.
    all: destruct hview as [htag hpayload].
    all: cbn [rawOrInjectionTag] in htag.
    all: try discriminate htag.
    inversion hpayload; subst endpointContext a b child1.
    subst endpointConclusion.
    exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofRuleValidCases, rawProofOrIRoot,
      rawOrInjectionTag, rawOrInjectionPremise in *.
    do 9 right. left.
    repeat split; assumption || reflexivity.
Qed.

Corollary raw_proofOrI_endpoint : forall
    (M : RawPAModel) injection context left right child,
  RawProofEndpoint M
    (rawProofOrIRoot M injection context left right child)
    context (rawFormulaOrCode M left right).
Proof.
  intros M [|] context left right child.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofEndpointCases, rawProofOrIRoot,
      rawOrInjectionTag.
    do 8 right. left. split; reflexivity.
  - exists context, left, right,
      (raw_zero M), (raw_zero M), child,
      (raw_zero M), (raw_zero M).
    split; [reflexivity |].
    unfold RawProofEndpointCases, rawProofOrIRoot,
      rawOrInjectionTag.
    do 9 right. left. split; reflexivity.
Qed.

(** Extend the child's exact support table by the chosen disjunction parent.
    The generic unary extension theorem preserves every old syntax/rule row
    and installs exactly the new root row. *)
Theorem raw_proofOrI_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      injection context left right child,
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context
    (rawOrInjectionPremise M injection left right) ->
  RawProofRuleCoverage M
    (rawProofOrIRoot M injection context left right child).
Proof.
  intros M hPA injection context left right child
    hchildCoverage hchildEndpoint.
  exact (raw_proofUnary_ruleCoverage M hPA child
    (rawProofOrIRoot M injection context left right child)
    hchildCoverage
    (raw_proofOrIRoot_child_lt M hPA
      injection context left right child)
    (raw_proofOrI_syntax_step M hPA
      injection context left right child)
    (raw_proofOrI_endpoint_rule_complete M hPA
      injection context left right child hchildEndpoint)).
Qed.

End PABoundedRawCodedProofOrIConstructors.
