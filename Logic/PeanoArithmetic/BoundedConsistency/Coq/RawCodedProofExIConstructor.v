(**
  Coverage-certified existential introduction for model-coded PA proofs.

  The quantified body, witness, and instantiated premise can all be
  genuinely nonstandard codes.  Consequently the constructor accepts the
  represented single-substitution graph as data instead of attempting to
  decode either formula or term in the metatheory.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofUnaryCoverage.

Import ListNotations.

Module PABoundedRawCodedProofExIConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofUnaryCoverage.

Definition rawProofExIRoot (M : RawPAModel)
    (context body replacement child : M) : M :=
  rawListCode M
    [rawNumeralValue M 13; context; body; replacement; child].

Arguments rawProofExIRoot M context body replacement child
  : clear implicits.

Lemma raw_proofExIRoot_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child,
  rawLt M child (rawProofExIRoot M context body replacement child).
Proof.
  intros M hPA context body replacement child.
  unfold rawProofExIRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** Injectivity of the raw list code makes the leading constructor tag and
    all payload fields recoverable even in a nonstandard PA model. *)
Lemma raw_proofExIRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child tag payload,
  rawProofExIRoot M context body replacement child =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 13 /\ payload = [context; body; replacement; child].
Proof.
  intros M hPA context body replacement child tag payload hcode.
  unfold rawProofExIRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 13; context; body; replacement; child]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 13 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; body; replacement; child] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofExIRoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofExIRoot M context body replacement child =
    rawListCode M fields ->
  children = [child].
Proof.
  intros M hPA context body replacement child
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofExIRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofExI_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement child supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep child ->
  RawProofSyntaxStep M
    (rawProofExIRoot M context body replacement child)
    supportCode supportStep.
Proof.
  intros M hPA context body replacement child
    supportCode supportStep hchildSupported.
  split.
  - exists context, body, (raw_zero M), (raw_zero M), replacement,
      child, (raw_zero M), (raw_zero M).
    unfold RawProofConstructorCode, rawProofExIRoot.
    do 13 right. left. reflexivity.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofExIRoot M context body replacement child)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofExIRoot_recursive_children M hPA
        context body replacement child
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hchildSupported |].
        exact (raw_proofExIRoot_child_lt M hPA
          context body replacement child).
      * constructor.
Qed.

(** Unlike universal elimination, existential introduction fixes its root
    conclusion syntactically.  The supplied substitution graph instead
    identifies the formula that the single child must prove. *)
Lemma raw_proofExI_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement instance child,
  RawCodedFormulaSingleSubstitution M replacement body instance ->
  RawProofEndpoint M child context instance ->
  RawProofEndpointRuleComplete M
    (rawProofExIRoot M context body replacement child).
Proof.
  intros M hPA context body replacement instance child
    hsubstitution hchildEndpoint
    endpointContext endpointConclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end; try contradiction.
  all: destruct hcases as [hhead hrest].
  all: pose proof (raw_proofExIRoot_list_view M hPA
    context body replacement child _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext a t child1.
  subst endpointConclusion.
  exists context, body, instance,
    (raw_zero M), replacement, child, (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofExIRoot.
  do 13 right. left.
  repeat split; assumption || reflexivity.
Qed.

Lemma raw_proofExI_endpoint : forall
    (M : RawPAModel) context body replacement child,
  RawProofEndpoint M
    (rawProofExIRoot M context body replacement child)
    context (rawFormulaExCode M body).
Proof.
  intros M context body replacement child.
  exists context, body, (raw_zero M), (raw_zero M), replacement,
    child, (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofExIRoot.
  do 13 right. left. split; reflexivity.
Qed.

Theorem raw_proofExI_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context body replacement instance child,
  RawCodedFormulaSingleSubstitution M replacement body instance ->
  RawProofRuleCoverage M child ->
  RawProofEndpoint M child context instance ->
  RawProofRuleCoverage M
    (rawProofExIRoot M context body replacement child).
Proof.
  intros M hPA context body replacement instance child
    hsubstitution hchildCoverage hchildEndpoint.
  exact (raw_proofUnary_ruleCoverage M hPA child
    (rawProofExIRoot M context body replacement child)
    hchildCoverage
    (raw_proofExIRoot_child_lt M hPA
      context body replacement child)
    (raw_proofExI_syntax_step M hPA
      context body replacement child)
    (raw_proofExI_endpoint_rule_complete M hPA
      context body replacement instance child
      hsubstitution hchildEndpoint)).
Qed.

End PABoundedRawCodedProofExIConstructor.
