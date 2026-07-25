(**
  Coverage-certified equality elimination for model-coded PA proofs.

  The tag-16 constructor stores two term codes ([source] and [target]), a
  formula-schema code ([body]), and the two recursive proofs.  It does not
  store either substituted instance.  Those instances therefore remain
  explicit witnesses of the represented single-substitution graph:

    - the equality child proves [source = target];
    - the body child proves [body[source]]; and
    - the parent concludes [body[target]].

  This formulation is valid for genuinely nonstandard term and formula
  codes.  In particular, it never decodes a carrier element into a
  metatheoretic syntax tree.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofBinaryCoverage.

Import ListNotations.

Module PABoundedRawCodedProofEqElimConstructor.

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
Import PABoundedRawCodedProofBinaryCoverage.

Definition rawProofEqElimRoot (M : RawPAModel)
    (context source target body equalityChild bodyChild : M) : M :=
  rawListCode M
    [rawNumeralValue M 16; context; source; target; body;
      equalityChild; bodyChild].

Arguments rawProofEqElimRoot
  M context source target body equalityChild bodyChild : clear implicits.

Lemma raw_proofEqElimRoot_equality_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body equalityChild bodyChild,
  rawLt M equalityChild
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild).
Proof.
  intros M hPA context source target body equalityChild bodyChild.
  unfold rawProofEqElimRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

Lemma raw_proofEqElimRoot_body_child_lt : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body equalityChild bodyChild,
  rawLt M bodyChild
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild).
Proof.
  intros M hPA context source target body equalityChild bodyChild.
  unfold rawProofEqElimRoot.
  apply rawProofListCode_member_lt; [exact hPA |].
  cbn. tauto.
Qed.

(** List-code injectivity recovers the tag and all six payload fields from
    any constructor-shaped view of the root.  This is the key fact excluding
    every other rule row in a nonstandard PA model. *)
Lemma raw_proofEqElimRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body equalityChild bodyChild tag payload,
  rawProofEqElimRoot M context source target body
      equalityChild bodyChild =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 16 /\
  payload = [context; source; target; body; equalityChild; bodyChild].
Proof.
  intros M hPA context source target body equalityChild bodyChild
    tag payload hcode.
  unfold rawProofEqElimRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 16; context; source; target; body;
      equalityChild; bodyChild]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 16 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail :
      [context; source; target; body; equalityChild; bodyChild] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

Lemma raw_proofEqElimRoot_recursive_children : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body equalityChild bodyChild
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofEqElimRoot M context source target body
      equalityChild bodyChild = rawListCode M fields ->
  children = [equalityChild; bodyChild].
Proof.
  intros M hPA context source target body equalityChild bodyChild
    rowContext a b c t child1 child2 child3 fields children
    hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofEqElimRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields.
  all: try discriminate hfields.
  all: inversion hfields; reflexivity.
Qed.

Lemma raw_proofEqElimRoot_constructor : forall
    (M : RawPAModel) context source target body equalityChild bodyChild,
  RawProofConstructorCode M
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild)
    context source target body (raw_zero M)
    equalityChild bodyChild (raw_zero M).
Proof.
  intros M context source target body equalityChild bodyChild.
  unfold RawProofConstructorCode, rawProofEqElimRoot.
  do 16 right. reflexivity.
Qed.

Lemma raw_proofEqElim_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body equalityChild bodyChild
      supportCode supportStep,
  rawProofCodeSupported M supportCode supportStep equalityChild ->
  rawProofCodeSupported M supportCode supportStep bodyChild ->
  RawProofSyntaxStep M
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild)
    supportCode supportStep.
Proof.
  intros M hPA context source target body equalityChild bodyChild
    supportCode supportStep hequalitySupported hbodySupported.
  split.
  - exists context, source, target, body, (raw_zero M),
      equalityChild, bodyChild, (raw_zero M).
    apply raw_proofEqElimRoot_constructor.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofEqElimRoot M context source target body
          equalityChild bodyChild)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode.
      pose proof (raw_proofEqElimRoot_recursive_children M hPA
        context source target body equalityChild bodyChild
        rowContext a b c t child1 child2 child3 fields children
        hentry hcode) as ->.
      constructor.
      * split; [exact hequalitySupported |].
        exact (raw_proofEqElimRoot_equality_child_lt M hPA
          context source target body equalityChild bodyChild).
      * constructor.
        -- split; [exact hbodySupported |].
           exact (raw_proofEqElimRoot_body_child_lt M hPA
             context source target body equalityChild bodyChild).
        -- constructor.
Qed.

(** The target instance is supplied by the endpoint view itself.  Thus rule
    completeness needs only the source-instance substitution graph and the
    two child endpoints; it does not assume substitution functionality. *)
Lemma raw_proofEqElim_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body sourceInstance equalityChild bodyChild,
  RawProofEndpoint M equalityChild context
    (rawFormulaEqCode M source target) ->
  RawCodedFormulaSingleSubstitution M source body sourceInstance ->
  RawProofEndpoint M bodyChild context sourceInstance ->
  RawProofEndpointRuleComplete M
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild).
Proof.
  intros M hPA context source target body sourceInstance
    equalityChild bodyChild hequalityEndpoint hsourceSubstitution
    hbodyEndpoint endpointContext endpointConclusion hendpoint.
  destruct hendpoint as
    (rowContext & a & b & c & t & child1 & child2 & child3 &
      hcontext & hcases).
  subst rowContext.
  unfold RawProofEndpointCases in hcases.
  repeat match type of hcases with
  | _ \/ _ => destruct hcases as [hcases | hcases]
  end; try contradiction.
  all: destruct hcases as [hhead hrest].
  all: pose proof (raw_proofEqElimRoot_list_view M hPA
    context source target body equalityChild bodyChild
    _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload;
    subst endpointContext a b c child1 child2.
  exists context, source, target, body,
    (rawFormulaEqCode M source target),
    equalityChild, bodyChild, sourceInstance.
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofEqElimRoot.
  do 16 right.
  repeat split; assumption || reflexivity.
Qed.

(** An exact endpoint is available once the represented substitution graph
    supplies the target instance. *)
Lemma raw_proofEqElim_endpoint : forall
    (M : RawPAModel) context source target body targetInstance
      equalityChild bodyChild,
  RawCodedFormulaSingleSubstitution M target body targetInstance ->
  RawProofEndpoint M
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild)
    context targetInstance.
Proof.
  intros M context source target body targetInstance
    equalityChild bodyChild htargetSubstitution.
  exists context, source, target, body, (raw_zero M),
    equalityChild, bodyChild, (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofEqElimRoot.
  do 16 right.
  split; [reflexivity | exact htargetSubstitution].
Qed.

(** Merge the two child support tables and install the exact tag-16 root.
    The target substitution does not appear here: coverage validates every
    endpoint exposed by the root, while [raw_proofEqElim_endpoint] selects a
    particular target instance when a caller needs one. *)
Theorem raw_proofEqElim_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context source target body sourceInstance equalityChild bodyChild,
  RawProofRuleCoverage M equalityChild ->
  RawProofEndpoint M equalityChild context
    (rawFormulaEqCode M source target) ->
  RawCodedFormulaSingleSubstitution M source body sourceInstance ->
  RawProofRuleCoverage M bodyChild ->
  RawProofEndpoint M bodyChild context sourceInstance ->
  RawProofRuleCoverage M
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild).
Proof.
  intros M hPA context source target body sourceInstance
    equalityChild bodyChild hequalityCoverage hequalityEndpoint
    hsourceSubstitution hbodyCoverage hbodyEndpoint.
  exact (raw_proofBinary_ruleCoverage M hPA
    equalityChild bodyChild
    (rawProofEqElimRoot M context source target body
      equalityChild bodyChild)
    hequalityCoverage hbodyCoverage
    (raw_proofEqElimRoot_equality_child_lt M hPA
      context source target body equalityChild bodyChild)
    (raw_proofEqElimRoot_body_child_lt M hPA
      context source target body equalityChild bodyChild)
    (raw_proofEqElim_syntax_step M hPA
      context source target body equalityChild bodyChild)
    (raw_proofEqElim_endpoint_rule_complete M hPA
      context source target body sourceInstance equalityChild bodyChild
      hequalityEndpoint hsourceSubstitution hbodyEndpoint)).
Qed.

End PABoundedRawCodedProofEqElimConstructor.
