(**
  Coverage-certified equality-reflexivity leaves for model-coded PA proofs.

  Equality reflexivity is constructor tag [15].  Its witness is kept as an
  arbitrary carrier element: this constructor layer records the exact raw
  proof-code arithmetic and the local rule endpoint, while separate syntax
  certificates establish when the witness is a coded term.

  The node has no recursive premises.  As for the other raw leaves, list-code
  injectivity rules out every recursive constructor view, and a one-point
  beta support table certifies exactly the root.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedAssignment RawCodedAssignmentTotality
  RawCodedFixedLevelTruthTotality RawCodedSyntaxConstructors
  RawCodedProofConstructors RawCodedProofDescent RawCodedProofTraversal
  RawCodedProofEndpoints RawCodedProofRules RawCodedProofRuleCoverage
  RawCodedListInjectivity RawCodedProofLeafConstructors.

Import ListNotations.

Module PABoundedRawCodedProofEqReflConstructor.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.
Import PABoundedRawCodedAssignmentTotality.
Import PABoundedRawCodedFixedLevelTruthTotality.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedProofConstructors.
Import PABoundedRawCodedProofDescent.
Import PABoundedRawCodedProofTraversal.
Import PABoundedRawCodedProofEndpoints.
Import PABoundedRawCodedProofRules.
Import PABoundedRawCodedProofRuleCoverage.
Import PABoundedRawCodedListInjectivity.
Import PABoundedRawCodedProofLeafConstructors.

Definition rawProofEqReflRoot
    (M : RawPAModel) (context witness : M) : M :=
  rawListCode M [rawNumeralValue M 15; context; witness].

Arguments rawProofEqReflRoot M context witness : clear implicits.

(** Any constructor-shaped view recovers both the tag and payload.  This is
    the key nonstandard-model fact: equality of polynomial list codes cannot
    make the leaf masquerade as a constructor carrying proof children. *)
Lemma raw_proofEqReflRoot_list_view : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      context witness tag payload,
  rawProofEqReflRoot M context witness =
    rawListCode M (rawNumeralValue M tag :: payload) ->
  tag = 15 /\ payload = [context; witness].
Proof.
  intros M hPA context witness tag payload hcode.
  unfold rawProofEqReflRoot in hcode.
  pose proof (rawListCode_injective M hPA
    [rawNumeralValue M 15; context; witness]
    (rawNumeralValue M tag :: payload) hcode) as hfields.
  assert (hhead : rawNumeralValue M 15 = rawNumeralValue M tag).
  { now inversion hfields. }
  assert (htail : [context; witness] = payload).
  { now inversion hfields. }
  split.
  - symmetry. exact (rawNumeralValue_injective M hPA _ _ hhead).
  - symmetry. exact htail.
Qed.

(** Tag [15] is deliberately absent from [rawProofRecursiveCases], whose
    fourteen rows are exactly the constructors with proof premises. *)
Lemma raw_proofEqReflRoot_not_recursive_case : forall
    (M : RawPAModel), RawPASatisfies M -> forall context witness
      rowContext a b c t child1 child2 child3 fields children,
  In (fields, children)
    (rawProofRecursiveCases M
      rowContext a b c t child1 child2 child3) ->
  rawProofEqReflRoot M context witness = rawListCode M fields ->
  False.
Proof.
  intros M hPA context witness rowContext a b c t
    child1 child2 child3 fields children hentry hcode.
  unfold rawProofRecursiveCases in hentry. cbn in hentry.
  repeat match type of hentry with
  | _ \/ _ => destruct hentry as [hentry | hentry]
  end; try contradiction.
  all: inversion hentry; subst fields children; clear hentry.
  all: unfold rawProofEqReflRoot in hcode.
  all: pose proof (rawListCode_injective M hPA _ _ hcode) as hfields;
    discriminate hfields.
Qed.

Lemma raw_proofEqReflRoot_constructor : forall
    (M : RawPAModel) context witness,
  RawProofConstructorCode M
    (rawProofEqReflRoot M context witness)
    context (raw_zero M) (raw_zero M) (raw_zero M) witness
    (raw_zero M) (raw_zero M) (raw_zero M).
Proof.
  intros M context witness.
  unfold RawProofConstructorCode, rawProofEqReflRoot.
  do 15 right. left. reflexivity.
Qed.

Lemma raw_proofEqRefl_syntax_step : forall
    (M : RawPAModel), RawPASatisfies M -> forall context witness
      supportCode supportStep,
  RawProofSyntaxStep M
    (rawProofEqReflRoot M context witness) supportCode supportStep.
Proof.
  intros M hPA context witness supportCode supportStep.
  split.
  - exists context,
      (raw_zero M), (raw_zero M), (raw_zero M), witness,
      (raw_zero M), (raw_zero M), (raw_zero M).
    apply raw_proofEqReflRoot_constructor.
  - intros rowContext a b c t child1 child2 child3 hconstructor.
    split.
    + exact (raw_proofConstructorCode_descent M hPA
        (rawProofEqReflRoot M context witness)
        rowContext a b c t child1 child2 child3 hconstructor).
    + apply Forall_forall. intros [fields children] hentry.
      unfold RawProofChildrenClosedCase.
      intro hcode. exfalso.
      exact (raw_proofEqReflRoot_not_recursive_case M hPA
        context witness rowContext a b c t
        child1 child2 child3 fields children hentry hcode).
Qed.

(** An endpoint view of a tag-[15] code has no freedom: its conclusion is
    exactly the equality of the stored witness with itself. *)
Lemma raw_proofEqRefl_endpoint_rule_complete : forall
    (M : RawPAModel), RawPASatisfies M -> forall context witness,
  RawProofEndpointRuleComplete M
    (rawProofEqReflRoot M context witness).
Proof.
  intros M hPA context witness
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
  all: pose proof (raw_proofEqReflRoot_list_view M hPA
    context witness _ _ hhead) as hview.
  all: destruct hview as [htag hpayload].
  all: try discriminate htag.
  inversion hpayload; subst endpointContext t.
  subst endpointConclusion.
  exists context,
    (raw_zero M), (raw_zero M), (raw_zero M), witness,
    (raw_zero M), (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofRuleValidCases, rawProofEqReflRoot.
  do 15 right. left.
  split; reflexivity.
Qed.

Corollary raw_proofEqRefl_endpoint : forall
    (M : RawPAModel) context witness,
  RawProofEndpoint M
    (rawProofEqReflRoot M context witness)
    context (rawFormulaEqCode M witness witness).
Proof.
  intros M context witness.
  exists context,
    (raw_zero M), (raw_zero M), (raw_zero M), witness,
    (raw_zero M), (raw_zero M), (raw_zero M).
  split; [reflexivity |].
  unfold RawProofEndpointCases, rawProofEqReflRoot.
  do 15 right. left.
  split; reflexivity.
Qed.

(** Public premise-free constructor.  Its support table contains precisely
    the equality-reflexivity root, so endpoint completeness at that root is
    already the full [RawProofRuleCoverage] certificate. *)
Theorem raw_proofEqRefl_ruleCoverage : forall
    (M : RawPAModel), RawPASatisfies M -> forall context witness,
  RawProofRuleCoverage M
    (rawProofEqReflRoot M context witness).
Proof.
  intros M hPA context witness.
  set (root := rawProofEqReflRoot M context witness).
  destruct (raw_codedAssignmentAppend_defined_exists M hPA
    (raw_zero M) (raw_zero M) root (rawNumeralValue M 1)
    (raw_codedZeroAssignment_defined_all M hPA root))
    as (supportCode & supportStep & hdefined & hprefix & hroot).
  exists supportCode, supportStep. split.
  - split.
    + split; [exact hdefined |].
      intros code hbelow hsupported.
      assert (code = root) as ->.
      {
        exact (raw_singleProofRoot_supported_eq M hPA
          root supportCode supportStep hdefined hprefix hroot
          code hbelow hsupported).
      }
      unfold root.
      exact (raw_proofEqRefl_syntax_step M hPA
        context witness supportCode supportStep).
    + unfold rawProofCodeSupported. exact hroot.
  - intros code hbelow hsupported.
    assert (code = root) as ->.
    {
      exact (raw_singleProofRoot_supported_eq M hPA
        root supportCode supportStep hdefined hprefix hroot
        code hbelow hsupported).
    }
    unfold root.
    exact (raw_proofEqRefl_endpoint_rule_complete M hPA
      context witness).
Qed.

End PABoundedRawCodedProofEqReflConstructor.
