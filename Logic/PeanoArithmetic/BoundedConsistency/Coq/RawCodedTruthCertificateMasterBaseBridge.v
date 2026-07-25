(**
  Build the level-zero callback for the concrete six-field master graph.

  There are two genuinely different ways to obtain the proof attached to a
  graph-selected master code.

  - In an arbitrary raw model, the six selected component codes need not be
    standard formula codes.  In that case six local raw proofs must share one
    witnessed PA-axiom context; the raw conjunction constructors can then
    assemble a proof of exactly the selected master code.

  - Ordinary [BProv] derivations quote standard formulas.  They can therefore
    be used only when each of the five field graphs is known to accept the
    corresponding quoted formula code at level zero.  The compact sixth graph
    has this standard view already.  Merely knowing graph totality would not
    justify identifying a possibly nonstandard output with a quoted code.

  Both routes below retain the graph witnesses and choose the transparent
  [rawSixFieldMasterCode] built from them.  Thus the resulting certificate
  cannot drift to a different, externally supplied master formula.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors
  RawCodedPALocalProofExistential
  RawCodedRestrictedPAProof
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyTheorem
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterGraph
  RawCodedTruthCertificateMasterInduction
  RawCodedTruthCertificateMasterAssembler
  RawCodedTruthCertificateMasterIntroduction.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterBaseBridge.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPALocalProofExistential.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyTheorem.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterGraph.
Import PABoundedRawCodedTruthCertificateMasterInduction.
Import PABoundedRawCodedTruthCertificateMasterAssembler.
Import PABoundedRawCodedTruthCertificateMasterIntroduction.

(** The six witnesses selected by the concrete component graphs at zero.
    Keeping the compact graph as a graph assertion, rather than only its
    semantic relation, makes the package line up exactly with the assembler. *)
Definition RawSixFieldMasterZeroGraphWitnessesAt (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    (tail : nat -> M)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  raw_formula_sat M
    (scons M field1 (scons M (raw_zero M) tail)) field1Graph /\
  raw_formula_sat M
    (scons M field2 (scons M (raw_zero M) tail)) field2Graph /\
  raw_formula_sat M
    (scons M field3 (scons M (raw_zero M) tail)) field3Graph /\
  raw_formula_sat M
    (scons M field4 (scons M (raw_zero M) tail)) field4Graph /\
  raw_formula_sat M
    (scons M field5 (scons M (raw_zero M) tail)) field5Graph /\
  raw_formula_sat M
    (scons M finalField (scons M (raw_zero M) tail))
    compactRestrictedPAConsistencyFormulaCodeGraph.

Arguments RawSixFieldMasterZeroGraphWitnessesAt
  M field1Graph field2Graph field3Graph field4Graph field5Graph tail
    field1 field2 field3 field4 field5 finalField : clear implicits.

(** The precise nonstandard-safe proof interface: all six local proofs use
    one context whose finite PA-axiom basis has an explicit witness list. *)
Definition RawSixFieldMasterCommonContextProofsOf (M : RawPAModel)
    (field1 field2 field3 field4 field5 finalField : M) : Prop :=
  exists witnessList context
      root1 root2 root3 root4 root5 finalRoot : M,
    RawCodedPAAxiomWitnessContext M witnessList context /\
    RawCodedPALocalProofOf M context field1 root1 /\
    RawCodedPALocalProofOf M context field2 root2 /\
    RawCodedPALocalProofOf M context field3 root3 /\
    RawCodedPALocalProofOf M context field4 root4 /\
    RawCodedPALocalProofOf M context field5 root5 /\
    RawCodedPALocalProofOf M context finalField finalRoot.

Arguments RawSixFieldMasterCommonContextProofsOf
  M field1 field2 field3 field4 field5 finalField : clear implicits.

(** A raw zero-component package chooses graph witnesses and proves those
    same carrier elements.  The quantification over [tail] is necessary
    because a graph may mention parameters beyond its output and level. *)
Definition RawSixFieldMasterZeroRawComponentPackage (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : Prop :=
  forall tail : nat -> M,
    exists field1 field2 field3 field4 field5 finalField : M,
      RawSixFieldMasterZeroGraphWitnessesAt M
        field1Graph field2Graph field3Graph field4Graph field5Graph tail
        field1 field2 field3 field4 field5 finalField /\
      RawSixFieldMasterCommonContextProofsOf M
        field1 field2 field3 field4 field5 finalField.

Arguments RawSixFieldMasterZeroRawComponentPackage
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    : clear implicits.

(** Common-context component proofs discharge the exact master base callback.
    In particular, the certificate target is definitionally the master code
    made from the six graph witnesses below. *)
Theorem raw_sixFieldMasterPackageBase_of_raw_components : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawSixFieldMasterZeroRawComponentPackage M
    field1Graph field2Graph field3Graph field4Graph field5Graph ->
  RawSixFieldMasterPackageBase M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M hPA
    field1Graph field2Graph field3Graph field4Graph field5Graph
    hcomponents tail.
  destruct (hcomponents tail) as
    (field1 & field2 & field3 & field4 & field5 & finalField &
      hgraphs & hproofs).
  unfold RawSixFieldMasterZeroGraphWitnessesAt in hgraphs.
  destruct hgraphs as
    (hfield1Graph & hfield2Graph & hfield3Graph & hfield4Graph &
      hfield5Graph & hfinalGraph).
  unfold RawSixFieldMasterCommonContextProofsOf in hproofs.
  destruct hproofs as
    (witnessList & context & root1 & root2 & root3 & root4 & root5 &
      finalRoot & hwitness & hfield1Proof & hfield2Proof &
      hfield3Proof & hfield4Proof & hfield5Proof & hfinalProof).
  destruct (raw_codedPAProofOf_sixFieldMaster_intro M hPA
    witnessList context
    field1 field2 field3 field4 field5 finalField
    root1 root2 root3 root4 root5 finalRoot
    hwitness hfield1Proof hfield2Proof hfield3Proof
    hfield4Proof hfield5Proof hfinalProof)
    as [certificate hcertificate].
  set (master := rawSixFieldMasterCode M
    field1 field2 field3 field4 field5 finalField).
  exists master, certificate. split.
  - apply (proj2 (raw_sat_concreteSixFieldMasterGraph_iff M
      field1Graph field2Graph field3Graph field4Graph field5Graph
      tail (raw_zero M) master)).
    exists field1, field2, field3, field4, field5, finalField.
    repeat split.
    + exact hfield1Graph.
    + exact hfield2Graph.
    + exact hfield3Graph.
    + exact hfield4Graph.
    + exact hfield5Graph.
    + exact (proj1
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail (raw_zero M) finalField) hfinalGraph).
  - unfold master. exact hcertificate.
Qed.

(** At level zero, totality alone chooses an arbitrary carrier output. *)
Definition RawOutputFirstFieldGraphZeroTotal (M : RawPAModel)
    (fieldGraph : formula) : Prop :=
  forall tail : nat -> M,
    exists output : M,
      raw_formula_sat M
        (scons M output (scons M (raw_zero M) tail)) fieldGraph.

Arguments RawOutputFirstFieldGraphZeroTotal M fieldGraph : clear implicits.

(** This is the explicit standard-view condition needed to identify such an
    arbitrary zero-level output with the code quoted by [BProv].  Functional
    standard graphs normally establish this form. *)
Definition RawOutputFirstFieldGraphStandardZeroView (M : RawPAModel)
    (fieldGraph fieldFormula : formula) : Prop :=
  forall (tail : nat -> M) output,
    raw_formula_sat M
      (scons M output (scons M (raw_zero M) tail)) fieldGraph ->
    output = rawQuotedFormulaCode M fieldFormula.

Arguments RawOutputFirstFieldGraphStandardZeroView
  M fieldGraph fieldFormula : clear implicits.

(** The base construction needs only one standard graph witness, not the
    stronger assertion that every alternative output is standard. *)
Definition RawOutputFirstFieldGraphStandardZeroWitness (M : RawPAModel)
    (fieldGraph fieldFormula : formula) : Prop :=
  forall tail : nat -> M,
    raw_formula_sat M
      (scons M (rawQuotedFormulaCode M fieldFormula)
        (scons M (raw_zero M) tail)) fieldGraph.

Arguments RawOutputFirstFieldGraphStandardZeroWitness
  M fieldGraph fieldFormula : clear implicits.

Lemma raw_outputFirstFieldGraphStandardZeroWitness_of_total_view : forall
    (M : RawPAModel) fieldGraph fieldFormula,
  RawOutputFirstFieldGraphZeroTotal M fieldGraph ->
  RawOutputFirstFieldGraphStandardZeroView M fieldGraph fieldFormula ->
  RawOutputFirstFieldGraphStandardZeroWitness M fieldGraph fieldFormula.
Proof.
  intros M fieldGraph fieldFormula htotal hview tail.
  destruct (htotal tail) as [output houtput].
  rewrite <- (hview tail output houtput).
  exact houtput.
Qed.

(** Standard components carry exactly the five graph witnesses and five
    closed derivations needed by the ordinary quotation route.  The sixth
    component is fixed: its graph witness is supplied by compact-graph
    standardness and its derivation by the bounded-consistency theorem. *)
Definition RawSixFieldMasterZeroBProvComponentPackage (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    (field1Formula field2Formula field3Formula field4Formula field5Formula
      : formula) : Prop :=
  RawOutputFirstFieldGraphStandardZeroWitness M
    field1Graph field1Formula /\
  RawOutputFirstFieldGraphStandardZeroWitness M
    field2Graph field2Formula /\
  RawOutputFirstFieldGraphStandardZeroWitness M
    field3Graph field3Formula /\
  RawOutputFirstFieldGraphStandardZeroWitness M
    field4Graph field4Formula /\
  RawOutputFirstFieldGraphStandardZeroWitness M
    field5Graph field5Formula /\
  Formula.BProv Formula.Ax_s [] field1Formula /\
  Formula.BProv Formula.Ax_s [] field2Formula /\
  Formula.BProv Formula.Ax_s [] field3Formula /\
  Formula.BProv Formula.Ax_s [] field4Formula /\
  Formula.BProv Formula.Ax_s [] field5Formula.

Arguments RawSixFieldMasterZeroBProvComponentPackage
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    field1Formula field2Formula field3Formula field4Formula field5Formula
    : clear implicits.

(** The standard route still proves the exact graph-selected master: here the
    selected witnesses are the quoted component codes guaranteed above. *)
Theorem raw_sixFieldMasterPackageBase_of_BProv_components : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1Graph field2Graph field3Graph field4Graph field5Graph
      field1Formula field2Formula field3Formula field4Formula field5Formula,
  RawSixFieldMasterZeroBProvComponentPackage M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    field1Formula field2Formula field3Formula field4Formula field5Formula ->
  RawSixFieldMasterPackageBase M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M hPA
    field1Graph field2Graph field3Graph field4Graph field5Graph
    field1Formula field2Formula field3Formula field4Formula field5Formula
    hcomponents tail.
  unfold RawSixFieldMasterZeroBProvComponentPackage in hcomponents.
  destruct hcomponents as
    (hfield1Graph & hfield2Graph & hfield3Graph & hfield4Graph &
      hfield5Graph & hfield1Proof & hfield2Proof & hfield3Proof &
      hfield4Proof & hfield5Proof).
  specialize (hfield1Graph tail).
  specialize (hfield2Graph tail).
  specialize (hfield3Graph tail).
  specialize (hfield4Graph tail).
  specialize (hfield5Graph tail).
  set (field1 := rawQuotedFormulaCode M field1Formula).
  set (field2 := rawQuotedFormulaCode M field2Formula).
  set (field3 := rawQuotedFormulaCode M field3Formula).
  set (field4 := rawQuotedFormulaCode M field4Formula).
  set (field5 := rawQuotedFormulaCode M field5Formula).
  set (finalFormula := restrictedPAConsistencyFormula 0).
  set (finalField := rawQuotedFormulaCode M finalFormula).
  assert (hfinalGraph : raw_formula_sat M
      (scons M finalField (scons M (raw_zero M) tail))
      compactRestrictedPAConsistencyFormulaCodeGraph).
  {
    unfold finalField, finalFormula.
    rewrite (rawQuotedFormulaCode_standard M hPA
      (restrictedPAConsistencyFormula 0)).
    exact (compactRestrictedPAConsistencyFormulaCodeGraph_standard
      M hPA tail 0).
  }
  destruct (raw_codedPAProofOf_sixFieldMaster_of_BProv M hPA
    field1Formula field2Formula field3Formula field4Formula field5Formula
    finalFormula
    hfield1Proof hfield2Proof hfield3Proof hfield4Proof hfield5Proof
    (PA_BProv_restrictedPAConsistencyFormula 0))
    as [certificate hcertificate].
  set (master := rawSixFieldMasterCode M
    field1 field2 field3 field4 field5 finalField).
  exists master, certificate. split.
  - apply (proj2 (raw_sat_concreteSixFieldMasterGraph_iff M
      field1Graph field2Graph field3Graph field4Graph field5Graph
      tail (raw_zero M) master)).
    exists field1, field2, field3, field4, field5, finalField.
    repeat split.
    + unfold field1. exact hfield1Graph.
    + unfold field2. exact hfield2Graph.
    + unfold field3. exact hfield3Graph.
    + unfold field4. exact hfield4Graph.
    + unfold field5. exact hfield5Graph.
    + exact (proj1
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail (raw_zero M) finalField) hfinalGraph).
  - unfold master, field1, field2, field3, field4, field5,
      finalField, finalFormula.
    exact hcertificate.
Qed.

(** The public zero-component interface permits either construction. *)
Definition RawSixFieldMasterZeroComponentPackage (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : Prop :=
  RawSixFieldMasterZeroRawComponentPackage M
    field1Graph field2Graph field3Graph field4Graph field5Graph \/
  exists field1Formula field2Formula field3Formula field4Formula field5Formula,
    RawSixFieldMasterZeroBProvComponentPackage M
      field1Graph field2Graph field3Graph field4Graph field5Graph
      field1Formula field2Formula field3Formula field4Formula field5Formula.

Arguments RawSixFieldMasterZeroComponentPackage
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    : clear implicits.

Theorem raw_sixFieldMasterPackageBase_of_components : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawSixFieldMasterZeroComponentPackage M
    field1Graph field2Graph field3Graph field4Graph field5Graph ->
  RawSixFieldMasterPackageBase M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M hPA
    field1Graph field2Graph field3Graph field4Graph field5Graph
    [hraw | hstandard].
  - exact (raw_sixFieldMasterPackageBase_of_raw_components M hPA
      field1Graph field2Graph field3Graph field4Graph field5Graph hraw).
  - destruct hstandard as
      (field1Formula & field2Formula & field3Formula & field4Formula &
        field5Formula & hstandard).
    exact (raw_sixFieldMasterPackageBase_of_BProv_components M hPA
      field1Graph field2Graph field3Graph field4Graph field5Graph
      field1Formula field2Formula field3Formula field4Formula field5Formula
      hstandard).
Qed.

End PABoundedRawCodedTruthCertificateMasterBaseBridge.
