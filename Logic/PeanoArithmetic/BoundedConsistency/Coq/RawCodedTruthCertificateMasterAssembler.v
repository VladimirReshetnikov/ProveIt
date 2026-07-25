(**
  Assemble five output-first field graphs and the compact consistency graph
  into one output-first six-field master graph.

  Every input field graph is read under

      field :: level :: tail,

  while the assembled graph is read under

      master :: level :: tail.

  Six existential witnesses are introduced in the order field1, ..., field5,
  finalField.  At their common body the environment is therefore

      finalField :: field5 :: field4 :: field3 :: field2 :: field1
        :: master :: level :: tail.

  The explicit renamings below project the appropriate field, retain level,
  and skip the other witnesses before forwarding the original tail.  Keeping
  this map visible avoids relying on an informal de Bruijn convention.
*)

From Stdlib Require Import List Arith Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyFormulaCode
  CompactRestrictedPAConsistencyFormulaCodeGraph
  RawCodedTruthCertificateFinalProjection
  RawCodedTruthCertificateMasterGraph
  RawCodedTruthCertificateMasterInduction.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterAssembler.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.
Import PABoundedRawCodedTruthCertificateFinalProjection.
Import PABoundedRawCodedTruthCertificateMasterGraph.
Import PABoundedRawCodedTruthCertificateMasterInduction.

(** In the six-witness body, [outputSlot] selects the desired field.  The
    level is always body variable seven and the old tail begins at eight. *)
Definition sixFieldAssemblerRenaming
    (outputSlot index : nat) : nat :=
  match index with
  | 0 => outputSlot
  | 1 => 7
  | S (S tailIndex) => 8 + tailIndex
  end.

Definition sixFieldAssemblerEnvironment (M : RawPAModel)
    (finalField field5 field4 field3 field2 field1 master level : M)
    (tail : nat -> M) : nat -> M :=
  scons M finalField
    (scons M field5
      (scons M field4
        (scons M field3
          (scons M field2
            (scons M field1
              (scons M master (scons M level tail))))))).

(** Exact semantic effect of one projected field renaming.  The selected
    output is left abstract as [bodyEnv outputSlot], which lets all six uses
    share this lemma. *)
Lemma raw_sat_sixFieldAssemblerRenamedGraph_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail
      outputSlot,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming outputSlot) graph) <->
  raw_formula_sat M
    (scons M
      ((sixFieldAssemblerEnvironment M
        finalField field5 field4 field3 field2 field1 master level tail)
        outputSlot)
      (scons M level tail))
    graph.
Proof.
  intros M graph finalField field5 field4 field3 field2 field1
    master level tail outputSlot.
  rewrite raw_formula_sat_rename.
  apply raw_formula_sat_ext. intro index.
  destruct index as [|[|tailIndex]].
  - reflexivity.
  - unfold sixFieldAssemblerEnvironment,
      sixFieldAssemblerRenaming.
    cbn [scons]. reflexivity.
  - unfold sixFieldAssemblerEnvironment,
      sixFieldAssemblerRenaming.
    cbn [scons]. reflexivity.
Qed.

Corollary raw_sat_sixFieldAssembler_field1_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming 5) graph) <->
  raw_formula_sat M (scons M field1 (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_sixFieldAssemblerRenamedGraph_iff.
  cbn [sixFieldAssemblerEnvironment scons]. reflexivity.
Qed.

Corollary raw_sat_sixFieldAssembler_field2_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming 4) graph) <->
  raw_formula_sat M (scons M field2 (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_sixFieldAssemblerRenamedGraph_iff.
  cbn [sixFieldAssemblerEnvironment scons]. reflexivity.
Qed.

Corollary raw_sat_sixFieldAssembler_field3_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming 3) graph) <->
  raw_formula_sat M (scons M field3 (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_sixFieldAssemblerRenamedGraph_iff.
  cbn [sixFieldAssemblerEnvironment scons]. reflexivity.
Qed.

Corollary raw_sat_sixFieldAssembler_field4_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming 2) graph) <->
  raw_formula_sat M (scons M field4 (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_sixFieldAssemblerRenamedGraph_iff.
  cbn [sixFieldAssemblerEnvironment scons]. reflexivity.
Qed.

Corollary raw_sat_sixFieldAssembler_field5_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming 1) graph) <->
  raw_formula_sat M (scons M field5 (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_sixFieldAssemblerRenamedGraph_iff.
  cbn [sixFieldAssemblerEnvironment scons]. reflexivity.
Qed.

Corollary raw_sat_sixFieldAssembler_final_iff : forall
    (M : RawPAModel) graph
      finalField field5 field4 field3 field2 field1 master level tail,
  raw_formula_sat M
    (sixFieldAssemblerEnvironment M
      finalField field5 field4 field3 field2 field1 master level tail)
    (Formula.rename (sixFieldAssemblerRenaming 0) graph) <->
  raw_formula_sat M (scons M finalField (scons M level tail)) graph.
Proof.
  intros. rewrite raw_sat_sixFieldAssemblerRenamedGraph_iff.
  cbn [sixFieldAssemblerEnvironment scons]. reflexivity.
Qed.

(** Right-associated wrappers make the witness and conjunction layout
    definitionally transparent in the semantic proof. *)
Definition sixFieldAssemblerEx6 (body : formula) : formula :=
  pEx (pEx (pEx (pEx (pEx (pEx body))))).

Definition sixFieldAssemblerAnd7
    (first second third fourth fifth sixth seventh : formula) : formula :=
  pAnd first
    (pAnd second
      (pAnd third
        (pAnd fourth
          (pAnd fifth (pAnd sixth seventh))))).

(** The resulting graph is output-first under [master :: level :: tail]. *)
Definition concreteSixFieldMasterGraph
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    : formula :=
  sixFieldAssemblerEx6
    (sixFieldAssemblerAnd7
      (Formula.rename (sixFieldAssemblerRenaming 5) field1Graph)
      (Formula.rename (sixFieldAssemblerRenaming 4) field2Graph)
      (Formula.rename (sixFieldAssemblerRenaming 3) field3Graph)
      (Formula.rename (sixFieldAssemblerRenaming 2) field4Graph)
      (Formula.rename (sixFieldAssemblerRenaming 1) field5Graph)
      (Formula.rename (sixFieldAssemblerRenaming 0)
        compactRestrictedPAConsistencyFormulaCodeGraph)
      (sixFieldMasterCodeTermAt
        (tVar 6) (tVar 5) (tVar 4) (tVar 3)
        (tVar 2) (tVar 1) (tVar 0))).

(** Semantic relation exposed by the assembled formula. *)
Definition RawConcreteSixFieldMasterGraphAt (M : RawPAModel)
    (field1Graph field2Graph field3Graph field4Graph field5Graph : formula)
    (tail : nat -> M) (level master : M) : Prop :=
  exists field1 field2 field3 field4 field5 finalField : M,
    raw_formula_sat M (scons M field1 (scons M level tail))
      field1Graph /\
    raw_formula_sat M (scons M field2 (scons M level tail))
      field2Graph /\
    raw_formula_sat M (scons M field3 (scons M level tail))
      field3Graph /\
    raw_formula_sat M (scons M field4 (scons M level tail))
      field4Graph /\
    raw_formula_sat M (scons M field5 (scons M level tail))
      field5Graph /\
    RawRestrictedPAConsistencyFormulaCodeAt M level finalField /\
    RawSixFieldMasterCodeAt M master
      field1 field2 field3 field4 field5 finalField.

Arguments RawConcreteSixFieldMasterGraphAt
  M field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level master : clear implicits.

(** Exact arbitrary-model semantics.  No model axioms are needed: this is
    solely binder bookkeeping plus the already exact compact-target and
    six-field constructor graphs. *)
Theorem raw_sat_concreteSixFieldMasterGraph_iff : forall
    (M : RawPAModel)
      field1Graph field2Graph field3Graph field4Graph field5Graph
      tail level master,
  raw_formula_sat M (scons M master (scons M level tail))
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph) <->
  RawConcreteSixFieldMasterGraphAt M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level master.
Proof.
  intros M field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level master.
  unfold concreteSixFieldMasterGraph,
    sixFieldAssemblerEx6, sixFieldAssemblerAnd7,
    RawConcreteSixFieldMasterGraphAt.
  cbn [raw_formula_sat].
  split.
  - intros (field1 & field2 & field3 & field4 & field5 & finalField &
      hfield1 & hfield2 & hfield3 & hfield4 & hfield5 &
      hfinalGraph & hmasterGraph).
    exists field1, field2, field3, field4, field5, finalField.
    repeat split.
    + exact (proj1 (raw_sat_sixFieldAssembler_field1_iff M
        field1Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield1).
    + exact (proj1 (raw_sat_sixFieldAssembler_field2_iff M
        field2Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield2).
    + exact (proj1 (raw_sat_sixFieldAssembler_field3_iff M
        field3Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield3).
    + exact (proj1 (raw_sat_sixFieldAssembler_field4_iff M
        field4Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield4).
    + exact (proj1 (raw_sat_sixFieldAssembler_field5_iff M
        field5Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield5).
    + apply (proj1
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail level finalField)).
      exact (proj1 (raw_sat_sixFieldAssembler_final_iff M
        compactRestrictedPAConsistencyFormulaCodeGraph
        finalField field5 field4 field3 field2 field1
        master level tail) hfinalGraph).
    + pose proof (proj1
        (raw_sat_sixFieldMasterCodeTermAt_iff M
          (sixFieldAssemblerEnvironment M
            finalField field5 field4 field3 field2 field1
            master level tail)
          (tVar 6) (tVar 5) (tVar 4) (tVar 3)
          (tVar 2) (tVar 1) (tVar 0))
        hmasterGraph) as hmasterCode.
      cbn [sixFieldAssemblerEnvironment raw_term_eval scons]
        in hmasterCode.
      exact hmasterCode.
  - intros (field1 & field2 & field3 & field4 & field5 & finalField &
      hfield1 & hfield2 & hfield3 & hfield4 & hfield5 &
      hfinalCode & hmasterCode).
    exists field1, field2, field3, field4, field5, finalField.
    repeat split.
    + exact (proj2 (raw_sat_sixFieldAssembler_field1_iff M
        field1Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield1).
    + exact (proj2 (raw_sat_sixFieldAssembler_field2_iff M
        field2Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield2).
    + exact (proj2 (raw_sat_sixFieldAssembler_field3_iff M
        field3Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield3).
    + exact (proj2 (raw_sat_sixFieldAssembler_field4_iff M
        field4Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield4).
    + exact (proj2 (raw_sat_sixFieldAssembler_field5_iff M
        field5Graph finalField field5 field4 field3 field2 field1
        master level tail) hfield5).
    + apply (proj2 (raw_sat_sixFieldAssembler_final_iff M
        compactRestrictedPAConsistencyFormulaCodeGraph
        finalField field5 field4 field3 field2 field1
        master level tail)).
      exact (proj2
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail level finalField) hfinalCode).
    + apply (proj2
        (raw_sat_sixFieldMasterCodeTermAt_iff M
          (sixFieldAssemblerEnvironment M
            finalField field5 field4 field3 field2 field1
            master level tail)
          (tVar 6) (tVar 5) (tVar 4) (tVar 3)
          (tVar 2) (tVar 1) (tVar 0))).
      cbn [sixFieldAssemblerEnvironment raw_term_eval scons].
      exact hmasterCode.
Qed.

(** This is precisely the decomposition callback consumed by the generic
    master-package induction bridge. *)
Theorem concreteSixFieldMasterGraph_decomposition : forall
    (M : RawPAModel)
      field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawSixFieldMasterGraphDecomposition M
    (concreteSixFieldMasterGraph
      field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level master hgraph.
  pose proof (proj1 (raw_sat_concreteSixFieldMasterGraph_iff M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level master) hgraph) as hsemantic.
  destruct hsemantic as
    (field1 & field2 & field3 & field4 & field5 & finalField &
      _ & _ & _ & _ & _ & hfinalCode & hmasterCode).
  exists field1, field2, field3, field4, field5, finalField.
  split; assumption.
Qed.

(** Uniform semantic totality for one output-first field graph. *)
Definition RawOutputFirstFieldGraphTotal (M : RawPAModel)
    (fieldGraph : formula) : Prop :=
  forall (tail : nat -> M) level,
    exists field,
      raw_formula_sat M (scons M field (scons M level tail)) fieldGraph.

Arguments RawOutputFirstFieldGraphTotal M fieldGraph : clear implicits.

(** Totality of all five inputs and the already proved compact target graph
    gives totality of the assembled master graph.  The master output itself
    is the transparent right-associated conjunction code. *)
Theorem concreteSixFieldMasterGraph_raw_total : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      field1Graph field2Graph field3Graph field4Graph field5Graph,
  RawOutputFirstFieldGraphTotal M field1Graph ->
  RawOutputFirstFieldGraphTotal M field2Graph ->
  RawOutputFirstFieldGraphTotal M field3Graph ->
  RawOutputFirstFieldGraphTotal M field4Graph ->
  RawOutputFirstFieldGraphTotal M field5Graph ->
  forall tail level,
    exists master,
      raw_formula_sat M (scons M master (scons M level tail))
        (concreteSixFieldMasterGraph
          field1Graph field2Graph field3Graph field4Graph field5Graph).
Proof.
  intros M hPA field1Graph field2Graph field3Graph field4Graph field5Graph
    hfield1Total hfield2Total hfield3Total hfield4Total hfield5Total
    tail level.
  destruct (hfield1Total tail level) as [field1 hfield1].
  destruct (hfield2Total tail level) as [field2 hfield2].
  destruct (hfield3Total tail level) as [field3 hfield3].
  destruct (hfield4Total tail level) as [field4 hfield4].
  destruct (hfield5Total tail level) as [field5 hfield5].
  destruct (compactRestrictedPAConsistencyFormulaCodeGraph_raw_total
    M hPA tail level) as [finalField hfinalGraph].
  set (master := rawSixFieldMasterCode M
    field1 field2 field3 field4 field5 finalField).
  exists master.
  apply (proj2 (raw_sat_concreteSixFieldMasterGraph_iff M
    field1Graph field2Graph field3Graph field4Graph field5Graph
    tail level master)).
  exists field1, field2, field3, field4, field5, finalField.
  split; [exact hfield1 |].
  split; [exact hfield2 |].
  split; [exact hfield3 |].
  split; [exact hfield4 |].
  split; [exact hfield5 |].
  split.
  - exact (proj1
      (compactRestrictedPAConsistencyFormulaCodeGraph_representation
        M tail level finalField) hfinalGraph).
  - unfold master.
    exact (raw_sixFieldMasterCodeAt_total M
      field1 field2 field3 field4 field5 finalField).
Qed.

End PABoundedRawCodedTruthCertificateMasterAssembler.
