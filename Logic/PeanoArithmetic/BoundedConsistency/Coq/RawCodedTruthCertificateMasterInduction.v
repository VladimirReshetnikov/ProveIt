(**
  Generic PA-internal induction for a six-field master proof package.

  The fixed [masterGraph] formula is output-first.  Its semantic environment
  is exactly

      master :: level :: tail.

  Thus the direct package formula can existentially bind [master] without
  any graph-specific lifting.  The same witness is required both to satisfy
  the graph and to have an ordinary coded PA proof.  This prevents a
  successor callback from proving an unrelated formula while claiming to
  have constructed the six reusable truth-certificate fields.

  Only three graph-specific semantic callbacks remain: graph decomposition,
  the package at zero, and preservation of the package under successor.  The
  induction below is [raw_definable_induction], so it reaches nonstandard
  elements of arbitrary PA models; a Rocq recursion over [nat] would not.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawModelCompleteness RawCodedPAProvability
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTruthCertificateMasterGraph
  CompactPAUniformProvability.

Import ListNotations.

Module PABoundedRawCodedTruthCertificateMasterInduction.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTruthCertificateMasterGraph.
Import PABoundedCompactPAUniformProvability.

(** The graph is evaluated directly under [master :: level :: tail]. *)
Definition RawSixFieldMasterDirectPackageAt (M : RawPAModel)
    (masterGraph : formula) (tail : nat -> M) (level : M) : Prop :=
  exists master certificate : M,
    raw_formula_sat M (scons M master (scons M level tail)) masterGraph /\
    RawCodedPAProofOf M master certificate.

Arguments RawSixFieldMasterDirectPackageAt
  M masterGraph tail level : clear implicits.

(** Under the existential binder, variable zero is [master], while the
    ambient environment begins with [level]. *)
Definition sixFieldMasterDirectPackageFormula
    (masterGraph : formula) : formula :=
  pEx
    (pAnd masterGraph
      (codedPAProvabilityTermAt (tVar 0))).

Lemma raw_sat_sixFieldMasterDirectPackageFormula_iff : forall
    (M : RawPAModel) masterGraph (tail : nat -> M) level,
  raw_formula_sat M (scons M level tail)
    (sixFieldMasterDirectPackageFormula masterGraph) <->
  RawSixFieldMasterDirectPackageAt M masterGraph tail level.
Proof.
  intros M masterGraph tail level.
  unfold sixFieldMasterDirectPackageFormula,
    RawSixFieldMasterDirectPackageAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAProvabilityTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros (master & hgraph & certificate & hcertificate).
    exists master, certificate. split; assumption.
  - intros (master & certificate & hgraph & hcertificate).
    exists master. split; [exact hgraph |].
    exists certificate. exact hcertificate.
Qed.

(** The fixed graph must reveal a syntactically forced six-field master
    code, and its final field must be exactly the compact [Con_level] target.
    The five reusable fields are intentionally unconstrained here: their
    construction and successor relationship belong to the concrete graph. *)
Definition RawSixFieldMasterGraphDecomposition (M : RawPAModel)
    (masterGraph : formula) : Prop :=
  forall (tail : nat -> M) level master,
    raw_formula_sat M (scons M master (scons M level tail)) masterGraph ->
    exists field1 field2 field3 field4 field5 finalField : M,
      RawSixFieldMasterCodeAt M master
        field1 field2 field3 field4 field5 finalField /\
      RawRestrictedPAConsistencyFormulaCodeAt M level finalField.

Arguments RawSixFieldMasterGraphDecomposition M masterGraph
  : clear implicits.

(** The remaining callbacks speak only about the represented direct package;
    they contain neither a target-code side channel nor a separate proof
    witness that could drift away from the graph-selected master. *)
Definition RawSixFieldMasterPackageBase (M : RawPAModel)
    (masterGraph : formula) : Prop :=
  forall tail,
    RawSixFieldMasterDirectPackageAt M masterGraph tail (raw_zero M).

Arguments RawSixFieldMasterPackageBase M masterGraph : clear implicits.

Definition RawSixFieldMasterPackageSuccessor (M : RawPAModel)
    (masterGraph : formula) : Prop :=
  forall tail level,
    RawSixFieldMasterDirectPackageAt M masterGraph tail level ->
    RawSixFieldMasterDirectPackageAt M masterGraph tail
      (raw_succ M level).

Arguments RawSixFieldMasterPackageSuccessor M masterGraph
  : clear implicits.

(** A convenient all-model bundle used only by the final completeness step.
    Keeping its three fields separate above makes each concrete construction
    obligation independently auditable. *)
Definition RawSixFieldMasterInductionCallbacksInAllModels
    (masterGraph : formula) : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawSixFieldMasterGraphDecomposition M masterGraph /\
    RawSixFieldMasterPackageBase M masterGraph /\
    RawSixFieldMasterPackageSuccessor M masterGraph.

(** The direct package is a represented arithmetic predicate.  PA induction
    therefore ranges over every carrier element, including nonstandard
    levels in nonstandard models. *)
Theorem raw_sixFieldMasterDirectPackages_all : forall
    (M : RawPAModel), RawPASatisfies M -> forall masterGraph,
  RawSixFieldMasterPackageBase M masterGraph ->
  RawSixFieldMasterPackageSuccessor M masterGraph ->
  forall tail level,
    RawSixFieldMasterDirectPackageAt M masterGraph tail level.
Proof.
  intros M hPA masterGraph hbase hsuccessor tail.
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail)
        (sixFieldMasterDirectPackageFormula masterGraph)).
  {
    apply (raw_definable_induction M hPA
      (sixFieldMasterDirectPackageFormula masterGraph) tail).
    - apply (proj2
        (raw_sat_sixFieldMasterDirectPackageFormula_iff
          M masterGraph tail (raw_zero M))).
      exact (hbase tail).
    - intros level hlevel.
      apply (proj2
        (raw_sat_sixFieldMasterDirectPackageFormula_iff
          M masterGraph tail (raw_succ M level))).
      apply (hsuccessor tail level).
      exact (proj1
        (raw_sat_sixFieldMasterDirectPackageFormula_iff
          M masterGraph tail level) hlevel).
  }
  intro level.
  exact (proj1
    (raw_sat_sixFieldMasterDirectPackageFormula_iff
      M masterGraph tail level) (hall level)).
Qed.

(** Five right projections turn the graph-forced master proof into a proof
    of the forced final coordinate.  Its second decomposition fact then makes
    that coordinate an ordinary compact-selector package. *)
Theorem raw_sixFieldMasterDirectPackage_to_compactSelector : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      masterGraph tail level,
  RawSixFieldMasterGraphDecomposition M masterGraph ->
  RawSixFieldMasterDirectPackageAt M masterGraph tail level ->
  RawCompactSelectorPackageAt M tail level.
Proof.
  intros M hPA masterGraph tail level hdecompose
    (master & certificate & hgraph & hcertificate).
  destruct (hdecompose tail level master hgraph) as
    (field1 & field2 & field3 & field4 & field5 & finalField &
      hmaster & hfinalCode).
  destruct (raw_sixFieldMasterProvability_final M hPA
    field1 field2 field3 field4 field5 finalField)
    as [finalCertificate hfinalCertificate].
  {
    exists master, certificate. split; assumption.
  }
  exists finalField, finalCertificate. split; assumption.
Qed.

Corollary raw_compactSelectorPackages_all_of_sixFieldMaster : forall
    (M : RawPAModel), RawPASatisfies M -> forall masterGraph,
  RawSixFieldMasterGraphDecomposition M masterGraph ->
  RawSixFieldMasterPackageBase M masterGraph ->
  RawSixFieldMasterPackageSuccessor M masterGraph ->
  forall tail level,
    RawCompactSelectorPackageAt M tail level.
Proof.
  intros M hPA masterGraph hdecompose hbase hsuccessor tail level.
  apply (raw_sixFieldMasterDirectPackage_to_compactSelector M hPA
    masterGraph tail level hdecompose).
  exact (raw_sixFieldMasterDirectPackages_all M hPA masterGraph
    hbase hsuccessor tail level).
Qed.

(** The generic master callbacks imply the exact arbitrary-model reading of
    the sealed uniform compact sentence. *)
Theorem
    compactUniformRestrictedPAConsistencyProvabilityFormula_raw_valid_of_sixFieldMaster :
    forall masterGraph,
  RawSixFieldMasterInductionCallbacksInAllModels masterGraph ->
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e
      compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros masterGraph hcallbacks M hPA e.
  apply (proj2
    (raw_sat_compactUniformRestrictedPAConsistencyProvabilityFormula_iff
      M e)).
  intros tail level.
  destruct (hcallbacks M hPA) as
    [hdecompose [hbase hsuccessor]].
  exact (raw_compactSelectorPackages_all_of_sixFieldMaster M hPA
    masterGraph hdecompose hbase hsuccessor tail level).
Qed.

(** Raw-model completeness converts the all-model construction into the
    requested object-level PA theorem.  This result remains conditional only
    on the three narrow, graph-specific callbacks above. *)
Theorem
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_sixFieldMaster :
    forall masterGraph,
  RawSixFieldMasterInductionCallbacksInAllModels masterGraph ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros masterGraph hcallbacks.
  apply PA_BProv_of_raw_valid.
  - exact compactUniformRestrictedPAConsistencyProvabilityFormula_sentence.
  - exact
      (compactUniformRestrictedPAConsistencyProvabilityFormula_raw_valid_of_sixFieldMaster
        masterGraph hcallbacks).
Qed.

End PABoundedRawCodedTruthCertificateMasterInduction.
