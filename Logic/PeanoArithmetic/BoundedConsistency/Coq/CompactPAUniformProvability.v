(**
  The compact target-code graph reduces uniform bounded consistency to one
  genuine proof-code constructor.

  [RawCodedPAUniformProvability] used a graph chosen by the generic
  Diophantine-representation interface.  Its arbitrary-model behaviour was
  consequently part of the compiler hypothesis.  The compact graph is an
  explicit PA formula and is already known to be total and exact in every PA
  model, including at nonstandard elements.  This file therefore removes
  target-code generation, graph adequacy, and the zero case from the open
  assumptions.

  The sole remaining premise is a successor transformer for ordinary PA
  proof certificates.  It receives a proof of the target at [level] and must
  produce a proof of the target at [level + 1].  PA's own induction then
  iterates that transformer over every element of an arbitrary PA model.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawModelCompleteness
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyTheorem
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedPAProvability
  CompactRestrictedPAConsistencyFormulaCodeGraph.

Import ListNotations.

Module PABoundedCompactPAUniformProvability.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyTheorem.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedPAProvability.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.

(** The package predicate is deliberately a formula: this lets PA's full
    induction scheme range over nonstandard levels.  At a level it stores a
    target selected by the compact code graph together with an ordinary PA
    proof certificate for that target. *)
Definition compactSelectorPackageFormula : formula :=
  pEx
    (pAnd
      compactRestrictedPAConsistencyFormulaCodeGraph
      (codedPAProvabilityTermAt (tVar 0))).

Definition RawCompactSelectorPackageAt (M : RawPAModel)
    (tail : nat -> M) (level : M) : Prop :=
  exists target certificate : M,
    RawRestrictedPAConsistencyFormulaCodeAt M level target /\
    RawCodedPAProofOf M target certificate.

Arguments RawCompactSelectorPackageAt M tail level : clear implicits.

(** Although [tail] occurs in the syntactic environment, the represented
    graph and the proof predicate do not semantically depend on it. *)
Lemma raw_sat_compactSelectorPackageFormula_iff : forall
    (M : RawPAModel) (tail : nat -> M) level,
  raw_formula_sat M (scons M level tail)
    compactSelectorPackageFormula <->
  RawCompactSelectorPackageAt M tail level.
Proof.
  intros M tail level.
  unfold compactSelectorPackageFormula, RawCompactSelectorPackageAt.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAProvabilityTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros [target [hgraph [certificate hproof]]].
    exists target, certificate. split.
    + exact (proj1
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail level target) hgraph).
    + exact hproof.
  - intros [target [certificate [htarget hproof]]].
    exists target. split.
    + exact (proj2
        (compactRestrictedPAConsistencyFormulaCodeGraph_representation
          M tail level target) htarget).
    + exists certificate. exact hproof.
Qed.

(** Zero needs no new compiler.  Quote the already constructed standard PA
    derivation of [Con_0], and use standard agreement of the compact graph. *)
Theorem raw_compactSelectorPackage_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail,
  RawCompactSelectorPackageAt M tail (raw_zero M).
Proof.
  intros M hPA tail.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (restrictedPAConsistencyFormula 0)
    (PA_BProv_restrictedPAConsistencyFormula 0))
    as [certificate hcertificate].
  exists
    (rawNumeralValue M
      (formulaCode (restrictedPAConsistencyFormula 0))),
    certificate.
  split.
  - change (raw_zero M) with (rawNumeralValue M 0).
    exact (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA 0).
  - exact hcertificate.
Qed.

(** More generally, every standard numeral has a concrete package in every
    PA model.  Both witnesses are the images of actual natural-number codes:
    the exact target code and the quoted proof produced by the established
    fixed-level theorem.  This is stronger bookkeeping than the old
    numeralwise [BProv] statement, though it still does not reach a
    nonstandard carrier element. *)
Theorem raw_compactSelectorPackage_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail (level : nat),
  RawCompactSelectorPackageAt M tail (rawNumeralValue M level).
Proof.
  intros M hPA tail level.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (restrictedPAConsistencyFormula level)
    (PA_BProv_restrictedPAConsistencyFormula level))
    as [certificate hcertificate].
  exists
    (rawNumeralValue M
      (formulaCode (restrictedPAConsistencyFormula level))),
    certificate.
  split.
  - exact (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA level).
  - exact hcertificate.
Qed.

(** This is the exact outstanding construction law.  Unlike a package-level
    closure premise it contains no graph formula and no unused environment:
    all target-code facts are stated through the already proved raw graph.
    A concrete proof compiler must discharge this predicate in every PA
    model. *)
Definition RawRestrictedPAConsistencyProofSuccessor
    (M : RawPAModel) : Prop :=
  forall level target certificate,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    exists nextTarget nextCertificate : M,
      RawRestrictedPAConsistencyFormulaCodeAt
        M (raw_succ M level) nextTarget /\
      RawCodedPAProofOf M nextTarget nextCertificate.

Arguments RawRestrictedPAConsistencyProofSuccessor M : clear implicits.

Definition RawRestrictedPAConsistencyProofSuccessorInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyProofSuccessor M.

(** Target construction is not part of the genuine remaining work.  This
    sharper interface is handed the (necessarily unique) successor target
    and asks only for its proof certificate. *)
Definition RawRestrictedPAConsistencyCertificateSuccessor
    (M : RawPAModel) : Prop :=
  forall level target certificate nextTarget,
    RawRestrictedPAConsistencyFormulaCodeAt M level target ->
    RawCodedPAProofOf M target certificate ->
    RawRestrictedPAConsistencyFormulaCodeAt
      M (raw_succ M level) nextTarget ->
    exists nextCertificate : M,
      RawCodedPAProofOf M nextTarget nextCertificate.

Arguments RawRestrictedPAConsistencyCertificateSuccessor M
  : clear implicits.

Definition RawRestrictedPAConsistencyCertificateSuccessorInAllModels
    : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyCertificateSuccessor M.

(** Totality of the compact target-code construction supplies [nextTarget];
    hence a certificate-only transformer implies the package transformer. *)
Theorem raw_restrictedPAConsistencyProofSuccessor_of_certificate : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAConsistencyCertificateSuccessor M ->
  RawRestrictedPAConsistencyProofSuccessor M.
Proof.
  intros M hPA hcertificateStep level target certificate
    htarget hcertificate.
  destruct (raw_restrictedPAConsistencyFormulaCodeAt_total M hPA
    (raw_succ M level)) as [nextTarget hnextTarget].
  destruct (hcertificateStep level target certificate nextTarget
    htarget hcertificate hnextTarget) as [nextCertificate hnextCertificate].
  exists nextTarget, nextCertificate. split; assumption.
Qed.

(** Conversely, in a PA model the target graph is functional.  Thus the two
    successor interfaces are equivalent there: a package transformer cannot
    hide any extra freedom in its choice of successor target. *)
Theorem raw_restrictedPAConsistencyCertificateSuccessor_of_proof : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAConsistencyProofSuccessor M ->
  RawRestrictedPAConsistencyCertificateSuccessor M.
Proof.
  intros M hPA hproofStep level target certificate nextTarget
    htarget hcertificate hnextTarget.
  destruct (hproofStep level target certificate htarget hcertificate)
    as [selectedTarget [nextCertificate
      [hselectedTarget hnextCertificate]]].
  assert (selectedTarget = nextTarget) as ->.
  {
    exact (raw_restrictedPAConsistencyFormulaCodeAt_functional M hPA
      (raw_succ M level) selectedTarget nextTarget
      hselectedTarget hnextTarget).
  }
  exists nextCertificate. exact hnextCertificate.
Qed.

Theorem raw_restrictedPAConsistencySuccessor_interfaces_equivalent : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawRestrictedPAConsistencyProofSuccessor M <->
  RawRestrictedPAConsistencyCertificateSuccessor M.
Proof.
  intros M hPA. split.
  - exact
      (raw_restrictedPAConsistencyCertificateSuccessor_of_proof M hPA).
  - exact
      (raw_restrictedPAConsistencyProofSuccessor_of_certificate M hPA).
Qed.

(** A reusable standard-target bridge.  The graph may present an arbitrary
    carrier element [target], rather than the canonical quotation selected by
    [raw_restrictedPAConsistencyFormulaCodeAt_standard].  Functionality of
    the graph identifies that supplied target with the canonical code, after
    which the already proved fixed-level PA theorem supplies its certificate.

    Keeping the target abstract is important for downstream compiler stages:
    they should consume the graph witness they already have instead of
    reopening the graph and duplicating this functionality argument. *)
Theorem raw_codedPAProofOf_standardRestrictedPAConsistencyTarget :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (level : nat) target,
  RawRestrictedPAConsistencyFormulaCodeAt M
    (rawNumeralValue M level) target ->
  exists certificate : M,
    RawCodedPAProofOf M target certificate.
Proof.
  intros M hPA level target htarget.
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (restrictedPAConsistencyFormula level)
    (PA_BProv_restrictedPAConsistencyFormula level))
    as [certificate hcertificate].
  assert (target =
      rawNumeralValue M
        (formulaCode (restrictedPAConsistencyFormula level)))
    as ->.
  {
    apply (raw_restrictedPAConsistencyFormulaCodeAt_functional M hPA
      (rawNumeralValue M level) target
      (rawNumeralValue M
        (formulaCode (restrictedPAConsistencyFormula level))) htarget).
    exact (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA level).
  }
  exists certificate. exact hcertificate.
Qed.

(** At every metatheoretic level the certificate successor is already
    constructible.  The proof ignores the incoming certificate and quotes
    the existing standard derivation at the next level.  This theorem cannot
    be iterated over a nonstandard carrier element; it documents exactly why
    the final all-model premise below is stronger than numeralwise
    provability. *)
Theorem raw_restrictedPAConsistencyCertificateSuccessor_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (level : nat) target certificate nextTarget,
  RawRestrictedPAConsistencyFormulaCodeAt M
    (rawNumeralValue M level) target ->
  RawCodedPAProofOf M target certificate ->
  RawRestrictedPAConsistencyFormulaCodeAt M
    (raw_succ M (rawNumeralValue M level)) nextTarget ->
  exists nextCertificate : M,
    RawCodedPAProofOf M nextTarget nextCertificate.
Proof.
  intros M hPA level target certificate nextTarget
    _ _ hnextTarget.
  apply (raw_codedPAProofOf_standardRestrictedPAConsistencyTarget
    M hPA (S level) nextTarget).
  change (raw_succ M (rawNumeralValue M level)) with
    (rawNumeralValue M (S level)) in hnextTarget.
  exact hnextTarget.
Qed.

(** The preceding theorem is often consumed by a traversal whose level is
    already a carrier value.  Make the standardness seam explicit instead of
    forcing every caller to perform the same dependent rewrite by hand.  The
    equality is intentionally an input: this adapter does not decode an
    arbitrary carrier element and therefore makes no claim about
    nonstandard levels. *)
Theorem raw_restrictedPAConsistencyCertificateSuccessor_of_standard_carrier_level :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (standardLevel : nat) (level target certificate nextTarget : M),
  level = rawNumeralValue M standardLevel ->
  RawRestrictedPAConsistencyFormulaCodeAt M level target ->
  RawCodedPAProofOf M target certificate ->
  RawRestrictedPAConsistencyFormulaCodeAt
    M (raw_succ M level) nextTarget ->
  exists nextCertificate : M,
    RawCodedPAProofOf M nextTarget nextCertificate.
Proof.
  intros M hPA standardLevel level target certificate nextTarget hlevel
    htarget hcertificate hnextTarget.
  subst level.
  exact
    (raw_restrictedPAConsistencyCertificateSuccessor_standard
      M hPA standardLevel target certificate nextTarget
      htarget hcertificate hnextTarget).
Qed.

(** The same carrier-level adapter at the package boundary.  It is useful for
    standard-orbit sanity checks: once the input package is at a quoted
    natural, the compact graph supplies the successor target and the fixed
    metatheoretic theorem supplies its proof certificate.  The all-model
    successor remains deliberately separate below. *)
Theorem raw_compactSelectorPackage_successor_of_standard_carrier_level :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (standardLevel : nat) tail,
  RawCompactSelectorPackageAt M tail
    (rawNumeralValue M standardLevel) ->
  RawCompactSelectorPackageAt M tail
    (raw_succ M (rawNumeralValue M standardLevel)).
Proof.
  intros M hPA standardLevel tail
    [target [certificate [htarget hcertificate]]].
  destruct (raw_restrictedPAConsistencyFormulaCodeAt_total M hPA
    (raw_succ M (rawNumeralValue M standardLevel)))
    as [nextTarget hnextTarget].
  destruct
    (raw_restrictedPAConsistencyCertificateSuccessor_standard
      M hPA standardLevel target certificate nextTarget
      htarget hcertificate hnextTarget) as [nextCertificate hnextCertificate].
  exists nextTarget, nextCertificate. split; assumption.
Qed.

(** External induction over [nat] packages the preceding standard-level
    adapter into the ordinary numeralwise family.  The induction variable is
    deliberately a metatheoretic natural: this theorem therefore proves only
    the standard orbit of the compact selector and is not used by
    [raw_compactSelectorPackages_all], whose represented induction reaches
    arbitrary carrier elements.  Keeping this bridge explicit is useful for
    clients that consume the already established numeralwise PA theorem while
    making the nonstandard gap impossible to overlook. *)
Theorem raw_compactSelectorPackages_standard_by_external_induction : forall
    (M : RawPAModel), RawPASatisfies M -> forall tail (standardLevel : nat),
  RawCompactSelectorPackageAt M tail (rawNumeralValue M standardLevel).
Proof.
  intros M hPA tail standardLevel.
  induction standardLevel as [|standardLevel IH].
  - exact (raw_compactSelectorPackage_zero M hPA tail).
  - change (RawCompactSelectorPackageAt M tail
      (raw_succ M (rawNumeralValue M standardLevel))).
    exact (raw_compactSelectorPackage_successor_of_standard_carrier_level
      M hPA standardLevel tail IH).
Qed.

(** A standard-carrier model has no nonstandard level at which the selector
    could fail.  This theorem is intentionally stated with the carrier
    generation property as an explicit premise: a PA model may contain
    nonstandard elements, so external induction alone cannot be promoted to
    the all-carrier result used by [raw_compactSelectorPackages_all]. *)
Definition RawCarrierGeneratedByStandardNumerals (M : RawPAModel) : Prop :=
  forall level : M,
    exists standardLevel : nat,
      level = rawNumeralValue M standardLevel.

Arguments RawCarrierGeneratedByStandardNumerals M : clear implicits.

Theorem raw_compactSelectorPackages_all_of_standard_carrier : forall
    (M : RawPAModel), RawPASatisfies M ->
  RawCarrierGeneratedByStandardNumerals M ->
  forall tail level,
    RawCompactSelectorPackageAt M tail level.
Proof.
  intros M hPA hstandard tail level.
  destruct (hstandard level) as [standardLevel hlevel].
  subst level.
  exact (raw_compactSelectorPackages_standard_by_external_induction
    M hPA tail standardLevel).
Qed.

Lemma raw_compactSelectorPackage_successor : forall
    (M : RawPAModel), RawRestrictedPAConsistencyProofSuccessor M ->
    forall tail level,
      RawCompactSelectorPackageAt M tail level ->
      RawCompactSelectorPackageAt M tail (raw_succ M level).
Proof.
  intros M hstep tail level
    [target [certificate [htarget hcertificate]]].
  exact (hstep level target certificate htarget hcertificate).
Qed.

(** Definable induction is the essential nonstandard step.  Metatheoretic
    recursion over [nat] would establish only the standard instances. *)
Theorem raw_compactSelectorPackages_all : forall
    (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyProofSuccessor M ->
    forall tail level,
      RawCompactSelectorPackageAt M tail level.
Proof.
  intros M hPA hstep tail.
  assert (hall : forall level,
      raw_formula_sat M (scons M level tail)
        compactSelectorPackageFormula).
  {
    apply (raw_definable_induction M hPA
      compactSelectorPackageFormula tail).
    - apply (proj2
        (@raw_sat_compactSelectorPackageFormula_iff
          M tail (raw_zero M))).
      exact (raw_compactSelectorPackage_zero M hPA tail).
    - intros level hlevel.
      apply (proj2
        (@raw_sat_compactSelectorPackageFormula_iff
          M tail (raw_succ M level))).
      apply (raw_compactSelectorPackage_successor M hstep tail level).
      exact (proj1
        (@raw_sat_compactSelectorPackageFormula_iff M tail level)
        hlevel).
  }
  intro level.
  exact (proj1
    (@raw_sat_compactSelectorPackageFormula_iff M tail level)
    (hall level)).
Qed.

(** The requested object-language sentence, using the explicit compact graph:

      forall n, exists c, Code_Con(n,c) and Prov_PA(c).

    [sealPA] makes closure independent of the auxiliary implementation
    variables used by either represented predicate. *)
Definition compactUniformRestrictedPAConsistencyProvabilityBodyFormula
    : formula :=
  pAll compactSelectorPackageFormula.

Definition compactUniformRestrictedPAConsistencyProvabilityFormula
    : formula :=
  Formula.sealPA
    compactUniformRestrictedPAConsistencyProvabilityBodyFormula.

Lemma raw_sat_compactUniformRestrictedPAConsistencyProvabilityBodyFormula_iff
    : forall (M : RawPAModel) (tail : nat -> M),
  raw_formula_sat M tail
    compactUniformRestrictedPAConsistencyProvabilityBodyFormula <->
  forall level : M, RawCompactSelectorPackageAt M tail level.
Proof.
  intros M tail.
  unfold compactUniformRestrictedPAConsistencyProvabilityBodyFormula.
  cbn [raw_formula_sat].
  split; intros hall level.
  - exact (proj1
      (@raw_sat_compactSelectorPackageFormula_iff M tail level)
      (hall level)).
  - exact (proj2
      (@raw_sat_compactSelectorPackageFormula_iff M tail level)
      (hall level)).
Qed.

(** Exact arbitrary-model reading of the sealed sentence.  This theorem is
    useful for checking that the formal target really is
    [forall n, Prov_PA(code(Con_n))], rather than merely its family of
    standard numeral instances. *)
Theorem raw_sat_compactUniformRestrictedPAConsistencyProvabilityFormula_iff
    : forall (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e
    compactUniformRestrictedPAConsistencyProvabilityFormula <->
  forall (tail : nat -> M) (level : M),
    RawCompactSelectorPackageAt M tail level.
Proof.
  intros M e.
  unfold compactUniformRestrictedPAConsistencyProvabilityFormula.
  rewrite raw_formula_sat_sealPA_iff_valid.
  split.
  - intros hall tail level.
    exact (proj1
      (raw_sat_compactUniformRestrictedPAConsistencyProvabilityBodyFormula_iff
        M tail) (hall tail) level).
  - intros hall tail.
    apply (proj2
      (raw_sat_compactUniformRestrictedPAConsistencyProvabilityBodyFormula_iff
        M tail)).
    exact (hall tail).
Qed.

(** The corresponding semantic statement for the sealed object-language
    sentence follows by opening [sealPA] and applying the carrier theorem at
    every ambient tail.  It is useful to compare this honest restricted
    result with [compactUniformRestrictedPAConsistencyProvabilityFormula_raw_valid],
    whose premise must handle arbitrary (including nonstandard) carriers. *)
Theorem compactUniformRestrictedPAConsistencyProvabilityFormula_raw_valid_of_standard_carrier
    : forall (M : RawPAModel), RawPASatisfies M ->
  RawCarrierGeneratedByStandardNumerals M -> forall e,
    raw_formula_sat M e
      compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros M hPA hstandard e.
  unfold compactUniformRestrictedPAConsistencyProvabilityFormula.
  apply raw_formula_sat_sealPA_of_valid.
  intro tail.
  unfold compactUniformRestrictedPAConsistencyProvabilityBodyFormula.
  cbn [raw_formula_sat].
  intro level.
  apply (proj2
    (@raw_sat_compactSelectorPackageFormula_iff M tail level)).
  exact (raw_compactSelectorPackages_all_of_standard_carrier
    M hPA hstandard tail level).
Qed.

Theorem compactUniformRestrictedPAConsistencyProvabilityFormula_sentence :
  Formula.Sentence
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  unfold compactUniformRestrictedPAConsistencyProvabilityFormula.
  apply Formula.sealPA_sentence.
Qed.

Theorem compactUniformRestrictedPAConsistencyProvabilityFormula_raw_valid
    : RawRestrictedPAConsistencyProofSuccessorInAllModels ->
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e
      compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros hstep M hPA e.
  unfold compactUniformRestrictedPAConsistencyProvabilityFormula.
  apply raw_formula_sat_sealPA_of_valid.
  intro tail.
  unfold compactUniformRestrictedPAConsistencyProvabilityBodyFormula.
  cbn [raw_formula_sat].
  intro level.
  apply (proj2
    (@raw_sat_compactSelectorPackageFormula_iff M tail level)).
  exact (raw_compactSelectorPackages_all M hPA
    (hstep M hPA) tail level).
Qed.

(** All code-generation and induction obligations have now been discharged.
    The displayed successor compiler is the only premise of the exact PA
    theorem. *)
Theorem PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula
    : RawRestrictedPAConsistencyProofSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hstep.
  apply PA_BProv_of_raw_valid.
  - exact
      compactUniformRestrictedPAConsistencyProvabilityFormula_sentence.
  - exact
      (compactUniformRestrictedPAConsistencyProvabilityFormula_raw_valid
        hstep).
Qed.

(** Final reduction with no target-code hypothesis: the only premise is the
    nonstandard certificate transformer isolated above. *)
Corollary
    PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula_of_certificate_successor
    : RawRestrictedPAConsistencyCertificateSuccessorInAllModels ->
  Formula.BProv Formula.Ax_s []
    compactUniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hcertificateStep.
  apply PA_BProv_compactUniformRestrictedPAConsistencyProvabilityFormula.
  intros M hPA.
  exact (raw_restrictedPAConsistencyProofSuccessor_of_certificate M hPA
    (hcertificateStep M hPA)).
Qed.

End PABoundedCompactPAUniformProvability.
