(**
  Standard-level selector packages.

  The compact uniform sentence uses a graph whose input is an arbitrary
  carrier element.  This file records the stronger *standard-instance*
  fact in the same package shape, but with the output graph specialized to
  the canonical equality graph for [Con_level].  It is useful when testing
  later compiler stages: the returned witness is simultaneously a code of
  the target formula and a checked PA proof certificate for that code.

  The level in this module is deliberately metatheoretic.  Nothing here
  converts the standard family into the missing nonstandard successor; that
  conversion remains the exact proof-producing boundary isolated by
  [CompactPAUniformProvability].
*)

From Stdlib Require Import List Lia.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF PAHFRawSemantics.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax
  RawModelCompleteness
  RawCodedSyntaxConstructors
  RawCodedStandardClosedFormulaCodeGraph
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyTheorem
  RawCodedRestrictedPAProof
  RawCodedPAProvability
  CompactPAUniformProvability
  CompactRestrictedPAConsistencyFormulaCodeGraph.

Import ListNotations.

Module PABoundedRawCodedPAStandardSelectorPackage.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedStandardClosedFormulaCodeGraph.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyTheorem.
Import PABoundedRawCodedRestrictedPAProof.
Import PABoundedRawCodedPAProvability.
Import PABoundedCompactPAUniformProvability.
Import PABoundedCompactRestrictedPAConsistencyFormulaCodeGraph.

(** The package relation for one fixed standard level.  The existential
    binder captures the proof certificate; the equality graph forces its
    target to be the code of the corresponding consistency formula. *)
Definition standardSelectorPackageBodyFormula (level : nat) : formula :=
  pEx
    (pAnd
      (standardClosedFormulaCodeGraph
        (restrictedPAConsistencyFormula level))
      (codedPAProvabilityTermAt (tVar 0))).

Definition standardSelectorPackageFormula (level : nat) : formula :=
  Formula.sealPA (standardSelectorPackageBodyFormula level).

Lemma standardSelectorPackageFormula_sentence : forall level,
  Formula.Sentence (standardSelectorPackageFormula level).
Proof.
  intro level. unfold standardSelectorPackageFormula.
  apply Formula.sealPA_sentence.
Qed.

(** The unsealed body has the direct existential reading used below. *)
Lemma raw_sat_standardSelectorPackageBodyFormula_iff : forall
    (M : RawPAModel) (e : nat -> M) level,
  raw_formula_sat M e (standardSelectorPackageBodyFormula level) <->
  exists target certificate : M,
    target = rawQuotedFormulaCode M
      (restrictedPAConsistencyFormula level) /\
    RawCodedPAProofOf M target certificate.
Proof.
  intros M e level.
  unfold standardSelectorPackageBodyFormula,
    standardClosedFormulaCodeGraph.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAProvabilityTermAt_iff.
  cbn [raw_term_eval scons].
  split.
  - intros [target [hgraph [certificate hcertificate]]].
    exists target, certificate. split.
    + cbn [raw_formula_sat raw_term_eval scons].
      exact hgraph.
    + exact hcertificate.
  - intros [target [certificate [htarget hcertificate]]].
    exists target. split.
    + cbn [raw_formula_sat raw_term_eval scons].
      rewrite raw_term_eval_numeral.
      exact htarget.
    + exists certificate. exact hcertificate.
Qed.

(** Opening the existential package gives exactly the expected carrier
    witnesses.  The equality graph is reduced directly rather than through
    the two-input graph API, since this formula has no level parameter. *)
Lemma raw_sat_standardSelectorPackageFormula_iff : forall
    (M : RawPAModel) (e : nat -> M) level,
  raw_formula_sat M e (standardSelectorPackageFormula level) <->
  exists target certificate : M,
    target = rawQuotedFormulaCode M
      (restrictedPAConsistencyFormula level) /\
    RawCodedPAProofOf M target certificate.
Proof.
  intros M e level.
  unfold standardSelectorPackageFormula.
  rewrite raw_formula_sat_sealPA_iff_valid.
  split.
  - intro hvalid.
    apply (proj1
      (raw_sat_standardSelectorPackageBodyFormula_iff M e level)).
    exact (hvalid e).
  - intros hpackage e'.
    apply (proj2
      (raw_sat_standardSelectorPackageBodyFormula_iff M e' level)).
    exact hpackage.
Qed.

(** Every standard package is an actual theorem of PA.  The proof is
    obtained by quoting the already verified fixed-level consistency
    derivation; no uniform or nonstandard compiler premise occurs. *)
Theorem PA_BProv_standardSelectorPackageFormula : forall level,
  Formula.BProv Formula.Ax_s [] (standardSelectorPackageFormula level).
Proof.
  intro level.
  apply PA_BProv_of_raw_valid.
  - apply standardSelectorPackageFormula_sentence.
  - intros M hPA e.
    apply (proj2
      (raw_sat_standardSelectorPackageFormula_iff M e level)).
    destruct (raw_codedPAProofOf_of_BProv M hPA
      (restrictedPAConsistencyFormula level)
      (PA_BProv_restrictedPAConsistencyFormula level)) as
      [certificate hcertificate].
    exists (rawNumeralValue M
      (formulaCode (restrictedPAConsistencyFormula level))), certificate.
    split.
    + rewrite rawQuotedFormulaCode_standard by exact hPA.
      reflexivity.
    + exact hcertificate.
Qed.

(** The corresponding raw package is available in every PA model, with the
    canonical quoted target as its first witness. *)
Corollary raw_standardSelectorPackage_standard : forall
    (M : RawPAModel), RawPASatisfies M -> forall level e,
  raw_formula_sat M e (standardSelectorPackageFormula level).
Proof.
  intros M hPA level e.
  apply (proj2 (raw_sat_standardSelectorPackageFormula_iff M e level)).
  destruct (raw_codedPAProofOf_of_BProv M hPA
    (restrictedPAConsistencyFormula level)
    (PA_BProv_restrictedPAConsistencyFormula level)) as
    [certificate hcertificate].
  exists (rawNumeralValue M
    (formulaCode (restrictedPAConsistencyFormula level))), certificate.
  split.
  - rewrite rawQuotedFormulaCode_standard by exact hPA.
    reflexivity.
  - exact hcertificate.
Qed.

(** The compact graph and the standard equality graph agree at standard
    levels.  Functionality of the compact target graph supplies the reverse
    direction; no choice of a nonstandard code is involved. *)
Lemma raw_compactRestrictedPAConsistencyGraph_standard_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall
      (tail : nat -> M) (level : nat) target,
  raw_formula_sat M
    (scons M target (scons M (rawNumeralValue M level) tail))
    compactRestrictedPAConsistencyFormulaCodeGraph <->
  target = rawQuotedFormulaCode M
    (restrictedPAConsistencyFormula level).
Proof.
  intros M hPA tail level target.
  rewrite (compactRestrictedPAConsistencyFormulaCodeGraph_representation
    M tail (rawNumeralValue M level) target).
  split.
  - intro htarget.
    assert (hcanonical : RawRestrictedPAConsistencyFormulaCodeAt M
        (rawNumeralValue M level)
        (rawQuotedFormulaCode M
          (restrictedPAConsistencyFormula level))).
    {
      exact (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA level).
    }
    exact (raw_restrictedPAConsistencyFormulaCodeAt_functional M hPA
      (rawNumeralValue M level) target
      (rawQuotedFormulaCode M
        (restrictedPAConsistencyFormula level)) htarget hcanonical).
  - intro htarget.
    subst target.
    exact (raw_restrictedPAConsistencyFormulaCodeAt_standard M hPA level).
Qed.

(** At a standard level, the compact selector package is propositionally
    equivalent to the explicit equality-graph package added above.  This is
    the precise bridge between the public compact sentence and the
    numeralwise selector API. *)
Theorem raw_compactSelectorPackage_standard_iff_standardSelectorPackage :
  forall (M : RawPAModel), RawPASatisfies M -> forall
    (tail : nat -> M) (level : nat),
  raw_formula_sat M
    (scons M (rawNumeralValue M level) tail)
    compactSelectorPackageFormula <->
  raw_formula_sat M tail (standardSelectorPackageFormula level).
Proof.
  intros M hPA tail level.
  rewrite (raw_sat_compactSelectorPackageFormula_iff M tail
    (rawNumeralValue M level)).
  rewrite (raw_sat_standardSelectorPackageFormula_iff M tail level).
  split.
  - intros [target [certificate [hgraph hcertificate]]].
    exists target, certificate. split.
    + exact (proj1
        (raw_compactRestrictedPAConsistencyGraph_standard_iff
          M hPA tail level target) hgraph).
    + exact hcertificate.
  - intros [target [certificate [htarget hcertificate]]].
    exists target, certificate. split.
    + exact (proj2
        (raw_compactRestrictedPAConsistencyGraph_standard_iff
          M hPA tail level target) htarget).
    + exact hcertificate.
Qed.

End PABoundedRawCodedPAStandardSelectorPackage.
