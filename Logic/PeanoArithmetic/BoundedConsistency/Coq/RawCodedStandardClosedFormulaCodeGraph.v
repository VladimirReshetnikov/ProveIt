(**
  Output-first graphs for fixed standard formula codes.

  A dynamic field often has a genuinely recursive positive orbit but a fixed
  metatheoretic formula at level zero.  The graph below is the canonical base
  branch for that situation.  It is read under

      output :: level :: tail

  and ignores [level] and [tail].  Its output is the internal numeral for the
  exact Goedel code of [phi].  In a PA model this numeral agrees with the
  structural carrier quotation [rawQuotedFormulaCode M phi].

  Although the intended inputs are closed formulas, coding itself does not
  use closedness.  Consequently no redundant [Sentence phi] hypothesis is
  imposed on the representation or totality theorems.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  CodedSyntax RawCodedSyntaxConstructors RawCodedPAProvability
  RawCodedDynamicLocalFieldGraph.

Module PABoundedRawCodedStandardClosedFormulaCodeGraph.

Import ListNotations.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedCodedSyntax.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedDynamicLocalFieldGraph.

(** Output-first equality graph for the fixed external formula [phi]. *)
Definition standardClosedFormulaCodeGraph (phi : formula) : formula :=
  pEq (tVar 0) (Term.numeral (formulaCode phi)).

(** Its transparent carrier-level relation. *)
Definition RawStandardClosedFormulaCodeAt (M : RawPAModel)
    (phi : formula) (output : M) : Prop :=
  output = rawQuotedFormulaCode M phi.

Arguments RawStandardClosedFormulaCodeAt M phi output : clear implicits.

(** Before using any arithmetic laws, the graph returns exactly the model
    numeral whose metatheoretic value is [formulaCode phi]. *)
Theorem standardClosedFormulaCodeGraph_numeral_representation : forall
    (M : RawPAModel) phi tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (standardClosedFormulaCodeGraph phi) <->
  output = rawNumeralValue M (formulaCode phi).
Proof.
  intros M phi tail level output.
  unfold standardClosedFormulaCodeGraph.
  cbn [raw_formula_sat raw_term_eval scons].
  rewrite raw_term_eval_numeral. reflexivity.
Qed.

(** Exact arbitrary-PA-model representation by the structural quotation. *)
Theorem standardClosedFormulaCodeGraph_representation : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi tail level output,
  raw_formula_sat M (scons M output (scons M level tail))
    (standardClosedFormulaCodeGraph phi) <->
  RawStandardClosedFormulaCodeAt M phi output.
Proof.
  intros M hPA phi tail level output.
  rewrite standardClosedFormulaCodeGraph_numeral_representation.
  unfold RawStandardClosedFormulaCodeAt.
  rewrite (rawQuotedFormulaCode_standard M hPA phi).
  reflexivity.
Qed.

(** Uniform totality is already law-free because the numeral itself is a
    canonical witness. *)
Theorem standardClosedFormulaCodeGraph_raw_total : forall
    (M : RawPAModel) phi tail level,
  exists output : M,
    raw_formula_sat M (scons M output (scons M level tail))
      (standardClosedFormulaCodeGraph phi).
Proof.
  intros M phi tail level.
  exists (rawNumeralValue M (formulaCode phi)).
  apply (proj2
    (standardClosedFormulaCodeGraph_numeral_representation
      M phi tail level _)).
  reflexivity.
Qed.

(** The exact component-totality interface expected of the base branch of
    [dynamicLocalFieldGraph]. *)
Corollary standardClosedFormulaCodeGraph_dynamic_base_total : forall
    (M : RawPAModel) phi,
  RawDynamicLocalBaseGraphTotal M (standardClosedFormulaCodeGraph phi).
Proof.
  intros M phi tail.
  exact (standardClosedFormulaCodeGraph_raw_total
    M phi tail (raw_zero M)).
Qed.

(** At level zero, graph membership is exactly equality with the quoted
    formula code. *)
Theorem standardClosedFormulaCodeGraph_zero_iff : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi tail output,
  raw_formula_sat M
    (scons M output (scons M (raw_zero M) tail))
    (standardClosedFormulaCodeGraph phi) <->
  output = rawQuotedFormulaCode M phi.
Proof.
  intros M hPA phi tail output.
  exact (standardClosedFormulaCodeGraph_representation
    M hPA phi tail (raw_zero M) output).
Qed.

(** Canonical standard zero witness, suitable for master-base packages that
    require the graph assertion rather than only existential totality. *)
Corollary standardClosedFormulaCodeGraph_zero : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi tail,
  raw_formula_sat M
    (scons M (rawQuotedFormulaCode M phi)
      (scons M (raw_zero M) tail))
    (standardClosedFormulaCodeGraph phi).
Proof.
  intros M hPA phi tail.
  apply (proj2
    (standardClosedFormulaCodeGraph_zero_iff M hPA phi tail _)).
  reflexivity.
Qed.

(** A standard PA derivation can be quoted together with the graph-selected
    output.  The same statement works at every supplied level, although its
    primary use is the zero branch of a dynamic splice. *)
Theorem raw_standardClosedFormulaCodeGraph_proof_of_BProv : forall
    (M : RawPAModel), RawPASatisfies M -> forall phi,
  Formula.BProv Formula.Ax_s [] phi ->
  forall tail level,
  exists output certificate : M,
    raw_formula_sat M (scons M output (scons M level tail))
      (standardClosedFormulaCodeGraph phi) /\
    RawCodedPAProofOf M output certificate.
Proof.
  intros M hPA phi hprov tail level.
  destruct (raw_codedPAProofOf_of_BProv M hPA phi hprov)
    as [certificate hcertificate].
  exists (rawQuotedFormulaCode M phi), certificate.
  split.
  - apply (proj2
      (standardClosedFormulaCodeGraph_representation
        M hPA phi tail level _)).
    reflexivity.
  - rewrite (rawQuotedFormulaCode_standard M hPA phi).
    exact hcertificate.
Qed.

End PABoundedRawCodedStandardClosedFormulaCodeGraph.
