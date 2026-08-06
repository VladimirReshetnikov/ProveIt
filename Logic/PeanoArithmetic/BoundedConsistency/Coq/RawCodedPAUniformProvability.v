(**
  The exact uniform-provability target and its missing proof compiler.

  [PA_BProv_restrictedPAConsistencyFormula] is an externally indexed family.
  An object-language universal must instead compute the code of the
  bounded-consistency formula from an object-language level, then exhibit a
  PA proof certificate for that code.  This module defines that sentence and
  proves it conditionally from precisely the arbitrary-model totality law
  that a future arithmetized proof compiler must establish.

  No pointwise use of completeness is hidden in the premise: the compiler
  quantifies over every carrier element of every (possibly nonstandard) raw
  PA model.  The final conditional theorem therefore records the actual gap
  between numeralwise reflection and uniform internal provability.
*)

From Stdlib Require Import List Vector.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAListCoding Require Import ComputableFormula DiophantineFormula.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA.
From BoundedPAConsistency Require Import
  CodedSyntax RawModelCompleteness
  RawCodedRestrictedPAConsistency
  RawCodedRestrictedPAConsistencyTheorem
  RawCodedPAProvability
  RawCodedPAProvabilityRestrictedConsistency.

From Undecidability.L.Datatypes Require Import LNat.
From Undecidability.L.Tactics Require Import Computable.

Import ListNotations.

Module PABoundedRawCodedPAUniformProvability.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PABoundedCodedSyntax.
Import PABoundedRawModelCompleteness.
Import PABoundedRawCodedRestrictedPAConsistency.
Import PABoundedRawCodedRestrictedPAConsistencyTheorem.
Import PABoundedRawCodedPAProvability.
Import PABoundedRawCodedPAProvabilityRestrictedConsistency.

(** The actual Godel-code function used by the requested inner provability
    statement.  It quotes the very same [restrictedPAConsistencyFormula]
    used by the already proved fixed-level theorem. *)
Definition restrictedPAConsistencyFormulaCode (level : nat) : nat :=
  formulaCode (restrictedPAConsistencyFormula level).

(** Output-first graph: free variable 0 is the formula code and free
    variable 1 is the level.  [unaryGraphFormula] names the graph selected by
    the generic Diophantine representation interface.  Its adequacy theorem
    below keeps the required computability certificate explicit; the final
    compiler premise directly states the stronger arbitrary-model behavior
    actually needed by the object theorem. *)
Definition restrictedPAConsistencyFormulaCodeGraph : formula :=
  unaryGraphFormula restrictedPAConsistencyFormulaCode.

Theorem restrictedPAConsistencyFormulaCodeGraph_standard_of_computable :
  computable restrictedPAConsistencyFormulaCode -> forall level,
  Formula.Sat natModel
    (graphEnv (unaryInputs level)
      (restrictedPAConsistencyFormulaCode level))
    restrictedPAConsistencyFormulaCodeGraph.
Proof.
  intros hcomputable level.
  unfold restrictedPAConsistencyFormulaCodeGraph.
  apply (proj2 (@unaryGraphFormula_output_first
    restrictedPAConsistencyFormulaCode
    hcomputable level
    (restrictedPAConsistencyFormulaCode level))).
  reflexivity.
Qed.

(** One arbitrary-model instance of the required uniform proof compiler.
    [tail] is retained because the graph formula was selected through the
    generic Diophantine representation API; requiring all tails states the
    exact environment-independent law consumed by the closed sentence. *)
Definition RawRestrictedPAConsistencyProvabilityCompiler
    (M : RawPAModel) : Prop :=
  forall (tail : nat -> M) (level : M),
    exists target certificate : M,
      raw_formula_sat M
        (scons M target (scons M level tail))
        restrictedPAConsistencyFormulaCodeGraph /\
      RawCodedPAProofOf M target certificate.

Arguments RawRestrictedPAConsistencyProvabilityCompiler M : clear implicits.

Definition RawRestrictedPAConsistencyProvabilityCompilerInAllModels : Prop :=
  forall (M : RawPAModel), RawPASatisfies M ->
    RawRestrictedPAConsistencyProvabilityCompiler M.

(** Written without [sealPA], the body says directly:

      for every level n, there is a code c of Con_n and PA proves c.

    The outer [sealPA] below guarantees closure even if the chosen graph
    representation changes its auxiliary free-variable layout. *)
Definition uniformRestrictedPAConsistencyProvabilityBodyFormula : formula :=
  pAll
    (pEx
      (pAnd
        restrictedPAConsistencyFormulaCodeGraph
        (codedPAProvabilityTermAt (tVar 0)))).

Definition uniformRestrictedPAConsistencyProvabilityFormula : formula :=
  Formula.sealPA uniformRestrictedPAConsistencyProvabilityBodyFormula.

Theorem uniformRestrictedPAConsistencyProvabilityFormula_sentence :
  Formula.Sentence uniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  unfold uniformRestrictedPAConsistencyProvabilityFormula.
  apply Formula.sealPA_sentence.
Qed.

Lemma raw_sat_uniformRestrictedPAConsistencyProvabilityBodyFormula_iff :
  forall (M : RawPAModel) (e : nat -> M),
  raw_formula_sat M e
    uniformRestrictedPAConsistencyProvabilityBodyFormula <->
  forall level : M,
    exists target certificate : M,
      raw_formula_sat M
        (scons M target (scons M level e))
        restrictedPAConsistencyFormulaCodeGraph /\
      RawCodedPAProofOf M target certificate.
Proof.
  intros M e.
  unfold uniformRestrictedPAConsistencyProvabilityBodyFormula.
  cbn [raw_formula_sat].
  setoid_rewrite raw_sat_codedPAProvabilityTermAt_iff.
  cbn [raw_term_eval scons].
  split; intros hlevel level.
  - destruct (hlevel level) as [target [hgraph hprovable]].
    destruct hprovable as [certificate hcertificate].
    exists target, certificate. split; assumption.
  - destruct (hlevel level) as
      [target [certificate [hgraph hcertificate]]].
    exists target. split; [exact hgraph |].
    exists certificate. exact hcertificate.
Qed.

Theorem uniformRestrictedPAConsistencyProvabilityFormula_raw_valid_of_compiler :
  RawRestrictedPAConsistencyProvabilityCompilerInAllModels ->
  forall (M : RawPAModel), RawPASatisfies M -> forall e,
    raw_formula_sat M e
      uniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intros hcompiler M hPA e.
  unfold uniformRestrictedPAConsistencyProvabilityFormula.
  apply raw_formula_sat_sealPA_of_valid.
  intro tail.
  apply (proj2
    (@raw_sat_uniformRestrictedPAConsistencyProvabilityBodyFormula_iff
      M tail)).
  exact (hcompiler M hPA tail).
Qed.

(** Conditional object theorem.  Discharging the sole premise requires an
    explicit PA-verifiable uniform proof-code compiler; the existing
    pointwise semantic-completeness argument does not discharge it. *)
Theorem PA_BProv_uniformRestrictedPAConsistencyProvabilityFormula_of_compiler :
  RawRestrictedPAConsistencyProvabilityCompilerInAllModels ->
  Formula.BProv Formula.Ax_s []
    uniformRestrictedPAConsistencyProvabilityFormula.
Proof.
  intro hcompiler.
  apply PA_BProv_of_raw_valid.
  - apply uniformRestrictedPAConsistencyProvabilityFormula_sentence.
  - exact
      (uniformRestrictedPAConsistencyProvabilityFormula_raw_valid_of_compiler
        hcompiler).
Qed.

(** The compiler premise is also necessary.  This converse is a useful
    boundary audit: an object-level proof of the sealed uniform sentence is
    semantically true in every raw PA model, and opening [sealPA] exposes the
    very same arbitrary-carrier witness package demanded by the compiler.

    In particular, this theorem does not manufacture the missing compiler.
    It proves that replacing the compiler premise by the headline theorem
    would be circular: the two propositions have exactly the same strength
    for this concrete graph representation. *)
Theorem raw_restrictedPAConsistencyProvabilityCompiler_of_BProv :
  Formula.BProv Formula.Ax_s []
    uniformRestrictedPAConsistencyProvabilityFormula ->
  RawRestrictedPAConsistencyProvabilityCompilerInAllModels.
Proof.
  intros hprov M hPA tail.
  pose proof (raw_sat_of_BProv_axs M
    uniformRestrictedPAConsistencyProvabilityFormula hPA hprov tail)
    as hsealed.
  pose proof (proj1
    (raw_formula_sat_sealPA_iff_valid M
      uniformRestrictedPAConsistencyProvabilityBodyFormula tail)
    hsealed) as hbody.
  apply (proj1
    (@raw_sat_uniformRestrictedPAConsistencyProvabilityBodyFormula_iff
      M tail)).
  exact (hbody tail).
Qed.

(** Exact characterization of the remaining Coq obligation.  The forward
    direction is the semantic converse above; the reverse direction is the
    constructive reduction proved earlier. *)
Theorem PA_BProv_uniformRestrictedPAConsistencyProvabilityFormula_iff_compiler :
  Formula.BProv Formula.Ax_s []
      uniformRestrictedPAConsistencyProvabilityFormula <->
    RawRestrictedPAConsistencyProvabilityCompilerInAllModels.
Proof.
  split.
  - exact raw_restrictedPAConsistencyProvabilityCompiler_of_BProv.
  - exact PA_BProv_uniformRestrictedPAConsistencyProvabilityFormula_of_compiler.
Qed.

(** The currently available standard-instance derivability condition.  This
    theorem is useful evidence for every numeral, but its [forall] remains
    metatheoretic and therefore is not the conditional theorem's compiler
    premise. *)
Corollary PA_BProv_each_standard_restrictedPAConsistencyProvability :
  forall level,
    Formula.BProv Formula.Ax_s []
      (restrictedPAConsistencyProvabilityFormula level).
Proof.
  exact PA_BProv_restrictedPAConsistencyProvabilityFormula.
Qed.

End PABoundedRawCodedPAUniformProvability.
