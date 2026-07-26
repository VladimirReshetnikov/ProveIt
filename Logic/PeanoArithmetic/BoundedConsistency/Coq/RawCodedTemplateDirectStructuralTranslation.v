(**
  Direct structural template translation over nonstandard opaque formulas.

  A metatheoretic [RawFormulaShiftTree] is ideal for ordinary finite formula
  skeletons, but an opaque template atom may denote a genuinely nonstandard
  formula code and therefore cannot in general be decoded into such a tree.
  This module gives the applicable interface: opaque leaves supply represented
  operation traces directly, and the finite surrounding template structure is
  assembled with trace concatenation.

  Terms remain finite template syntax and carry exact shift/substitution atoms.
  Formula recursion uses generic constructor compositionality, so no carrier
  formula is decoded and no atomic-adequacy claim is promoted to an operation
  theorem.
*)

From Stdlib Require Import List.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization
  RawCodedFormulaOperationTraceConcatenation
  RawCodedFormulaOperationCompositionality
  RawCodedTemplateSyntax RawCodedTemplateProofCompiler
  RawCodedTemplateStructuralTranslation.

Module PABoundedRawCodedTemplateDirectStructuralTranslation.

Import ListNotations.
Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.
Import PABoundedRawCodedFormulaOperationTraceConcatenation.
Import PABoundedRawCodedFormulaOperationCompositionality.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedTemplateStructuralTranslation.

(** Exact inputs at the only nontransparent leaves.  In contrast with
    [RawCodedTemplateStructuralInputs], opaque formulas provide relations,
    not metatheoretic trees. *)
Record RawCodedTemplateDirectStructuralInputs (M : RawPAModel) : Type := {
  rawDirectTemplateSymbols : RawCodedTemplateStructuralSymbols M;

  rawDirectTemplateTermShiftAt : forall depth input,
    RawCodedTermShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawStructuralTemplateTermWith M rawDirectTemplateSymbols input)
      (rawStructuralTemplateTermWith M rawDirectTemplateSymbols
        (templateTermRename (templateShiftRenamingAt depth) input));

  rawDirectTemplateTermOpeningAt : forall depth replacement input,
    RawCodedFormulaSubstitutionAtom M
      (rawStructuralTemplateTermWith M rawDirectTemplateSymbols replacement)
      (rawNumeralValue M depth)
      (rawStructuralTemplateTermWith M rawDirectTemplateSymbols input)
      (rawStructuralTemplateTermWith M rawDirectTemplateSymbols
        (templateTermSubst
          (templateOpeningSubstAt depth replacement) input));

  rawDirectTemplateOpaqueShiftAt : forall depth predicate arguments,
    RawCodedFormulaShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawStructuralTemplateFormulaWith M rawDirectTemplateSymbols
        (tfOpaque predicate arguments))
      (rawStructuralTemplateFormulaWith M rawDirectTemplateSymbols
        (templateFormulaRename (templateShiftRenamingAt depth)
          (tfOpaque predicate arguments)));

  rawDirectTemplateOpaqueOpeningAt : forall
      depth replacement predicate arguments,
    RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
      (rawStructuralTemplateTermWith M rawDirectTemplateSymbols replacement)
      (rawNumeralValue M depth)
      (rawStructuralTemplateFormulaWith M rawDirectTemplateSymbols
        (tfOpaque predicate arguments))
      (rawStructuralTemplateFormulaWith M rawDirectTemplateSymbols
        (templateFormulaSubst
          (templateOpeningSubstAt depth replacement)
          (tfOpaque predicate arguments)))
}.

Arguments rawDirectTemplateSymbols {M} _.
Arguments rawDirectTemplateTermShiftAt {M} _ _ _.
Arguments rawDirectTemplateTermOpeningAt {M} _ _ _ _.
Arguments rawDirectTemplateOpaqueShiftAt {M} _ _ _ _.
Arguments rawDirectTemplateOpaqueOpeningAt {M} _ _ _ _ _.

Definition rawDirectTemplateTerm {M : RawPAModel}
    (inputs : RawCodedTemplateDirectStructuralInputs M) :=
  rawStructuralTemplateTermWith M (rawDirectTemplateSymbols inputs).

Definition rawDirectTemplateFormula {M : RawPAModel}
    (inputs : RawCodedTemplateDirectStructuralInputs M) :=
  rawStructuralTemplateFormulaWith M (rawDirectTemplateSymbols inputs).

Arguments rawDirectTemplateTerm {M} _ _.
Arguments rawDirectTemplateFormula {M} _ _.

(** ------------------------------------------------------------------
    Direct represented shift, by finite recursion only on template syntax. *)

Theorem rawDirectTemplateFormula_shiftAt : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M)
      depth formula,
  RawCodedFormulaShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs formula)
    (rawDirectTemplateFormula inputs
      (templateFormulaRename (templateShiftRenamingAt depth) formula)).
Proof.
  intros M hPA inputs depth formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth.
  - change (RawCodedFormulaShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawFormulaEqCode M
        (rawDirectTemplateTerm inputs left)
        (rawDirectTemplateTerm inputs right))
      (rawFormulaEqCode M
        (rawDirectTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) left))
        (rawDirectTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) right)))).
    apply (raw_codedFormulaShift_of_valid_tree M hPA
      (rawNumeralValue M 1)
      (RFSTEq M (rawNumeralValue M depth)
        (rawDirectTemplateTerm inputs left)
        (rawDirectTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) left))
        (rawDirectTemplateTerm inputs right)
        (rawDirectTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) right)))).
    split; apply rawDirectTemplateTermShiftAt.
  - change (RawCodedFormulaShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawFormulaBotCode M) (rawFormulaBotCode M)).
    apply (raw_codedFormulaShift_of_valid_tree M hPA
      (rawNumeralValue M 1) (RFSTBot M (rawNumeralValue M depth))).
    exact I.
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaRename].
    eapply (raw_codedFormulaShift_binary_composition M hPA RFSBImp).
    + exact (IHleft depth).
    + exact (IHright depth).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaRename].
    eapply (raw_codedFormulaShift_binary_composition M hPA RFSBAnd).
    + exact (IHleft depth).
    + exact (IHright depth).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaRename].
    eapply (raw_codedFormulaShift_binary_composition M hPA RFSBOr).
    + exact (IHleft depth).
    + exact (IHright depth).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaRename].
    replace
      (templateFormulaRename
        (templateUpRenaming (templateShiftRenamingAt depth)) body)
      with
      (templateFormulaRename (templateShiftRenamingAt (S depth)) body).
    2:{ symmetry. apply templateFormulaRename_shift_succ. }
    eapply (raw_codedFormulaShift_unary_composition M hPA RFSUAll).
    exact (IHbody (S depth)).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaRename].
    replace
      (templateFormulaRename
        (templateUpRenaming (templateShiftRenamingAt depth)) body)
      with
      (templateFormulaRename (templateShiftRenamingAt (S depth)) body).
    2:{ symmetry. apply templateFormulaRename_shift_succ. }
    eapply (raw_codedFormulaShift_unary_composition M hPA RFSUEx).
    exact (IHbody (S depth)).
  - exact (rawDirectTemplateOpaqueShiftAt inputs
      depth predicate arguments).
Qed.

(** ------------------------------------------------------------------
    Direct represented capture-avoiding opening. *)

Theorem rawDirectTemplateFormula_openingAt : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M)
      depth replacement formula,
  RawCodedFormulaOperation M (RawCodedFormulaSubstitutionAtom M)
    (rawDirectTemplateTerm inputs replacement)
    (rawNumeralValue M depth)
    (rawDirectTemplateFormula inputs formula)
    (rawDirectTemplateFormula inputs
      (templateFormulaSubst
        (templateOpeningSubstAt depth replacement) formula)).
Proof.
  intros M hPA inputs depth replacement formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth.
  - change (RawCodedFormulaOperation M
      (RawCodedFormulaSubstitutionAtom M)
      (rawDirectTemplateTerm inputs replacement)
      (rawNumeralValue M depth)
      (rawFormulaEqCode M
        (rawDirectTemplateTerm inputs left)
        (rawDirectTemplateTerm inputs right))
      (rawFormulaEqCode M
        (rawDirectTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) left))
        (rawDirectTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) right)))).
    apply (raw_codedFormulaSubstitution_of_valid_tree M hPA
      (rawDirectTemplateTerm inputs replacement)
      (RFSTEq M (rawNumeralValue M depth)
        (rawDirectTemplateTerm inputs left)
        (rawDirectTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) left))
        (rawDirectTemplateTerm inputs right)
        (rawDirectTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) right)))).
    split; apply rawDirectTemplateTermOpeningAt.
  - change (RawCodedFormulaOperation M
      (RawCodedFormulaSubstitutionAtom M)
      (rawDirectTemplateTerm inputs replacement)
      (rawNumeralValue M depth)
      (rawFormulaBotCode M) (rawFormulaBotCode M)).
    apply (raw_codedFormulaSubstitution_of_valid_tree M hPA
      (rawDirectTemplateTerm inputs replacement)
      (RFSTBot M (rawNumeralValue M depth))).
    exact I.
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaSubst].
    eapply (raw_codedFormulaSubstitution_binary_composition
      M hPA (rawDirectTemplateTerm inputs replacement) RFSBImp).
    + exact (IHleft depth).
    + exact (IHright depth).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaSubst].
    eapply (raw_codedFormulaSubstitution_binary_composition
      M hPA (rawDirectTemplateTerm inputs replacement) RFSBAnd).
    + exact (IHleft depth).
    + exact (IHright depth).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaSubst].
    eapply (raw_codedFormulaSubstitution_binary_composition
      M hPA (rawDirectTemplateTerm inputs replacement) RFSBOr).
    + exact (IHleft depth).
    + exact (IHright depth).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaSubst templateOpeningSubstAt].
    eapply (raw_codedFormulaSubstitution_unary_composition
      M hPA (rawDirectTemplateTerm inputs replacement) RFSUAll).
    exact (IHbody (S depth)).
  - cbn [rawDirectTemplateFormula rawStructuralTemplateFormulaWith
      templateFormulaSubst templateOpeningSubstAt].
    eapply (raw_codedFormulaSubstitution_unary_composition
      M hPA (rawDirectTemplateTerm inputs replacement) RFSUEx).
    exact (IHbody (S depth)).
  - exact (rawDirectTemplateOpaqueOpeningAt inputs
      depth replacement predicate arguments).
Qed.

(** Root-level relations expected by the finite proof-tree compiler. *)
Corollary rawDirectTemplateFormula_shift : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M) formula,
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawDirectTemplateFormula inputs formula)
    (rawDirectTemplateFormula inputs (templateFormulaRename S formula)).
Proof.
  intros M hPA inputs formula.
  pose proof (rawDirectTemplateFormula_shiftAt M hPA inputs 0 formula)
    as hshift.
  cbn [templateShiftRenamingAt rawNumeralValue] in hshift.
  exact hshift.
Qed.

Corollary rawDirectTemplateFormula_open : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateDirectStructuralInputs M)
      body replacement,
  RawCodedFormulaSingleSubstitution M
    (rawDirectTemplateTerm inputs replacement)
    (rawDirectTemplateFormula inputs body)
    (rawDirectTemplateFormula inputs
      (templateFormulaOpen replacement body)).
Proof.
  intros M hPA inputs body replacement.
  pose proof (rawDirectTemplateFormula_openingAt
    M hPA inputs 0 replacement body) as hopen.
  cbn [rawNumeralValue templateOpeningSubstAt] in hopen.
  unfold templateFormulaOpen.
  exact hopen.
Qed.

(** Applicable compiler translation: direct opaque traces, finite structural
    assembly, and no metatheoretic decoding of the opaque formula code. *)
Definition rawDirectStructuralTemplateTranslation
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateDirectStructuralInputs M)
    : RawCodedTemplateTranslation M.
Proof.
  refine {| rawTemplateTerm := rawDirectTemplateTerm inputs;
    rawTemplateFormula := rawDirectTemplateFormula inputs |}.
  - reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - apply rawDirectTemplateFormula_shift. exact hPA.
  - apply rawDirectTemplateFormula_open. exact hPA.
Defined.

Arguments rawDirectStructuralTemplateTranslation M _ _ : clear implicits.

End PABoundedRawCodedTemplateDirectStructuralTranslation.
