(**
  Structural specialization of model-coded proof templates.

  [RawCodedTemplateSyntax] separates honest, finite metatheoretic syntax from
  the possibly nonstandard carrier values inserted into it.  This module
  gives the corresponding concrete translation into a [RawPAModel].  Every
  ordinary term/formula constructor is translated by its public raw-code
  constructor.  Only named parameters and opaque predicate applications are
  supplied by the client.

  The subtle part is compatibility with represented shift and substitution.
  It would be unsound to infer either operation merely from an atomic
  adequacy statement: adequacy does not imply a free-variable bound.  The
  input record therefore asks for exact depth-indexed term atoms and for an
  explicit finite operation tree at each opaque formula leaf.  Structural
  recursion then grafts those leaves beneath the transparent connectives and
  quantifiers.  The generic finite-tree realizers turn the resulting valid
  trees into the full [RawCodedFormulaShift] and
  [RawCodedFormulaSingleSubstitution] traces required by the proof compiler.
*)

From Stdlib Require Import List Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax RawCodedTemplateProofCompiler
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedFormulaShiftTreeRealization
  RawCodedFormulaOperationTreeRealization.

Import ListNotations.

Module PABoundedRawCodedTemplateStructuralTranslation.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateProofCompiler.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedFormulaShiftTreeRealization.
Import PABoundedRawCodedFormulaOperationTreeRealization.

(** ------------------------------------------------------------------
    Transparent constructor translation. *)

(** The client chooses codes only for the two genuinely opaque pieces of
    template syntax.  An opaque predicate receives the already translated
    argument codes, so its arity and predicate-name discipline remain fully
    general. *)
Record RawCodedTemplateStructuralSymbols (M : RawPAModel) : Type := {
  rawStructuralTemplateParameterCode : TemplateParameterName -> M;
  rawStructuralTemplateOpaqueCode : TemplatePredicateName -> list M -> M
}.

Arguments rawStructuralTemplateParameterCode {M} _ _.
Arguments rawStructuralTemplateOpaqueCode {M} _ _ _.

Fixpoint rawStructuralTemplateTermWith (M : RawPAModel)
    (symbols : RawCodedTemplateStructuralSymbols M)
    (input : TemplateTerm) : M :=
  match input with
  | ttVar index => rawTermVarCode M (rawNumeralValue M index)
  | ttParameter name => rawStructuralTemplateParameterCode symbols name
  | ttZero => rawTermZeroCode M
  | ttSucc child =>
      rawTermSuccCode M (rawStructuralTemplateTermWith M symbols child)
  | ttAdd lhs rhs =>
      rawTermAddCode M
        (rawStructuralTemplateTermWith M symbols lhs)
        (rawStructuralTemplateTermWith M symbols rhs)
  | ttMul lhs rhs =>
      rawTermMulCode M
        (rawStructuralTemplateTermWith M symbols lhs)
        (rawStructuralTemplateTermWith M symbols rhs)
  end.

Definition rawStructuralTemplateTermsWith (M : RawPAModel)
    (symbols : RawCodedTemplateStructuralSymbols M)
    (inputs : list TemplateTerm) : list M :=
  map (rawStructuralTemplateTermWith M symbols) inputs.

Fixpoint rawStructuralTemplateFormulaWith (M : RawPAModel)
    (symbols : RawCodedTemplateStructuralSymbols M)
    (input : TemplateFormula) : M :=
  match input with
  | tfEq lhs rhs =>
      rawFormulaEqCode M
        (rawStructuralTemplateTermWith M symbols lhs)
        (rawStructuralTemplateTermWith M symbols rhs)
  | tfBot => rawFormulaBotCode M
  | tfImp lhs rhs =>
      rawFormulaImpCode M
        (rawStructuralTemplateFormulaWith M symbols lhs)
        (rawStructuralTemplateFormulaWith M symbols rhs)
  | tfAnd lhs rhs =>
      rawFormulaAndCode M
        (rawStructuralTemplateFormulaWith M symbols lhs)
        (rawStructuralTemplateFormulaWith M symbols rhs)
  | tfOr lhs rhs =>
      rawFormulaOrCode M
        (rawStructuralTemplateFormulaWith M symbols lhs)
        (rawStructuralTemplateFormulaWith M symbols rhs)
  | tfAll body =>
      rawFormulaAllCode M
        (rawStructuralTemplateFormulaWith M symbols body)
  | tfEx body =>
      rawFormulaExCode M
        (rawStructuralTemplateFormulaWith M symbols body)
  | tfOpaque predicate arguments =>
      rawStructuralTemplateOpaqueCode symbols predicate
        (rawStructuralTemplateTermsWith M symbols arguments)
  end.

Arguments rawStructuralTemplateTermWith M _ _ : clear implicits.
Arguments rawStructuralTemplateTermsWith M _ _ : clear implicits.
Arguments rawStructuralTemplateFormulaWith M _ _ : clear implicits.

(** ------------------------------------------------------------------
    Depth-indexed metasyntactic operations. *)

(** Shift every de Bruijn variable at or above [depth] by one.  This is the
    exact renaming seen at an equality leaf after descending through [depth]
    quantifiers of a root-level [templateFormulaRename S]. *)
Fixpoint templateShiftRenamingAt (depth index : nat) : nat :=
  match depth with
  | 0 => S index
  | S outerDepth =>
      match index with
      | 0 => 0
      | S outerIndex => S (templateShiftRenamingAt outerDepth outerIndex)
      end
  end.

Lemma templateShiftRenamingAt_succ : forall depth index,
  templateShiftRenamingAt (S depth) index =
    templateUpRenaming (templateShiftRenamingAt depth) index.
Proof.
  intros depth [|index]; reflexivity.
Qed.

Lemma templateFormulaRename_shift_succ : forall depth formula,
  templateFormulaRename (templateShiftRenamingAt (S depth)) formula =
  templateFormulaRename
    (templateUpRenaming (templateShiftRenamingAt depth)) formula.
Proof.
  intros depth formula.
  apply templateFormulaRename_ext.
  apply templateShiftRenamingAt_succ.
Qed.

Lemma templateFormulaRename_shift_zero : forall formula,
  templateFormulaRename (templateShiftRenamingAt 0) formula =
  templateFormulaRename S formula.
Proof.
  intro formula. apply templateFormulaRename_ext.
  intros index. reflexivity.
Qed.

(** Substitution beneath [depth] binders is obtained by repeatedly applying
    the standard lifting operation.  At depth zero this is ordinary opening:
    variable zero is replaced and every positive variable is lowered. *)
Fixpoint templateOpeningSubstAt (depth : nat)
    (replacement : TemplateTerm) : nat -> TemplateTerm :=
  match depth with
  | 0 => templateInstTerm replacement
  | S outerDepth =>
      templateTermUpSubst
        (templateOpeningSubstAt outerDepth replacement)
  end.

(** ------------------------------------------------------------------
    Exact atomic inputs. *)

(** The term clauses are precisely the equality-leaf obligations consumed
    by the two formula-operation tree validators.  The opaque clauses supply
    whole finite trees, not just semantic claims.  Their four equations make
    depth, source, target, and validation independently inspectable. *)
Record RawCodedTemplateStructuralInputs (M : RawPAModel) : Type := {
  rawStructuralTemplateSymbols : RawCodedTemplateStructuralSymbols M;

  rawStructuralTemplateTermShiftAt : forall depth input,
    RawCodedTermShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawStructuralTemplateTermWith M
        rawStructuralTemplateSymbols input)
      (rawStructuralTemplateTermWith M rawStructuralTemplateSymbols
        (templateTermRename (templateShiftRenamingAt depth) input));

  rawStructuralTemplateTermOpeningAt : forall depth replacement input,
    RawCodedFormulaSubstitutionAtom M
      (rawStructuralTemplateTermWith M
        rawStructuralTemplateSymbols replacement)
      (rawNumeralValue M depth)
      (rawStructuralTemplateTermWith M
        rawStructuralTemplateSymbols input)
      (rawStructuralTemplateTermWith M rawStructuralTemplateSymbols
        (templateTermSubst
          (templateOpeningSubstAt depth replacement) input));

  rawStructuralTemplateOpaqueShiftTree :
    forall depth predicate arguments, RawFormulaShiftTree M;
  rawStructuralTemplateOpaqueShiftTree_depth :
    forall depth predicate arguments,
      rawFormulaShiftTreeDepth M
        (rawStructuralTemplateOpaqueShiftTree
          depth predicate arguments) = rawNumeralValue M depth;
  rawStructuralTemplateOpaqueShiftTree_source :
    forall depth predicate arguments,
      rawFormulaShiftTreeSource M
        (rawStructuralTemplateOpaqueShiftTree
          depth predicate arguments) =
      rawStructuralTemplateFormulaWith M rawStructuralTemplateSymbols
        (tfOpaque predicate arguments);
  rawStructuralTemplateOpaqueShiftTree_target :
    forall depth predicate arguments,
      rawFormulaShiftTreeTarget M
        (rawStructuralTemplateOpaqueShiftTree
          depth predicate arguments) =
      rawStructuralTemplateFormulaWith M rawStructuralTemplateSymbols
        (templateFormulaRename (templateShiftRenamingAt depth)
          (tfOpaque predicate arguments));
  rawStructuralTemplateOpaqueShiftTree_valid :
    forall depth predicate arguments,
      RawFormulaShiftTreeValid M (rawNumeralValue M 1)
        (rawStructuralTemplateOpaqueShiftTree
          depth predicate arguments);

  rawStructuralTemplateOpaqueOpenTree :
    forall depth replacement predicate arguments, RawFormulaShiftTree M;
  rawStructuralTemplateOpaqueOpenTree_depth :
    forall depth replacement predicate arguments,
      rawFormulaShiftTreeDepth M
        (rawStructuralTemplateOpaqueOpenTree
          depth replacement predicate arguments) = rawNumeralValue M depth;
  rawStructuralTemplateOpaqueOpenTree_source :
    forall depth replacement predicate arguments,
      rawFormulaShiftTreeSource M
        (rawStructuralTemplateOpaqueOpenTree
          depth replacement predicate arguments) =
      rawStructuralTemplateFormulaWith M rawStructuralTemplateSymbols
        (tfOpaque predicate arguments);
  rawStructuralTemplateOpaqueOpenTree_target :
    forall depth replacement predicate arguments,
      rawFormulaShiftTreeTarget M
        (rawStructuralTemplateOpaqueOpenTree
          depth replacement predicate arguments) =
      rawStructuralTemplateFormulaWith M rawStructuralTemplateSymbols
        (templateFormulaSubst
          (templateOpeningSubstAt depth replacement)
          (tfOpaque predicate arguments));
  rawStructuralTemplateOpaqueOpenTree_valid :
    forall depth replacement predicate arguments,
      RawFormulaSubstitutionTreeValid M
        (rawStructuralTemplateTermWith M
          rawStructuralTemplateSymbols replacement)
        (rawStructuralTemplateOpaqueOpenTree
          depth replacement predicate arguments)
}.

Arguments rawStructuralTemplateSymbols {M} _.
Arguments rawStructuralTemplateTermShiftAt {M} _ _ _.
Arguments rawStructuralTemplateTermOpeningAt {M} _ _ _ _.
Arguments rawStructuralTemplateOpaqueShiftTree {M}
  _ _ _ _.
Arguments rawStructuralTemplateOpaqueShiftTree_depth {M}
  _ _ _ _.
Arguments rawStructuralTemplateOpaqueShiftTree_source {M}
  _ _ _ _.
Arguments rawStructuralTemplateOpaqueShiftTree_target {M}
  _ _ _ _.
Arguments rawStructuralTemplateOpaqueShiftTree_valid {M}
  _ _ _ _.
Arguments rawStructuralTemplateOpaqueOpenTree {M}
  _ _ _ _ _.
Arguments rawStructuralTemplateOpaqueOpenTree_depth {M}
  _ _ _ _ _.
Arguments rawStructuralTemplateOpaqueOpenTree_source {M}
  _ _ _ _ _.
Arguments rawStructuralTemplateOpaqueOpenTree_target {M}
  _ _ _ _ _.
Arguments rawStructuralTemplateOpaqueOpenTree_valid {M}
  _ _ _ _ _.

Definition rawStructuralTemplateTerm {M : RawPAModel}
    (inputs : RawCodedTemplateStructuralInputs M)
    (input : TemplateTerm) : M :=
  rawStructuralTemplateTermWith M
    (rawStructuralTemplateSymbols inputs) input.

Definition rawStructuralTemplateTerms {M : RawPAModel}
    (inputs : RawCodedTemplateStructuralInputs M)
    (terms : list TemplateTerm) : list M :=
  rawStructuralTemplateTermsWith M
    (rawStructuralTemplateSymbols inputs) terms.

Definition rawStructuralTemplateFormula {M : RawPAModel}
    (inputs : RawCodedTemplateStructuralInputs M)
    (formula : TemplateFormula) : M :=
  rawStructuralTemplateFormulaWith M
    (rawStructuralTemplateSymbols inputs) formula.

Arguments rawStructuralTemplateTerm {M} _ _.
Arguments rawStructuralTemplateTerms {M} _ _.
Arguments rawStructuralTemplateFormula {M} _ _.

(** ------------------------------------------------------------------
    Structural shift tree. *)

Fixpoint rawStructuralTemplateShiftTree {M : RawPAModel}
    (inputs : RawCodedTemplateStructuralInputs M)
    (depth : nat) (formula : TemplateFormula) : RawFormulaShiftTree M :=
  match formula with
  | tfEq lhs rhs =>
      RFSTEq M (rawNumeralValue M depth)
        (rawStructuralTemplateTerm inputs lhs)
        (rawStructuralTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) lhs))
        (rawStructuralTemplateTerm inputs rhs)
        (rawStructuralTemplateTerm inputs
          (templateTermRename (templateShiftRenamingAt depth) rhs))
  | tfBot => RFSTBot M (rawNumeralValue M depth)
  | tfImp lhs rhs =>
      RFSTBinary M RFSBImp (rawNumeralValue M depth)
        (rawStructuralTemplateShiftTree inputs depth lhs)
        (rawStructuralTemplateShiftTree inputs depth rhs)
  | tfAnd lhs rhs =>
      RFSTBinary M RFSBAnd (rawNumeralValue M depth)
        (rawStructuralTemplateShiftTree inputs depth lhs)
        (rawStructuralTemplateShiftTree inputs depth rhs)
  | tfOr lhs rhs =>
      RFSTBinary M RFSBOr (rawNumeralValue M depth)
        (rawStructuralTemplateShiftTree inputs depth lhs)
        (rawStructuralTemplateShiftTree inputs depth rhs)
  | tfAll body =>
      RFSTUnary M RFSUAll (rawNumeralValue M depth)
        (rawStructuralTemplateShiftTree inputs (S depth) body)
  | tfEx body =>
      RFSTUnary M RFSUEx (rawNumeralValue M depth)
        (rawStructuralTemplateShiftTree inputs (S depth) body)
  | tfOpaque predicate arguments =>
      rawStructuralTemplateOpaqueShiftTree
        inputs depth predicate arguments
  end.

Arguments rawStructuralTemplateShiftTree {M} _ _ _.

Lemma rawStructuralTemplateShiftTree_depth : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth formula,
  rawFormulaShiftTreeDepth M
    (rawStructuralTemplateShiftTree inputs depth formula) =
  rawNumeralValue M depth.
Proof.
  intros M inputs depth formula.
  destruct formula; cbn [rawStructuralTemplateShiftTree
    rawFormulaShiftTreeDepth]; try reflexivity.
  apply rawStructuralTemplateOpaqueShiftTree_depth.
Qed.

Lemma rawStructuralTemplateShiftTree_source : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth formula,
  rawFormulaShiftTreeSource M
    (rawStructuralTemplateShiftTree inputs depth formula) =
  rawStructuralTemplateFormula inputs formula.
Proof.
  intros M inputs depth formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth;
    cbn [rawStructuralTemplateShiftTree rawFormulaShiftTreeSource
      rawFormulaShiftBinaryCode rawFormulaShiftUnaryCode
      rawStructuralTemplateFormula rawStructuralTemplateFormulaWith].
  - reflexivity.
  - reflexivity.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHbody.
  - now rewrite IHbody.
  - apply rawStructuralTemplateOpaqueShiftTree_source.
Qed.

Lemma rawStructuralTemplateShiftTree_target : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth formula,
  rawFormulaShiftTreeTarget M
    (rawStructuralTemplateShiftTree inputs depth formula) =
  rawStructuralTemplateFormula inputs
    (templateFormulaRename (templateShiftRenamingAt depth) formula).
Proof.
  intros M inputs depth formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth;
    cbn [rawStructuralTemplateShiftTree rawFormulaShiftTreeTarget
      rawFormulaShiftBinaryCode rawFormulaShiftUnaryCode
      rawStructuralTemplateFormula rawStructuralTemplateFormulaWith].
  - reflexivity.
  - reflexivity.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - rewrite IHbody, templateFormulaRename_shift_succ. reflexivity.
  - rewrite IHbody, templateFormulaRename_shift_succ. reflexivity.
  - apply rawStructuralTemplateOpaqueShiftTree_target.
Qed.

Lemma rawStructuralTemplateShiftTree_valid : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth formula,
  RawFormulaShiftTreeValid M (rawNumeralValue M 1)
    (rawStructuralTemplateShiftTree inputs depth formula).
Proof.
  intros M inputs depth formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth;
    cbn [rawStructuralTemplateShiftTree RawFormulaShiftTreeValid].
  - split; apply rawStructuralTemplateTermShiftAt.
  - exact I.
  - repeat split.
    + apply rawStructuralTemplateShiftTree_depth.
    + apply rawStructuralTemplateShiftTree_depth.
    + exact (IHleft depth).
    + exact (IHright depth).
  - repeat split.
    + apply rawStructuralTemplateShiftTree_depth.
    + apply rawStructuralTemplateShiftTree_depth.
    + exact (IHleft depth).
    + exact (IHright depth).
  - repeat split.
    + apply rawStructuralTemplateShiftTree_depth.
    + apply rawStructuralTemplateShiftTree_depth.
    + exact (IHleft depth).
    + exact (IHright depth).
  - split.
    + rewrite rawStructuralTemplateShiftTree_depth. reflexivity.
    + exact (IHbody (S depth)).
  - split.
    + rewrite rawStructuralTemplateShiftTree_depth. reflexivity.
    + exact (IHbody (S depth)).
  - apply rawStructuralTemplateOpaqueShiftTree_valid.
Qed.

(** ------------------------------------------------------------------
    Structural opening/substitution tree. *)

Fixpoint rawStructuralTemplateOpenTree {M : RawPAModel}
    (inputs : RawCodedTemplateStructuralInputs M)
    (depth : nat) (replacement : TemplateTerm)
    (formula : TemplateFormula) : RawFormulaShiftTree M :=
  match formula with
  | tfEq lhs rhs =>
      RFSTEq M (rawNumeralValue M depth)
        (rawStructuralTemplateTerm inputs lhs)
        (rawStructuralTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) lhs))
        (rawStructuralTemplateTerm inputs rhs)
        (rawStructuralTemplateTerm inputs
          (templateTermSubst
            (templateOpeningSubstAt depth replacement) rhs))
  | tfBot => RFSTBot M (rawNumeralValue M depth)
  | tfImp lhs rhs =>
      RFSTBinary M RFSBImp (rawNumeralValue M depth)
        (rawStructuralTemplateOpenTree inputs depth replacement lhs)
        (rawStructuralTemplateOpenTree inputs depth replacement rhs)
  | tfAnd lhs rhs =>
      RFSTBinary M RFSBAnd (rawNumeralValue M depth)
        (rawStructuralTemplateOpenTree inputs depth replacement lhs)
        (rawStructuralTemplateOpenTree inputs depth replacement rhs)
  | tfOr lhs rhs =>
      RFSTBinary M RFSBOr (rawNumeralValue M depth)
        (rawStructuralTemplateOpenTree inputs depth replacement lhs)
        (rawStructuralTemplateOpenTree inputs depth replacement rhs)
  | tfAll body =>
      RFSTUnary M RFSUAll (rawNumeralValue M depth)
        (rawStructuralTemplateOpenTree inputs (S depth) replacement body)
  | tfEx body =>
      RFSTUnary M RFSUEx (rawNumeralValue M depth)
        (rawStructuralTemplateOpenTree inputs (S depth) replacement body)
  | tfOpaque predicate arguments =>
      rawStructuralTemplateOpaqueOpenTree
        inputs depth replacement predicate arguments
  end.

Arguments rawStructuralTemplateOpenTree {M}
  _ _ _ _.

Lemma rawStructuralTemplateOpenTree_depth : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth replacement formula,
  rawFormulaShiftTreeDepth M
    (rawStructuralTemplateOpenTree inputs depth replacement formula) =
  rawNumeralValue M depth.
Proof.
  intros M inputs depth replacement formula.
  destruct formula; cbn [rawStructuralTemplateOpenTree
    rawFormulaShiftTreeDepth]; try reflexivity.
  apply rawStructuralTemplateOpaqueOpenTree_depth.
Qed.

Lemma rawStructuralTemplateOpenTree_source : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth replacement formula,
  rawFormulaShiftTreeSource M
    (rawStructuralTemplateOpenTree inputs depth replacement formula) =
  rawStructuralTemplateFormula inputs formula.
Proof.
  intros M inputs depth replacement formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth;
    cbn [rawStructuralTemplateOpenTree rawFormulaShiftTreeSource
      rawFormulaShiftBinaryCode rawFormulaShiftUnaryCode
      rawStructuralTemplateFormula rawStructuralTemplateFormulaWith].
  - reflexivity.
  - reflexivity.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHbody.
  - now rewrite IHbody.
  - apply rawStructuralTemplateOpaqueOpenTree_source.
Qed.

Lemma rawStructuralTemplateOpenTree_target : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth replacement formula,
  rawFormulaShiftTreeTarget M
    (rawStructuralTemplateOpenTree inputs depth replacement formula) =
  rawStructuralTemplateFormula inputs
    (templateFormulaSubst
      (templateOpeningSubstAt depth replacement) formula).
Proof.
  intros M inputs depth replacement formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth;
    cbn [rawStructuralTemplateOpenTree rawFormulaShiftTreeTarget
      rawFormulaShiftBinaryCode rawFormulaShiftUnaryCode
      rawStructuralTemplateFormula rawStructuralTemplateFormulaWith].
  - reflexivity.
  - reflexivity.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHleft, IHright.
  - now rewrite IHbody.
  - now rewrite IHbody.
  - apply rawStructuralTemplateOpaqueOpenTree_target.
Qed.

Lemma rawStructuralTemplateOpenTree_valid : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    depth replacement formula,
  RawFormulaSubstitutionTreeValid M
    (rawStructuralTemplateTerm inputs replacement)
    (rawStructuralTemplateOpenTree inputs depth replacement formula).
Proof.
  intros M inputs depth replacement formula.
  revert depth.
  induction formula as
      [left right | | left IHleft right IHright
      | left IHleft right IHright | left IHleft right IHright
      | body IHbody | body IHbody | predicate arguments]; intro depth;
    cbn [rawStructuralTemplateOpenTree RawFormulaSubstitutionTreeValid
      RawFormulaOperationTreeValid].
  - split; apply rawStructuralTemplateTermOpeningAt.
  - exact I.
  - repeat split.
    + apply rawStructuralTemplateOpenTree_depth.
    + apply rawStructuralTemplateOpenTree_depth.
    + exact (IHleft depth).
    + exact (IHright depth).
  - repeat split.
    + apply rawStructuralTemplateOpenTree_depth.
    + apply rawStructuralTemplateOpenTree_depth.
    + exact (IHleft depth).
    + exact (IHright depth).
  - repeat split.
    + apply rawStructuralTemplateOpenTree_depth.
    + apply rawStructuralTemplateOpenTree_depth.
    + exact (IHleft depth).
    + exact (IHright depth).
  - split.
    + rewrite rawStructuralTemplateOpenTree_depth. reflexivity.
    + exact (IHbody (S depth)).
  - split.
    + rewrite rawStructuralTemplateOpenTree_depth. reflexivity.
    + exact (IHbody (S depth)).
  - apply rawStructuralTemplateOpaqueOpenTree_valid.
Qed.

(** ------------------------------------------------------------------
    Realization and compiler-facing translation. *)

Theorem rawStructuralTemplateFormula_shift : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateStructuralInputs M) formula,
  RawCodedFormulaShift M
    (raw_zero M) (rawNumeralValue M 1)
    (rawStructuralTemplateFormula inputs formula)
    (rawStructuralTemplateFormula inputs
      (templateFormulaRename S formula)).
Proof.
  intros M hPA inputs formula.
  pose proof (raw_codedFormulaShift_of_valid_tree M hPA
    (rawNumeralValue M 1)
    (rawStructuralTemplateShiftTree inputs 0 formula)
    (rawStructuralTemplateShiftTree_valid M inputs 0 formula)) as hshift.
  rewrite rawStructuralTemplateShiftTree_depth in hshift.
  rewrite rawStructuralTemplateShiftTree_source in hshift.
  rewrite rawStructuralTemplateShiftTree_target in hshift.
  rewrite templateFormulaRename_shift_zero in hshift.
  exact hshift.
Qed.

Theorem rawStructuralTemplateFormula_open : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (inputs : RawCodedTemplateStructuralInputs M) body replacement,
  RawCodedFormulaSingleSubstitution M
    (rawStructuralTemplateTerm inputs replacement)
    (rawStructuralTemplateFormula inputs body)
    (rawStructuralTemplateFormula inputs
      (templateFormulaOpen replacement body)).
Proof.
  intros M hPA inputs body replacement.
  assert (hdepth :
      rawFormulaShiftTreeDepth M
        (rawStructuralTemplateOpenTree inputs 0 replacement body) =
      raw_zero M).
  {
    rewrite rawStructuralTemplateOpenTree_depth. reflexivity.
  }
  pose proof (raw_codedFormulaSingleSubstitution_of_valid_tree M hPA
    (rawStructuralTemplateTerm inputs replacement)
    (rawStructuralTemplateOpenTree inputs 0 replacement body)
    hdepth
    (rawStructuralTemplateOpenTree_valid
      M inputs 0 replacement body)) as hopen.
  rewrite rawStructuralTemplateOpenTree_source in hopen.
  rewrite rawStructuralTemplateOpenTree_target in hopen.
  cbn [templateOpeningSubstAt] in hopen.
  unfold templateFormulaOpen.
  exact hopen.
Qed.

(** This is the promised concrete inhabitant of the proof compiler's
    translation interface.  Constructor equations are definitional; only
    the two relational fields invoke the structural realization theorems. *)
Definition rawStructuralTemplateTranslation
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (inputs : RawCodedTemplateStructuralInputs M)
    : RawCodedTemplateTranslation M.
Proof.
  refine {| rawTemplateTerm := rawStructuralTemplateTerm inputs;
    rawTemplateFormula := rawStructuralTemplateFormula inputs |}.
  - reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - intros. reflexivity.
  - apply rawStructuralTemplateFormula_shift. exact hPA.
  - apply rawStructuralTemplateFormula_open. exact hPA.
Defined.

Arguments rawStructuralTemplateTranslation M _ _ : clear implicits.

End PABoundedRawCodedTemplateStructuralTranslation.
