(**
  Interpret restricted-target syntax contexts as opaque proof templates.

  [RestrictedTargetFormulaContext] is the transparent syntax family used by
  the compact restricted-consistency target.  Its distinguished hole is
  filled by a numeral-term *code* in an arbitrary raw PA model, so it is one
  of the few existing interfaces which already ranges over nonstandard
  restriction levels.  The generic template compiler, on the other hand,
  knows how to carry named model parameters and opaque predicates through a
  finite proof tree.

  This module connects those two representations structurally.  A target
  context is converted to [TemplateFormula] while its hole is filled by an
  arbitrary [TemplateTerm].  The main raw-code theorem says that structural
  template translation is exactly [rawRestrictedTargetFormulaContextCode]
  applied to the translated replacement term.  No decoding, numeral
  standardness, or semantic truth-to-proof principle occurs in the proof.

  A separate host-syntax theorem shows agreement with ordinary context
  instantiation when the replacement is a genuinely closed PA term.  The
  closedness hypothesis is needed only because [RTFCSeal] chooses its number
  of universal closures from the formula bound.
*)

From Stdlib Require Import Arith.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedRestrictedPAConsistencyFormulaCode
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedDynamicTruthUniversalLeafSourceTemplate.

Module PABoundedRawCodedRestrictedTargetTemplateContext.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedRestrictedPAConsistencyFormulaCode.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedDynamicTruthUniversalLeafSourceTemplate.

(** The replacement may be a named carrier parameter.  Fixed subterms remain
    honest embedded PA syntax, while the distinguished hole is never
    inspected. *)
Fixpoint restrictedTargetTemplateTermContext
    (replacement : TemplateTerm) (context : RestrictedTargetTermContext)
    : TemplateTerm :=
  match context with
  | RTTCFixed fixed => embedPATerm fixed
  | RTTCHole => replacement
  | RTTCSucc child =>
      ttSucc (restrictedTargetTemplateTermContext replacement child)
  | RTTCAdd lhs rhs =>
      ttAdd
        (restrictedTargetTemplateTermContext replacement lhs)
        (restrictedTargetTemplateTermContext replacement rhs)
  | RTTCMul lhs rhs =>
      ttMul
        (restrictedTargetTemplateTermContext replacement lhs)
        (restrictedTargetTemplateTermContext replacement rhs)
  end.

(** Match [Formula.closeN] exactly: each successor first adds one universal
    binder and then continues around the enlarged formula. *)
Fixpoint restrictedTargetTemplateCloseN
    (count : nat) (body : TemplateFormula) : TemplateFormula :=
  match count with
  | 0 => body
  | S smaller => restrictedTargetTemplateCloseN smaller (tfAll body)
  end.

Fixpoint restrictedTargetTemplateFormulaContext
    (replacement : TemplateTerm) (context : RestrictedTargetFormulaContext)
    : TemplateFormula :=
  match context with
  | RTFCFixed fixed => embedPAFormula fixed
  | RTFCBot => tfBot
  | RTFCEq lhs rhs =>
      tfEq
        (restrictedTargetTemplateTermContext replacement lhs)
        (restrictedTargetTemplateTermContext replacement rhs)
  | RTFCImp lhs rhs =>
      tfImp
        (restrictedTargetTemplateFormulaContext replacement lhs)
        (restrictedTargetTemplateFormulaContext replacement rhs)
  | RTFCAnd lhs rhs =>
      tfAnd
        (restrictedTargetTemplateFormulaContext replacement lhs)
        (restrictedTargetTemplateFormulaContext replacement rhs)
  | RTFCOr lhs rhs =>
      tfOr
        (restrictedTargetTemplateFormulaContext replacement lhs)
        (restrictedTargetTemplateFormulaContext replacement rhs)
  | RTFCAll child =>
      tfAll (restrictedTargetTemplateFormulaContext replacement child)
  | RTFCEx child =>
      tfEx (restrictedTargetTemplateFormulaContext replacement child)
  | RTFCSeal child =>
      restrictedTargetTemplateCloseN
        (restrictedTargetFormulaContextBound child)
        (restrictedTargetTemplateFormulaContext replacement child)
  end.

Arguments restrictedTargetTemplateTermContext replacement context
  : clear implicits.
Arguments restrictedTargetTemplateFormulaContext replacement context
  : clear implicits.

(** ------------------------------------------------------------------
    Agreement with ordinary host-level instantiation. *)

Lemma restrictedTargetTemplateCloseN_embedPA : forall count body,
  restrictedTargetTemplateCloseN count (embedPAFormula body) =
  embedPAFormula (Formula.closeN count body).
Proof.
  induction count as [|count ih]; intro body.
  - reflexivity.
  - cbn [restrictedTargetTemplateCloseN Formula.closeN].
    exact (ih (pAll body)).
Qed.

Lemma restrictedTargetTemplateTermContext_embedPA : forall
    replacement context,
  restrictedTargetTemplateTermContext (embedPATerm replacement) context =
  embedPATerm
    (instantiateRestrictedTargetTermContext replacement context).
Proof.
  intros replacement context.
  induction context; cbn
    [restrictedTargetTemplateTermContext
      instantiateRestrictedTargetTermContext];
    try rewrite ?IHcontext, ?IHcontext1, ?IHcontext2;
    reflexivity.
Qed.

Theorem restrictedTargetTemplateFormulaContext_embedPA : forall
    replacement,
  Term.bound replacement = 0 -> forall context,
  restrictedTargetTemplateFormulaContext (embedPATerm replacement) context =
  embedPAFormula
    (instantiateRestrictedTargetFormulaContext replacement context).
Proof.
  intros replacement hclosed context.
  induction context; cbn
    [restrictedTargetTemplateFormulaContext
      instantiateRestrictedTargetFormulaContext];
    try rewrite ?IHcontext, ?IHcontext1, ?IHcontext2;
    try reflexivity.
  - now rewrite !restrictedTargetTemplateTermContext_embedPA.
  - unfold Formula.sealPA.
    rewrite restrictedTargetFormulaContextBound_instance by exact hclosed.
    apply restrictedTargetTemplateCloseN_embedPA.
Qed.

(** ------------------------------------------------------------------
    Exact arbitrary-model raw-code translation.

    The main recursion is stated over bare structural symbols rather than the
    stronger operation-tree input record.  Restricted targets contain no
    opaque template leaves, so requiring shift and substitution witnesses here
    would be artificial.  This more general statement is also what lets the
    direct nonstandard translation share the exact same target theorem. *)

Lemma rawStructuralWith_restrictedTargetTemplateCloseN : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    count body,
  rawStructuralTemplateFormulaWith M symbols
    (restrictedTargetTemplateCloseN count body) =
  rawRestrictedTargetCloseNFormulaCode M count
    (rawStructuralTemplateFormulaWith M symbols body).
Proof.
  intros M symbols count.
  induction count as [|count ih]; intro body.
  - reflexivity.
  - cbn [restrictedTargetTemplateCloseN
      rawRestrictedTargetCloseNFormulaCode].
    change
      (rawStructuralTemplateFormulaWith M symbols
        (restrictedTargetTemplateCloseN count (tfAll body)) =
       rawRestrictedTargetCloseNFormulaCode M count
        (rawStructuralTemplateFormulaWith M symbols (tfAll body))).
    apply ih.
Qed.

Lemma rawStructuralWith_restrictedTargetTemplateTermContext : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    replacement context,
  rawStructuralTemplateTermWith M symbols
    (restrictedTargetTemplateTermContext replacement context) =
  rawRestrictedTargetTermContextCode M
    (rawStructuralTemplateTermWith M symbols replacement) context.
Proof.
  intros M symbols replacement context.
  induction context as
      [fixed | | child ih | lhs ihLeft rhs ihRight |
       lhs ihLeft rhs ihRight].
  - cbn [restrictedTargetTemplateTermContext
      rawRestrictedTargetTermContextCode].
    apply rawStructuralTemplateTermWith_embedPA.
  - reflexivity.
  - cbn [restrictedTargetTemplateTermContext
      rawRestrictedTargetTermContextCode rawStructuralTemplateTermWith].
    now rewrite ih.
  - cbn [restrictedTargetTemplateTermContext
      rawRestrictedTargetTermContextCode rawStructuralTemplateTermWith].
    now rewrite ihLeft, ihRight.
  - cbn [restrictedTargetTemplateTermContext
      rawRestrictedTargetTermContextCode rawStructuralTemplateTermWith].
    now rewrite ihLeft, ihRight.
Qed.

Theorem rawStructuralWith_restrictedTargetTemplateFormulaContext : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    replacement context,
  rawStructuralTemplateFormulaWith M symbols
    (restrictedTargetTemplateFormulaContext replacement context) =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTermWith M symbols replacement) context.
Proof.
  intros M symbols replacement context.
  induction context as
      [fixed | | lhs rhs | lhs ihLeft rhs ihRight |
       lhs ihLeft rhs ihRight | lhs ihLeft rhs ihRight |
       child ih | child ih | child ih].
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode].
    apply rawStructuralTemplateFormulaWith_embedPA.
  - reflexivity.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode
      rawStructuralTemplateFormulaWith].
    pose proof
      (rawStructuralWith_restrictedTargetTemplateTermContext
        M symbols replacement lhs) as hLeft.
    pose proof
      (rawStructuralWith_restrictedTargetTemplateTermContext
        M symbols replacement rhs) as hRight.
    now rewrite hLeft, hRight.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode
      rawStructuralTemplateFormulaWith].
    now rewrite ihLeft, ihRight.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode
      rawStructuralTemplateFormulaWith].
    now rewrite ihLeft, ihRight.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode
      rawStructuralTemplateFormulaWith].
    now rewrite ihLeft, ihRight.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode
      rawStructuralTemplateFormulaWith].
    now rewrite ih.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode
      rawStructuralTemplateFormulaWith].
    now rewrite ih.
  - cbn [restrictedTargetTemplateFormulaContext
      rawRestrictedTargetFormulaContextCode].
    rewrite rawStructuralWith_restrictedTargetTemplateCloseN, ih.
    reflexivity.
Qed.

Lemma rawStructural_restrictedTargetTemplateCloseN : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    count body,
  rawStructuralTemplateFormula inputs
    (restrictedTargetTemplateCloseN count body) =
  rawRestrictedTargetCloseNFormulaCode M count
    (rawStructuralTemplateFormula inputs body).
Proof.
  intros M inputs count body.
  unfold rawStructuralTemplateFormula.
  apply rawStructuralWith_restrictedTargetTemplateCloseN.
Qed.

Lemma rawStructural_restrictedTargetTemplateTermContext : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    replacement context,
  rawStructuralTemplateTerm inputs
    (restrictedTargetTemplateTermContext replacement context) =
  rawRestrictedTargetTermContextCode M
    (rawStructuralTemplateTerm inputs replacement) context.
Proof.
  intros M inputs replacement context.
  unfold rawStructuralTemplateTerm.
  apply rawStructuralWith_restrictedTargetTemplateTermContext.
Qed.

Theorem rawStructural_restrictedTargetTemplateFormulaContext : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    replacement context,
  rawStructuralTemplateFormula inputs
    (restrictedTargetTemplateFormulaContext replacement context) =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTerm inputs replacement) context.
Proof.
  intros M inputs replacement context.
  unfold rawStructuralTemplateFormula, rawStructuralTemplateTerm.
  apply rawStructuralWith_restrictedTargetTemplateFormulaContext.
Qed.

(** Two useful nonstandard specializations.  They identify the exact
    restricted-proof and consistency shapes without requiring the parameter
    code to quote any metatheoretic numeral. *)
Corollary rawStructural_restrictedTargetProofTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    levelParameter root,
  rawStructuralTemplateFormula inputs
    (restrictedTargetTemplateFormulaContext levelParameter
      (restrictedTargetProofContext root)) =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTerm inputs levelParameter)
    (restrictedTargetProofContext root).
Proof.
  intros. apply rawStructural_restrictedTargetTemplateFormulaContext.
Qed.

Corollary rawStructural_restrictedPAConsistencyTemplate : forall
    (M : RawPAModel) (inputs : RawCodedTemplateStructuralInputs M)
    levelParameter,
  rawStructuralTemplateFormula inputs
    (restrictedTargetTemplateFormulaContext levelParameter
      restrictedPAConsistencyFormulaContext) =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTerm inputs levelParameter)
    restrictedPAConsistencyFormulaContext.
Proof.
  intros. apply rawStructural_restrictedTargetTemplateFormulaContext.
Qed.

(** Direct translations use the same constructor interpretation and differ
    only in the operation evidence attached to opaque leaves.  Since a
    restricted target has no opaque leaves, the symbol-level theorem gives
    both useful direct specializations without any carrier decoding. *)
Corollary rawStructuralWith_restrictedTargetProofTemplate : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    levelParameter root,
  rawStructuralTemplateFormulaWith M symbols
    (restrictedTargetTemplateFormulaContext levelParameter
      (restrictedTargetProofContext root)) =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTermWith M symbols levelParameter)
    (restrictedTargetProofContext root).
Proof.
  intros. apply rawStructuralWith_restrictedTargetTemplateFormulaContext.
Qed.

Corollary rawStructuralWith_restrictedPAConsistencyTemplate : forall
    (M : RawPAModel) (symbols : RawCodedTemplateStructuralSymbols M)
    levelParameter,
  rawStructuralTemplateFormulaWith M symbols
    (restrictedTargetTemplateFormulaContext levelParameter
      restrictedPAConsistencyFormulaContext) =
  rawRestrictedTargetFormulaContextCode M
    (rawStructuralTemplateTermWith M symbols levelParameter)
    restrictedPAConsistencyFormulaContext.
Proof.
  intros. apply rawStructuralWith_restrictedTargetTemplateFormulaContext.
Qed.

End PABoundedRawCodedRestrictedTargetTemplateContext.
