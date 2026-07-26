(**
  Structural term traces for templates with model-internal numeral parameters.

  A named template parameter may denote a numeral whose length is
  nonstandard in the ambient PA model.  Such a parameter cannot be decoded
  into an ordinary metatheoretic term.  A [RawNumeralTermCodeAt] witness is,
  however, enough to prove that shifting and opening leave the parameter code
  fixed.  Variables and the transparent zero/successor/addition/
  multiplication constructors can then be handled by the existing exact
  operation constructors.

  This file supplies precisely the two term-level fields requested by
  [RawCodedTemplateStructuralInputs].  In particular, the substitution atom
  is not postulated: we structurally shift the replacement beneath the
  current binder depth and then structurally open the input term with that
  exact lifted code.
*)

From Stdlib Require Import List Arith Lia.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax RawCodedTemplateStructuralTranslation
  RawCodedSyntaxConstructors RawCodedFormulaOperations
  RawCodedTermOperationsStandardAdequacy
  RawCodedTermOperationTreeRealization
  RawCodedPAAxiomContextSelfShift RawCodedFormulaShiftTotality
  RawCodedTermOpeningTotality
  RawCodedNumeralTermCode RawCodedNumeralTermShift
  RawCodedNumeralTermOpening.

Import ListNotations.

Module PABoundedRawCodedTemplateNumeralParameters.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedSyntaxConstructors.
Import PABoundedRawCodedFormulaOperations.
Import PABoundedRawCodedTermOperationsStandardAdequacy.
Import PABoundedRawCodedTermOperationTreeRealization.
Import PABoundedRawCodedPAAxiomContextSelfShift.
Import PABoundedRawCodedFormulaShiftTotality.
Import PABoundedRawCodedTermOpeningTotality.
Import PABoundedRawCodedNumeralTermCode.
Import PABoundedRawCodedNumeralTermShift.
Import PABoundedRawCodedNumeralTermOpening.

(** ------------------------------------------------------------------
    Named numeral data and its structural-symbol interpretation. *)

(** Each name carries both the value bounding its numeral traversal and the
    resulting term code.  Keeping the bound explicit lets a client reuse an
    already produced [RawNumeralTermCodeAt] witness without any appeal to
    functionality or external decoding. *)
Record RawCodedTemplateNumeralParameters (M : RawPAModel) : Type := {
  rawNumeralTemplateParameterBound : TemplateParameterName -> M;
  rawNumeralTemplateParameterCode : TemplateParameterName -> M;
  rawNumeralTemplateParameter_valid : forall name,
    RawNumeralTermCodeAt M
      (rawNumeralTemplateParameterBound name)
      (rawNumeralTemplateParameterCode name)
}.

Arguments rawNumeralTemplateParameterBound {M} _ _.
Arguments rawNumeralTemplateParameterCode {M} _ _.
Arguments rawNumeralTemplateParameter_valid {M} _ _.

(** Opaque predicate applications play no role in term traces.  Accepting
    their interpretation here nevertheless returns exactly the symbols
    record used by the structural formula layer, avoiding a later equality
    transport between two almost-identical records. *)
Definition rawNumeralTemplateSymbols (M : RawPAModel)
    (parameters : RawCodedTemplateNumeralParameters M)
    (opaqueCode : TemplatePredicateName -> list M -> M)
    : RawCodedTemplateStructuralSymbols M :=
  {| rawStructuralTemplateParameterCode :=
       rawNumeralTemplateParameterCode parameters;
     rawStructuralTemplateOpaqueCode := opaqueCode |}.

Arguments rawNumeralTemplateSymbols M _ _ : clear implicits.

(** ------------------------------------------------------------------
    Metatheoretic cutoff operations. *)

(** General shifting by [amount].  The earlier structural formula module
    needs only amount one; substitution additionally needs to lift a
    replacement by the complete binder depth. *)
Definition templateShiftRenamingBy
    (cutoff amount index : nat) : nat :=
  if index <? cutoff then index else index + amount.

Lemma templateShiftRenamingBy_zero_amount : forall cutoff index,
  templateShiftRenamingBy cutoff 0 index = index.
Proof.
  intros cutoff index. unfold templateShiftRenamingBy.
  destruct (index <? cutoff); lia.
Qed.

Lemma templateShiftRenamingBy_one : forall cutoff index,
  templateShiftRenamingBy cutoff 1 index =
    templateShiftRenamingAt cutoff index.
Proof.
  induction cutoff as [|cutoff IH]; intros [|index].
  - reflexivity.
  - cbn [templateShiftRenamingAt].
    unfold templateShiftRenamingBy.
    destruct (S index <? 0) eqn:hzero.
    + apply Nat.ltb_lt in hzero. lia.
    + now rewrite Nat.add_1_r.
  - reflexivity.
  - cbn [templateShiftRenamingAt].
    unfold templateShiftRenamingBy at 1.
    replace (S index <? S cutoff) with (index <? cutoff).
    2:{
      destruct (index <? cutoff) eqn:hcompare.
      - apply Nat.ltb_lt in hcompare.
        symmetry. apply Nat.ltb_lt. lia.
      - apply Nat.ltb_ge in hcompare.
        symmetry. apply Nat.ltb_ge. lia.
    }
    rewrite <- (IH index).
    unfold templateShiftRenamingBy.
    destruct (index <? cutoff); cbn; reflexivity.
Qed.

(** Three pointwise descriptions of capture-avoiding opening.  They are used
    only for the variable leaf below; all compound terms are handled by
    structural trace composition. *)
Lemma templateOpeningSubstAt_below : forall depth replacement index,
  index < depth ->
  templateOpeningSubstAt depth replacement index = ttVar index.
Proof.
  induction depth as [|depth IH]; intros replacement index hbelow.
  - lia.
  - destruct index as [|index].
    + reflexivity.
    + cbn [templateOpeningSubstAt templateTermUpSubst].
      rewrite (IH replacement index) by lia. reflexivity.
Qed.

Lemma templateOpeningSubstAt_at : forall depth replacement,
  templateOpeningSubstAt depth replacement depth =
  templateTermRename
    (templateShiftRenamingBy 0 depth) replacement.
Proof.
  induction depth as [|depth IH]; intro replacement.
  - cbn [templateOpeningSubstAt templateInstTerm].
    rewrite <- (templateTermRename_id replacement) at 1.
    apply templateTermRename_ext. intro index.
    symmetry. apply templateShiftRenamingBy_zero_amount.
  - cbn [templateOpeningSubstAt templateTermUpSubst].
    rewrite IH, templateTermRename_comp.
    apply templateTermRename_ext. intro index.
    unfold templateShiftRenamingBy.
    destruct (index <? 0) eqn:hzero.
    + apply Nat.ltb_lt in hzero. lia.
    + lia.
Qed.

Lemma templateOpeningSubstAt_above : forall depth replacement index,
  depth < index ->
  templateOpeningSubstAt depth replacement index =
    ttVar (Nat.pred index).
Proof.
  induction depth as [|depth IH]; intros replacement index habove.
  - destruct index; [lia | reflexivity].
  - destruct index as [|index]; [lia |].
    destruct index as [|index]; [lia |].
    cbn [templateOpeningSubstAt templateTermUpSubst].
    rewrite (IH replacement (S index)) by lia. reflexivity.
Qed.

(** ------------------------------------------------------------------
    Structural shifting. *)

Theorem raw_numeralTemplateTerm_shift_by : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode cutoff amount input,
  RawCodedTermShift M
    (rawNumeralValue M cutoff) (rawNumeralValue M amount)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermRename
        (templateShiftRenamingBy cutoff amount) input)).
Proof.
  intros M hPA parameters opaqueCode cutoff amount input.
  induction input as
      [index | name | | child IHchild
      | lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    cbn [rawStructuralTemplateTermWith rawNumeralTemplateSymbols
      templateTermRename].
  - pose proof (raw_codedTermShift_standard M hPA
      cutoff amount (tVar index)) as hshift.
    cbn [rawQuotedTermCode standardTermShift] in hshift.
    unfold templateShiftRenamingBy.
    destruct (index <? cutoff) eqn:hindex;
      cbn [rawQuotedTermCode] in hshift;
      exact hshift.
  - apply (raw_codedTermShift_numeral_identity M hPA
      (rawNumeralTemplateParameterBound parameters name)).
    apply rawNumeralTemplateParameter_valid.
  - apply raw_codedTermShift_zero_identity. exact hPA.
  - apply raw_codedTermShift_succ; [exact hPA | exact IHchild].
  - apply raw_codedTermShift_add;
      [exact hPA | exact IHlhs | exact IHrhs].
  - apply raw_codedTermShift_mul;
      [exact hPA | exact IHlhs | exact IHrhs].
Qed.

(** Exact one-place shifting has the type of
    [rawStructuralTemplateTermShiftAt]. *)
Corollary raw_numeralTemplateTerm_shift : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode depth input,
  RawCodedTermShift M
    (rawNumeralValue M depth) (rawNumeralValue M 1)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermRename (templateShiftRenamingAt depth) input)).
Proof.
  intros M hPA parameters opaqueCode depth input.
  replace (templateTermRename (templateShiftRenamingAt depth) input)
    with (templateTermRename
      (templateShiftRenamingBy depth 1) input).
  - apply raw_numeralTemplateTerm_shift_by. exact hPA.
  - apply templateTermRename_ext. intro index.
    exact (templateShiftRenamingBy_one depth index).
Qed.

(** ------------------------------------------------------------------
    Structural opening and substitution atoms. *)

(** A standard variable leaf can be opened exactly even when the lifted
    replacement is a genuinely nonstandard composite term.  The below/equal/
    above cases are certified by a one-node operation tree; only the equal
    case reuses the specialized public constructor. *)
Lemma raw_numeralTemplateTerm_opening_variable : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode depth replacement index,
  RawCodedTermOpening M
    (rawNumeralValue M depth)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermRename
        (templateShiftRenamingBy 0 depth) replacement))
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) (ttVar index))
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermSubst
        (templateOpeningSubstAt depth replacement) (ttVar index))).
Proof.
  intros M hPA parameters opaqueCode depth replacement index.
  cbn [templateTermSubst rawStructuralTemplateTermWith].
  destruct (Nat.lt_trichotomy index depth)
    as [hbelow | [-> | habove]].
  - rewrite (templateOpeningSubstAt_below
      depth replacement index hbelow).
    cbn [templateTermSubst rawStructuralTemplateTermWith].
    apply (raw_codedTermOpening_of_valid_tree M hPA
      (rawNumeralValue M depth)
      (rawStructuralTemplateTermWith M
        (rawNumeralTemplateSymbols M parameters opaqueCode)
        (templateTermRename
          (templateShiftRenamingBy 0 depth) replacement))
      (RTOTVar M (rawNumeralValue M index)
        (rawTermVarCode M (rawNumeralValue M index)))).
    cbn [RawTermOperationTreeValid].
    exists (rawNumeralValue M index). split; [reflexivity |].
    left. split; [|reflexivity].
    apply raw_lt_numeralValue_of_lt; assumption.
  - rewrite templateOpeningSubstAt_at.
    cbn [templateTermSubst rawStructuralTemplateTermWith].
    apply raw_codedTermOpening_variable_at_cutoff. exact hPA.
  - rewrite (templateOpeningSubstAt_above
      depth replacement index habove).
    destruct index as [|predecessor]; [lia |].
    cbn [templateTermSubst rawStructuralTemplateTermWith].
    apply (raw_codedTermOpening_of_valid_tree M hPA
      (rawNumeralValue M depth)
      (rawStructuralTemplateTermWith M
        (rawNumeralTemplateSymbols M parameters opaqueCode)
        (templateTermRename
          (templateShiftRenamingBy 0 depth) replacement))
      (RTOTVar M (rawNumeralValue M (S predecessor))
        (rawTermVarCode M (rawNumeralValue M predecessor)))).
    cbn [RawTermOperationTreeValid].
    exists (rawNumeralValue M (S predecessor)).
    split; [reflexivity |]. right. right.
    exists (rawNumeralValue M predecessor).
    repeat split; try reflexivity.
    apply raw_lt_numeralValue_of_lt; [exact hPA | exact habove].
Qed.

Theorem raw_numeralTemplateTerm_opening : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode depth replacement input,
  RawCodedTermOpening M
    (rawNumeralValue M depth)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermRename
        (templateShiftRenamingBy 0 depth) replacement))
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermSubst
        (templateOpeningSubstAt depth replacement) input)).
Proof.
  intros M hPA parameters opaqueCode depth replacement input.
  induction input as
      [index | name | | child IHchild
      | lhs IHlhs rhs IHrhs | lhs IHlhs rhs IHrhs];
    cbn [templateTermSubst rawStructuralTemplateTermWith
      rawNumeralTemplateSymbols].
  - apply raw_numeralTemplateTerm_opening_variable. exact hPA.
  - apply (raw_codedTermOpening_numeral_identity M hPA
      (rawNumeralTemplateParameterBound parameters name)).
    apply rawNumeralTemplateParameter_valid.
  - apply raw_codedTermOpening_zero. exact hPA.
  - apply raw_codedTermOpening_succ; [exact hPA | exact IHchild].
  - apply raw_codedTermOpening_add;
      [exact hPA | exact IHlhs | exact IHrhs].
  - apply raw_codedTermOpening_mul;
      [exact hPA | exact IHlhs | exact IHrhs].
Qed.

(** This packages capture avoidance exactly as the atom relation consumed at
    equality leaves by [RawFormulaSubstitutionTreeValid]. *)
Corollary raw_numeralTemplateTerm_substitutionAtom : forall
    (M : RawPAModel), RawPASatisfies M ->
    forall (parameters : RawCodedTemplateNumeralParameters M)
      opaqueCode depth replacement input,
  RawCodedFormulaSubstitutionAtom M
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) replacement)
    (rawNumeralValue M depth)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode) input)
    (rawStructuralTemplateTermWith M
      (rawNumeralTemplateSymbols M parameters opaqueCode)
      (templateTermSubst
        (templateOpeningSubstAt depth replacement) input)).
Proof.
  intros M hPA parameters opaqueCode depth replacement input.
  exists (rawStructuralTemplateTermWith M
    (rawNumeralTemplateSymbols M parameters opaqueCode)
    (templateTermRename
      (templateShiftRenamingBy 0 depth) replacement)).
  split.
  - apply raw_numeralTemplateTerm_shift_by. exact hPA.
  - apply raw_numeralTemplateTerm_opening. exact hPA.
Qed.

(** ------------------------------------------------------------------
    Client-facing package. *)

(** This small record isolates exactly the two term trace fields of the full
    structural formula input.  Clients may build opaque shift/open trees
    independently and copy these two projections into
    [RawCodedTemplateStructuralInputs]. *)
Record RawCodedTemplateTermTraceInputs (M : RawPAModel)
    (symbols : RawCodedTemplateStructuralSymbols M) : Type := {
  rawTemplateTermTrace_shiftAt : forall depth input,
    RawCodedTermShift M
      (rawNumeralValue M depth) (rawNumeralValue M 1)
      (rawStructuralTemplateTermWith M symbols input)
      (rawStructuralTemplateTermWith M symbols
        (templateTermRename (templateShiftRenamingAt depth) input));
  rawTemplateTermTrace_openAt : forall depth replacement input,
    RawCodedFormulaSubstitutionAtom M
      (rawStructuralTemplateTermWith M symbols replacement)
      (rawNumeralValue M depth)
      (rawStructuralTemplateTermWith M symbols input)
      (rawStructuralTemplateTermWith M symbols
        (templateTermSubst
          (templateOpeningSubstAt depth replacement) input))
}.

Arguments rawTemplateTermTrace_shiftAt {M symbols} _ _ _.
Arguments rawTemplateTermTrace_openAt {M symbols} _ _ _ _.

Definition rawNumeralTemplateTermTraceInputs
    (M : RawPAModel) (hPA : RawPASatisfies M)
    (parameters : RawCodedTemplateNumeralParameters M)
    (opaqueCode : TemplatePredicateName -> list M -> M)
    : RawCodedTemplateTermTraceInputs M
        (rawNumeralTemplateSymbols M parameters opaqueCode).
Proof.
  refine {| rawTemplateTermTrace_shiftAt := _;
    rawTemplateTermTrace_openAt := _ |}.
  - apply raw_numeralTemplateTerm_shift. exact hPA.
  - apply raw_numeralTemplateTerm_substitutionAtom. exact hPA.
Defined.

Arguments rawNumeralTemplateTermTraceInputs M _ _ _ : clear implicits.

End PABoundedRawCodedTemplateNumeralParameters.
