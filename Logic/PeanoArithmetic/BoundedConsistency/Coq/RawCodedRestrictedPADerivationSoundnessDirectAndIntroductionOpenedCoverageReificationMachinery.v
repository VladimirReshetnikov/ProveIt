(**
  Generic, computation-free reification machinery for parameter abstraction.

  The Boolean checker traverses an original template without constructing
  either its abstracted copy or its PA translation.  Its soundness theorem is
  independent of the And-I compiler law and valid at every binder depth.
*)

From Stdlib Require Import Lia.
From PAHF Require Import PAHF.
From BoundedPAConsistency Require Import
  RawCodedTemplateSyntax
  RawCodedTemplateStructuralTranslation
  RawCodedTemplateParameterAbstraction.

Module PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationMachinery.

Import PA.
Import PABoundedRawCodedTemplateSyntax.
Import PABoundedRawCodedTemplateStructuralTranslation.
Import PABoundedRawCodedTemplateParameterAbstraction.

Local Open Scope bool_scope.

Fixpoint templateTermHasPAReificationAfterAbstracting
    (selected : TemplateParameterName) (input : TemplateTerm) : bool :=
  match input with
  | ttVar _ => true
  | ttParameter current => Nat.eqb current selected
  | ttZero => true
  | ttSucc child =>
      templateTermHasPAReificationAfterAbstracting selected child
  | ttAdd lhs rhs =>
      templateTermHasPAReificationAfterAbstracting selected lhs &&
      templateTermHasPAReificationAfterAbstracting selected rhs
  | ttMul lhs rhs =>
      templateTermHasPAReificationAfterAbstracting selected lhs &&
      templateTermHasPAReificationAfterAbstracting selected rhs
  end.

Fixpoint templateFormulaHasPAReificationAfterAbstracting
    (selected : TemplateParameterName) (input : TemplateFormula) : bool :=
  match input with
  | tfEq lhs rhs =>
      templateTermHasPAReificationAfterAbstracting selected lhs &&
      templateTermHasPAReificationAfterAbstracting selected rhs
  | tfBot => true
  | tfImp lhs rhs =>
      templateFormulaHasPAReificationAfterAbstracting selected lhs &&
      templateFormulaHasPAReificationAfterAbstracting selected rhs
  | tfAnd lhs rhs =>
      templateFormulaHasPAReificationAfterAbstracting selected lhs &&
      templateFormulaHasPAReificationAfterAbstracting selected rhs
  | tfOr lhs rhs =>
      templateFormulaHasPAReificationAfterAbstracting selected lhs &&
      templateFormulaHasPAReificationAfterAbstracting selected rhs
  | tfAll body =>
      templateFormulaHasPAReificationAfterAbstracting selected body
  | tfEx body =>
      templateFormulaHasPAReificationAfterAbstracting selected body
  | tfOpaque _ _ => false
  end.

(** Variable renaming preserves the checker because it changes neither named
    parameters nor the formula constructor tree. *)
Lemma templateTermHasPAReificationAfterAbstracting_rename : forall
    selected renaming input,
  templateTermHasPAReificationAfterAbstracting selected
    (templateTermRename renaming input) =
  templateTermHasPAReificationAfterAbstracting selected input.
Proof.
  intros selected renaming input. revert renaming.
  induction input as
      [index | current | | child ih | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs]; intro renaming;
    cbn [templateTermRename
      templateTermHasPAReificationAfterAbstracting].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply ih.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
Qed.

Lemma templateFormulaHasPAReificationAfterAbstracting_rename : forall
    selected renaming input,
  templateFormulaHasPAReificationAfterAbstracting selected
    (templateFormulaRename renaming input) =
  templateFormulaHasPAReificationAfterAbstracting selected input.
Proof.
  intros selected renaming input. revert renaming.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intro renaming;
    cbn [templateFormulaRename
      templateFormulaHasPAReificationAfterAbstracting].
  - now rewrite !templateTermHasPAReificationAfterAbstracting_rename.
  - reflexivity.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - now rewrite ihlhs, ihrhs.
  - apply ihbody.
  - apply ihbody.
  - reflexivity.
Qed.

(** Successful checking produces a PA translation after abstraction. *)
Lemma templateTermHasPAReificationAfterAbstracting_sound : forall
    selected depth input,
  templateTermHasPAReificationAfterAbstracting selected input = true ->
  exists output,
    templateTermAsPATerm
      (templateTermAbstractParameterAt selected depth input) = Some output.
Proof.
  intros selected depth input. revert depth.
  induction input as
      [index | current | | child ih | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs]; intros depth hsuccess;
    cbn [templateTermHasPAReificationAfterAbstracting
      templateTermAbstractParameterAt templateTermAsPATerm] in *.
  - exists (tVar (templateShiftRenamingAt depth index)). reflexivity.
  - destruct (Nat.eqb current selected) eqn:hselected;
      [|discriminate hsuccess].
    exists (tVar depth). reflexivity.
  - exists tZero. reflexivity.
  - destruct (ih depth hsuccess) as [output houtput].
    rewrite houtput. eexists. reflexivity.
  - destruct
      (templateTermHasPAReificationAfterAbstracting selected lhs)
      eqn:hleft;
      [|discriminate hsuccess].
    destruct
      (templateTermHasPAReificationAfterAbstracting selected rhs)
      eqn:hright;
      [|discriminate hsuccess].
    destruct (ihlhs depth eq_refl) as [leftOutput hleftOutput].
    destruct (ihrhs depth eq_refl) as [rightOutput hrightOutput].
    rewrite hleftOutput, hrightOutput. eexists. reflexivity.
  - destruct
      (templateTermHasPAReificationAfterAbstracting selected lhs)
      eqn:hleft;
      [|discriminate hsuccess].
    destruct
      (templateTermHasPAReificationAfterAbstracting selected rhs)
      eqn:hright;
      [|discriminate hsuccess].
    destruct (ihlhs depth eq_refl) as [leftOutput hleftOutput].
    destruct (ihrhs depth eq_refl) as [rightOutput hrightOutput].
    rewrite hleftOutput, hrightOutput. eexists. reflexivity.
Qed.

Lemma templateFormulaHasPAReificationAfterAbstracting_sound : forall
    selected depth input,
  templateFormulaHasPAReificationAfterAbstracting selected input = true ->
  exists output,
    templateFormulaAsPAFormula
      (templateFormulaAbstractParameterAt selected depth input) = Some output.
Proof.
  intros selected depth input. revert depth.
  induction input as
      [lhs rhs | | lhs ihlhs rhs ihrhs | lhs ihlhs rhs ihrhs |
       lhs ihlhs rhs ihrhs | body ihbody | body ihbody |
       predicate arguments]; intros depth hsuccess;
    cbn [templateFormulaHasPAReificationAfterAbstracting
      templateFormulaAbstractParameterAt templateFormulaAsPAFormula] in *.
  - destruct
      (templateTermHasPAReificationAfterAbstracting selected lhs)
      eqn:hleft;
      [|discriminate hsuccess].
    destruct
      (templateTermHasPAReificationAfterAbstracting selected rhs)
      eqn:hright;
      [|discriminate hsuccess].
    destruct (templateTermHasPAReificationAfterAbstracting_sound
      selected depth lhs hleft)
      as [leftOutput hleftOutput].
    destruct (templateTermHasPAReificationAfterAbstracting_sound
      selected depth rhs hright)
      as [rightOutput hrightOutput].
    rewrite hleftOutput, hrightOutput. eexists. reflexivity.
  - exists pBot. reflexivity.
  - destruct
      (templateFormulaHasPAReificationAfterAbstracting selected lhs)
      eqn:hleft;
      [|discriminate hsuccess].
    destruct
      (templateFormulaHasPAReificationAfterAbstracting selected rhs)
      eqn:hright;
      [|discriminate hsuccess].
    destruct (ihlhs depth eq_refl) as [leftOutput hleftOutput].
    destruct (ihrhs depth eq_refl) as [rightOutput hrightOutput].
    rewrite hleftOutput, hrightOutput. eexists. reflexivity.
  - destruct
      (templateFormulaHasPAReificationAfterAbstracting selected lhs)
      eqn:hleft;
      [|discriminate hsuccess].
    destruct
      (templateFormulaHasPAReificationAfterAbstracting selected rhs)
      eqn:hright;
      [|discriminate hsuccess].
    destruct (ihlhs depth eq_refl) as [leftOutput hleftOutput].
    destruct (ihrhs depth eq_refl) as [rightOutput hrightOutput].
    rewrite hleftOutput, hrightOutput. eexists. reflexivity.
  - destruct
      (templateFormulaHasPAReificationAfterAbstracting selected lhs)
      eqn:hleft;
      [|discriminate hsuccess].
    destruct
      (templateFormulaHasPAReificationAfterAbstracting selected rhs)
      eqn:hright;
      [|discriminate hsuccess].
    destruct (ihlhs depth eq_refl) as [leftOutput hleftOutput].
    destruct (ihrhs depth eq_refl) as [rightOutput hrightOutput].
    rewrite hleftOutput, hrightOutput. eexists. reflexivity.
  - destruct (ihbody (S depth) hsuccess) as [output houtput].
    rewrite houtput. eexists. reflexivity.
  - destruct (ihbody (S depth) hsuccess) as [output houtput].
    rewrite houtput. eexists. reflexivity.
  - discriminate hsuccess.
Qed.

(** Once immediate subformula translations are opaque, the PA translations
    of conjunction and implication can be assembled without re-running the
    recursive checker or normalizing either subformula. *)
Lemma templateFormulaAsPAFormula_abstract_imp_success : forall
    selected lhs rhs leftOutput rightOutput,
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter selected lhs) = Some leftOutput ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter selected rhs) = Some rightOutput ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter selected (tfImp lhs rhs)) =
  Some (pImp leftOutput rightOutput).
Proof.
  intros selected lhs rhs leftOutput rightOutput hleft hright.
  unfold templateFormulaAbstractParameter in *.
  cbn [templateFormulaAbstractParameterAt templateFormulaAsPAFormula].
  now rewrite hleft, hright.
Qed.

Lemma templateFormulaAsPAFormula_abstract_and_success : forall
    selected lhs rhs leftOutput rightOutput,
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter selected lhs) = Some leftOutput ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter selected rhs) = Some rightOutput ->
  templateFormulaAsPAFormula
    (templateFormulaAbstractParameter selected (tfAnd lhs rhs)) =
  Some (pAnd leftOutput rightOutput).
Proof.
  intros selected lhs rhs leftOutput rightOutput hleft hright.
  unfold templateFormulaAbstractParameter in *.
  cbn [templateFormulaAbstractParameterAt templateFormulaAsPAFormula].
  now rewrite hleft, hright.
Qed.

End PABoundedRawCodedRestrictedPADerivationSoundnessDirectAndIntroductionOpenedCoverageReificationMachinery.
