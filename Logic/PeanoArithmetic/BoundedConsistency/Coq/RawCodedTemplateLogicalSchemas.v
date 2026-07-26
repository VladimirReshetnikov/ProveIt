(**
  Small explicit proof templates used by dynamic-truth field laws.

  Lean materializes several fixed source derivations through semantic
  completeness.  The corresponding logical cores are tiny: conjunction
  projection/introduction, existential projection, and universal
  specialization followed by modus ponens.  Recording the finite trees
  directly in Rocq makes their later model-coded compilation transparent and
  keeps completeness out of the nonstandard specialization layer.
*)

From Stdlib Require Import List.
From BoundedPAConsistency Require Import RawCodedTemplateSyntax.

Import ListNotations.

Module PABoundedRawCodedTemplateLogicalSchemas.

Import PABoundedRawCodedTemplateSyntax.

(** ------------------------------------------------------------------
    Rewriting support for existential elimination.

    Substitution cancels a renaming when it sends every renamed variable
    back to its source variable.  The quantified cases lift both maps; named
    parameters and opaque predicate symbols remain untouched. *)

Lemma templateTermSubst_rename_cancel : forall
    input renaming substitution,
  (forall index, substitution (renaming index) = ttVar index) ->
  templateTermSubst substitution
    (templateTermRename renaming input) = input.
Proof.
  induction input; intros renaming substitution hcancel; cbn.
  - apply hcancel.
  - reflexivity.
  - reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsSubst_rename_cancel : forall
    inputs renaming substitution,
  (forall index, substitution (renaming index) = ttVar index) ->
  templateTermsSubst substitution
    (templateTermsRename renaming inputs) = inputs.
Proof.
  unfold templateTermsSubst, templateTermsRename.
  induction inputs as [|input inputs ih];
    intros renaming substitution hcancel; cbn.
  - reflexivity.
  - rewrite (templateTermSubst_rename_cancel
      input renaming substitution hcancel).
    f_equal. now apply ih.
Qed.

Lemma templateFormulaSubst_rename_cancel : forall
    input renaming substitution,
  (forall index, substitution (renaming index) = ttVar index) ->
  templateFormulaSubst substitution
    (templateFormulaRename renaming input) = input.
Proof.
  induction input; intros renaming substitution hcancel; cbn.
  - rewrite (templateTermSubst_rename_cancel
      t renaming substitution hcancel).
    now rewrite (templateTermSubst_rename_cancel
      t0 renaming substitution hcancel).
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - f_equal. apply IHinput. intros [|index]; cbn.
    + reflexivity.
    + rewrite hcancel. reflexivity.
  - f_equal. apply IHinput. intros [|index]; cbn.
    + reflexivity.
    + rewrite hcancel. reflexivity.
  - f_equal. apply templateTermsSubst_rename_cancel.
    exact hcancel.
Qed.

(** Opening the shifted body of a binder by its fresh variable recovers the
    original body literally.  This is the de Bruijn identity used by the
    explicit existential-projection proof below. *)
Lemma templateFormulaOpen_binderShift_zero : forall body,
  templateFormulaOpen (ttVar 0)
    (templateFormulaRename (templateUpRenaming S) body) = body.
Proof.
  intro body.
  unfold templateFormulaOpen.
  apply templateFormulaSubst_rename_cancel.
  intros [|index]; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Propositional schemas. *)

Definition templateAndLeftImpProof
    (leftFormula rightFormula : TemplateFormula) : TemplateRawProof :=
  let conjunction := tfAnd leftFormula rightFormula in
  trpImpI [] conjunction leftFormula
    (trpAndE1 [conjunction] leftFormula rightFormula
      (trpAss [conjunction] conjunction)).

Theorem templateAndLeftImpProof_derives : forall leftFormula rightFormula,
  TemplateRawDerives []
    (tfImp (tfAnd leftFormula rightFormula) leftFormula)
    (templateAndLeftImpProof leftFormula rightFormula).
Proof.
  intros leftFormula rightFormula.
  unfold templateAndLeftImpProof, TemplateRawDerives.
  cbn. repeat split; auto.
Qed.

Definition templateAndRightImpProof
    (leftFormula rightFormula : TemplateFormula) : TemplateRawProof :=
  let conjunction := tfAnd leftFormula rightFormula in
  trpImpI [] conjunction rightFormula
    (trpAndE2 [conjunction] leftFormula rightFormula
      (trpAss [conjunction] conjunction)).

Theorem templateAndRightImpProof_derives : forall leftFormula rightFormula,
  TemplateRawDerives []
    (tfImp (tfAnd leftFormula rightFormula) rightFormula)
    (templateAndRightImpProof leftFormula rightFormula).
Proof.
  intros leftFormula rightFormula.
  unfold templateAndRightImpProof, TemplateRawDerives.
  cbn. repeat split; auto.
Qed.

(** Curried conjunction introduction: [A -> B -> A and B]. *)
Definition templateAndIntroductionProof
    (leftFormula rightFormula : TemplateFormula) : TemplateRawProof :=
  let conjunction := tfAnd leftFormula rightFormula in
  trpImpI [] leftFormula (tfImp rightFormula conjunction)
    (trpImpI [leftFormula] rightFormula conjunction
      (trpAndI [rightFormula; leftFormula]
        leftFormula rightFormula
        (trpAss [rightFormula; leftFormula] leftFormula)
        (trpAss [rightFormula; leftFormula] rightFormula))).

Theorem templateAndIntroductionProof_derives : forall leftFormula rightFormula,
  TemplateRawDerives []
    (tfImp leftFormula
      (tfImp rightFormula (tfAnd leftFormula rightFormula)))
    (templateAndIntroductionProof leftFormula rightFormula).
Proof.
  intros leftFormula rightFormula.
  unfold templateAndIntroductionProof, TemplateRawDerives.
  cbn. repeat split; auto.
Qed.

(** ------------------------------------------------------------------
    Existential projection.

    From [exists x, A(x) and B(x)] retain the same witness for [A]. *)

Definition templateExistsAndLeftImpProof
    (leftBody rightBody : TemplateFormula) : TemplateRawProof :=
  let conjunctionBody := tfAnd leftBody rightBody in
  let antecedent := tfEx conjunctionBody in
  let consequent := tfEx leftBody in
  let shiftedLeftBody :=
    templateFormulaRename (templateUpRenaming S) leftBody in
  let outerContext := [antecedent] in
  let eigenContext := conjunctionBody :: templateContextShift outerContext in
  let conjunctionProof := trpAss eigenContext conjunctionBody in
  let leftProof := trpAndE1 eigenContext leftBody rightBody conjunctionProof in
  let existentialProof :=
    trpExI eigenContext shiftedLeftBody (ttVar 0) leftProof in
  let antecedentProof := trpAss outerContext antecedent in
  trpImpI [] antecedent consequent
    (trpExE outerContext conjunctionBody consequent
      antecedentProof existentialProof).

Theorem templateExistsAndLeftImpProof_derives : forall leftBody rightBody,
  TemplateRawDerives []
    (tfImp (tfEx (tfAnd leftBody rightBody)) (tfEx leftBody))
    (templateExistsAndLeftImpProof leftBody rightBody).
Proof.
  intros leftBody rightBody.
  unfold templateExistsAndLeftImpProof, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    templateContextShift templateContextRename].
  rewrite templateFormulaOpen_binderShift_zero.
  repeat split; auto.
  all: try reflexivity.
  all: left; reflexivity.
Qed.

(** ------------------------------------------------------------------
    Universal specialization and modus ponens.

    This fixed tree proves

      ((forall x, P(x) -> Q(x)) and P(t)) -> Q(t).

    It is the logical kernel of the member-validity field. *)

Definition templateUniversalModusPonensProof
    (premiseBody conclusionBody : TemplateFormula)
    (witness : TemplateTerm) : TemplateRawProof :=
  let universal := tfAll (tfImp premiseBody conclusionBody) in
  let premise := templateFormulaOpen witness premiseBody in
  let conclusion := templateFormulaOpen witness conclusionBody in
  let assumption := tfAnd universal premise in
  let context := [assumption] in
  let assumptionProof := trpAss context assumption in
  let universalProof :=
    trpAndE1 context universal premise assumptionProof in
  let implicationProof :=
    trpAllE context (tfImp premiseBody conclusionBody)
      witness universalProof in
  let premiseProof :=
    trpAndE2 context universal premise assumptionProof in
  trpImpI [] assumption conclusion
    (trpImpE context premise conclusion implicationProof premiseProof).

Theorem templateUniversalModusPonensProof_derives : forall
    premiseBody conclusionBody witness,
  TemplateRawDerives []
    (tfImp
      (tfAnd
        (tfAll (tfImp premiseBody conclusionBody))
        (templateFormulaOpen witness premiseBody))
      (templateFormulaOpen witness conclusionBody))
    (templateUniversalModusPonensProof
      premiseBody conclusionBody witness).
Proof.
  intros premiseBody conclusionBody witness.
  unfold templateUniversalModusPonensProof, TemplateRawDerives.
  cbn [TemplateRawProofValid templateRawContext templateRawConclusion
    templateFormulaOpen templateFormulaSubst].
  repeat split; auto.
  all: try reflexivity.
  all: left; reflexivity.
Qed.

End PABoundedRawCodedTemplateLogicalSchemas.
