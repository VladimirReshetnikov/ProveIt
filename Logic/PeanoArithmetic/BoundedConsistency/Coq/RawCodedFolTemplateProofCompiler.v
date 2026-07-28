(**
  Compile generic first-order derivations into finite template proof trees.

  [FirstOrder.Calculus.Prov] is the repository's natural-deduction calculus
  for a purely relational language with equality and one binary membership
  predicate.  This module embeds that language into [TemplateFormula]:

  - a de Bruijn variable is the template variable with the same index;
  - equality is template equality;
  - membership is one fixed opaque binary predicate;
  - every logical constructor is preserved structurally.

  The source derivation relation lives in [Prop].  Consequently Coq's
  elimination discipline deliberately prevents defining a function which
  pattern-matches on a source proof to return a proof tree in [Type].  The
  compiler is therefore stated constructively as an existence theorem.  Its
  induction still builds an explicit finite [TemplateRawProof] at every
  constructor, and proves declarative validity plus exact context and
  conclusion endpoints.  No semantic truth-to-proof principle is used.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol Calculus Completeness.
From BoundedPAConsistency Require Import RawCodedTemplateSyntax.

Import ListNotations.

Module PABoundedRawCodedFolTemplateProofCompiler.

Import PABoundedRawCodedTemplateSyntax.

(** The numeric name is intentionally fixed once for the entire embedding.
    Its value is irrelevant to the structural compiler; later concrete
    translations decide how this opaque predicate is interpreted. *)
Definition folMembershipTemplatePredicateName : TemplatePredicateName := 0.

Fixpoint folTemplateFormula (input : form) : TemplateFormula :=
  match input with
  | fMem lhs rhs =>
      tfOpaque folMembershipTemplatePredicateName [ttVar lhs; ttVar rhs]
  | fEq lhs rhs => tfEq (ttVar lhs) (ttVar rhs)
  | fBot => tfBot
  | fImp lhs rhs =>
      tfImp (folTemplateFormula lhs) (folTemplateFormula rhs)
  | fAnd lhs rhs =>
      tfAnd (folTemplateFormula lhs) (folTemplateFormula rhs)
  | fOr lhs rhs =>
      tfOr (folTemplateFormula lhs) (folTemplateFormula rhs)
  | fAll body => tfAll (folTemplateFormula body)
  | fEx body => tfEx (folTemplateFormula body)
  end.

Definition folTemplateContext (context : list form) : TemplateContext :=
  map folTemplateFormula context.

(** Renaming compatibility includes the lifted renaming beneath binders,
    because [Fol.up] and [templateUpRenaming] are definitionally the same
    operation on natural-number indices. *)
Lemma folTemplateFormula_rename : forall input renaming,
  folTemplateFormula (rename renaming input) =
  templateFormulaRename renaming (folTemplateFormula input).
Proof.
  induction input; intros renaming; cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput.
  - now rewrite IHinput.
Qed.

Lemma folTemplateContext_rename : forall context renaming,
  folTemplateContext (map (rename renaming) context) =
  templateContextRename renaming (folTemplateContext context).
Proof.
  intros context renaming.
  unfold folTemplateContext, templateContextRename.
  rewrite !map_map.
  apply map_ext. intro input.
  apply folTemplateFormula_rename.
Qed.

Lemma folTemplateContext_shift : forall context,
  folTemplateContext (map (rename S) context) =
  templateContextShift (folTemplateContext context).
Proof.
  intros context.
  unfold templateContextShift.
  apply folTemplateContext_rename.
Qed.

(** Source terms are variables only.  Instantiating de Bruijn zero by source
    variable [replacement] therefore becomes template opening by
    [ttVar replacement]. *)
Lemma folTemplateFormula_inst : forall body replacement,
  folTemplateFormula (rename (inst replacement) body) =
  templateFormulaOpen (ttVar replacement) (folTemplateFormula body).
Proof.
  intros body replacement.
  rewrite folTemplateFormula_rename.
  unfold templateFormulaOpen.
  symmetry.
  transitivity
    (templateFormulaSubst
      (fun index => ttVar (inst replacement index))
      (folTemplateFormula body)).
  - apply templateFormulaSubst_ext.
    intros [|index]; reflexivity.
  - apply templateFormulaSubst_variables.
Qed.

(** Package used by the compiler's induction hypotheses. *)
Definition FolTemplateCompiledDerivation
    (context : list form) (conclusion : form) : Prop :=
  exists derivation : TemplateRawProof,
    TemplateRawDerives
      (folTemplateContext context)
      (folTemplateFormula conclusion)
      derivation.

(** Constructor-for-constructor proof compilation.  Although the source
    derivation is proof-irrelevant, each branch supplies a concrete finite
    proof-tree witness. *)
Theorem fol_prov_compiles : forall context conclusion,
  Prov context conclusion ->
  FolTemplateCompiledDerivation context conclusion.
Proof.
  intros context conclusion hprov.
  induction hprov as
    [ context formula hin
    | context antecedent consequent hchild ihChild
    | context antecedent consequent himplication ihImplication
        hantecedent ihAntecedent
    | context conclusion hbottom ihBottom
    | context body
    | context lhs rhs hleft ihLeft hright ihRight
    | context lhs rhs hconjunction ihConjunction
    | context lhs rhs hconjunction ihConjunction
    | context lhs rhs hleft ihLeft
    | context lhs rhs hright ihRight
    | context lhs rhs conclusion hdisjunction ihDisjunction
        hleft ihLeft hright ihRight
    | context body hbody ihBody
    | context body replacement huniversal ihUniversal
    | context body replacement hinstance ihInstance
    | context body conclusion hexistential ihExistential
        hbody ihBody
    | context witness
    | context source target motive hequality ihEquality
        hmotive ihMotive].
  - exists (trpAss (folTemplateContext context)
      (folTemplateFormula formula)).
    apply templateRawDerives_assumption.
    apply in_map. exact hin.
  - destruct ihChild as [child [hvalid [hcontext hconclusion]]].
    exists (trpImpI (folTemplateContext context)
      (folTemplateFormula antecedent) (folTemplateFormula consequent)
      child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihImplication as
      [implicationChild [himplicationValid
        [himplicationContext himplicationConclusion]]].
    destruct ihAntecedent as
      [antecedentChild [hantecedentValid
        [hantecedentContext hantecedentConclusion]]].
    exists (trpImpE (folTemplateContext context)
      (folTemplateFormula antecedent) (folTemplateFormula consequent)
      implicationChild antecedentChild).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihBottom as
      [bottomChild [hbottomValid [hbottomContext hbottomConclusion]]].
    exists (trpBotE (folTemplateContext context)
      (folTemplateFormula conclusion) bottomChild).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - exists (trpLem (folTemplateContext context)
      (folTemplateFormula body)).
    unfold TemplateRawDerives. cbn.
    repeat split; reflexivity.
  - destruct ihLeft as
      [leftChild [hleftValid [hleftContext hleftConclusion]]].
    destruct ihRight as
      [rightChild [hrightValid [hrightContext hrightConclusion]]].
    exists (trpAndI (folTemplateContext context)
      (folTemplateFormula lhs) (folTemplateFormula rhs)
      leftChild rightChild).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihConjunction as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpAndE1 (folTemplateContext context)
      (folTemplateFormula lhs) (folTemplateFormula rhs) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihConjunction as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpAndE2 (folTemplateContext context)
      (folTemplateFormula lhs) (folTemplateFormula rhs) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihLeft as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpOrI1 (folTemplateContext context)
      (folTemplateFormula lhs) (folTemplateFormula rhs) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihRight as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpOrI2 (folTemplateContext context)
      (folTemplateFormula lhs) (folTemplateFormula rhs) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihDisjunction as
      [disjunctionChild [hdisjunctionValid
        [hdisjunctionContext hdisjunctionConclusion]]].
    destruct ihLeft as
      [leftChild [hleftValid [hleftContext hleftConclusion]]].
    destruct ihRight as
      [rightChild [hrightValid [hrightContext hrightConclusion]]].
    exists (trpOrE (folTemplateContext context)
      (folTemplateFormula lhs) (folTemplateFormula rhs)
      (folTemplateFormula conclusion)
      disjunctionChild leftChild rightChild).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; assumption.
  - destruct ihBody as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpAllI (folTemplateContext context)
      (folTemplateFormula body) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; try assumption.
    rewrite <- folTemplateContext_shift. exact hcontext.
  - destruct ihUniversal as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpAllE (folTemplateContext context)
      (folTemplateFormula body) (ttVar replacement) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; try assumption.
    symmetry. apply folTemplateFormula_inst.
  - destruct ihInstance as
      [child [hvalid [hcontext hconclusion]]].
    exists (trpExI (folTemplateContext context)
      (folTemplateFormula body) (ttVar replacement) child).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; try assumption.
    rewrite <- folTemplateFormula_inst. exact hconclusion.
  - destruct ihExistential as
      [existentialChild [hexistentialValid
        [hexistentialContext hexistentialConclusion]]].
    destruct ihBody as
      [bodyChild [hbodyValid [hbodyContext hbodyConclusion]]].
    exists (trpExE (folTemplateContext context)
      (folTemplateFormula body) (folTemplateFormula conclusion)
      existentialChild bodyChild).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; try assumption.
    + rewrite <- folTemplateContext_shift.
      exact hbodyContext.
    + rewrite <- folTemplateFormula_rename.
      exact hbodyConclusion.
  - exists (trpEqRefl (folTemplateContext context) (ttVar witness)).
    apply templateRawDerives_eqRefl.
  - destruct ihEquality as
      [equalityChild [hequalityValid
        [hequalityContext hequalityConclusion]]].
    destruct ihMotive as
      [motiveChild [hmotiveValid [hmotiveContext hmotiveConclusion]]].
    exists (trpEqElim (folTemplateContext context)
      (ttVar source) (ttVar target) (folTemplateFormula motive)
      equalityChild motiveChild).
    unfold TemplateRawDerives. cbn.
    repeat split; try reflexivity; try assumption.
    + rewrite <- folTemplateFormula_inst. exact hmotiveConclusion.
    + symmetry. apply folTemplateFormula_inst.
Qed.

(** Endpoint-expanded form for callers which do not need the package name. *)
Corollary fol_prov_has_valid_template_raw_proof : forall context conclusion,
  Prov context conclusion ->
  exists derivation : TemplateRawProof,
    TemplateRawProofValid derivation /\
    templateRawContext derivation = folTemplateContext context /\
    templateRawConclusion derivation = folTemplateFormula conclusion.
Proof.
  intros context conclusion hprov.
  exact (fol_prov_compiles context conclusion hprov).
Qed.

(** A conventional empty-context semantic validity interface. *)
Definition FolLogicallyValid (formula : form) : Prop :=
  forall (domain : Type) (membership : domain -> domain -> Prop)
    (valuation : nat -> domain),
    Sat domain membership valuation formula.

(** Generic completeness first returns a syntactic [Prov] derivation.  Only
    then does [fol_prov_compiles] expose its finite template proof witness.
    This optional corollary therefore adds no semantic truth-to-proof rule to
    the raw PA compiler: its output remains an ordinary finite proof tree. *)
Corollary fol_logically_valid_compiles : forall formula,
  FolLogicallyValid formula ->
  FolTemplateCompiledDerivation nil formula.
Proof.
  intros formula hvalid.
  apply fol_prov_compiles.
  apply completeness.
  intros domain membership valuation _.
  exact (hvalid domain membership valuation).
Qed.

End PABoundedRawCodedFolTemplateProofCompiler.
