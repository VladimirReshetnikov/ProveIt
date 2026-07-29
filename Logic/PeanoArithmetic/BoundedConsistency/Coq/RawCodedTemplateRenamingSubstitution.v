(**
  Renaming/substitution interchange for coded proof templates.

  The extended template syntax deliberately mirrors ordinary de Bruijn
  syntax, but its variables coexist with named carrier parameters.  The
  latter are inert under both operations.  This module collects the generic
  interchange laws needed whenever a represented proof is moved underneath
  an eigenvariable binder.

  Keeping these facts independent of any particular soundness rule avoids
  repeating delicate [up]-renaming calculations in each recursive-child
  compiler.  In particular, [templateFormulaRename_open] says that opening a
  body and then entering a binder is the same as first entering the binder
  in both the replacement and the body, then opening there.
*)

From BoundedPAConsistency Require Import RawCodedTemplateSyntax.

Module PABoundedRawCodedTemplateRenamingSubstitution.

Import PABoundedRawCodedTemplateSyntax.

(** Renaming distributes over a term substitution. *)
Lemma templateTermRename_subst : forall input renaming substitution,
  templateTermRename renaming (templateTermSubst substitution input) =
  templateTermSubst
    (fun index => templateTermRename renaming (substitution index)) input.
Proof.
  induction input; intros renaming substitution; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsRename_subst : forall inputs renaming substitution,
  templateTermsRename renaming (templateTermsSubst substitution inputs) =
  templateTermsSubst
    (fun index => templateTermRename renaming (substitution index)) inputs.
Proof.
  induction inputs as [|input inputs ih]; intros renaming substitution; cbn.
  - reflexivity.
  - rewrite templateTermRename_subst. f_equal.
    exact (ih renaming substitution).
Qed.

(** The pointwise substitution produced above commutes with lifting.  This
    is the only binder calculation needed by the formula theorem. *)
Lemma templateTermRename_upSubst : forall renaming substitution index,
  templateTermRename (templateUpRenaming renaming)
    (templateTermUpSubst substitution index) =
  templateTermUpSubst
    (fun outer => templateTermRename renaming (substitution outer)) index.
Proof.
  intros renaming substitution [|index]; cbn; [reflexivity |].
  rewrite !templateTermRename_comp.
  apply templateTermRename_ext.
  intro variable. reflexivity.
Qed.

Lemma templateFormulaRename_subst : forall input renaming substitution,
  templateFormulaRename renaming
    (templateFormulaSubst substitution input) =
  templateFormulaSubst
    (fun index => templateTermRename renaming (substitution index)) input.
Proof.
  induction input; intros renaming substitution; cbn.
  - now rewrite !templateTermRename_subst.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - rewrite IHinput. f_equal.
    apply templateFormulaSubst_ext.
    apply templateTermRename_upSubst.
  - rewrite IHinput. f_equal.
    apply templateFormulaSubst_ext.
    apply templateTermRename_upSubst.
  - now rewrite templateTermsRename_subst.
Qed.

(** Conversely, substituting after a renaming composes the substitution with
    that renaming. *)
Lemma templateTermSubst_rename : forall input substitution renaming,
  templateTermSubst substitution (templateTermRename renaming input) =
  templateTermSubst (fun index => substitution (renaming index)) input.
Proof.
  induction input; intros substitution renaming; cbn; try reflexivity.
  - now rewrite IHinput.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
Qed.

Lemma templateTermsSubst_rename : forall inputs substitution renaming,
  templateTermsSubst substitution (templateTermsRename renaming inputs) =
  templateTermsSubst (fun index => substitution (renaming index)) inputs.
Proof.
  induction inputs as [|input inputs ih]; intros substitution renaming; cbn.
  - reflexivity.
  - rewrite templateTermSubst_rename. f_equal.
    exact (ih substitution renaming).
Qed.

Lemma templateTermUpSubst_upRenaming : forall substitution renaming index,
  templateTermUpSubst substitution (templateUpRenaming renaming index) =
  templateTermUpSubst
    (fun outer => substitution (renaming outer)) index.
Proof. intros substitution renaming [|index]; reflexivity. Qed.

Lemma templateFormulaSubst_rename : forall input substitution renaming,
  templateFormulaSubst substitution
    (templateFormulaRename renaming input) =
  templateFormulaSubst
    (fun index => substitution (renaming index)) input.
Proof.
  induction input; intros substitution renaming; cbn.
  - now rewrite !templateTermSubst_rename.
  - reflexivity.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - now rewrite IHinput1, IHinput2.
  - rewrite IHinput. f_equal.
    apply templateFormulaSubst_ext.
    apply templateTermUpSubst_upRenaming.
  - rewrite IHinput. f_equal.
    apply templateFormulaSubst_ext.
    apply templateTermUpSubst_upRenaming.
  - now rewrite templateTermsSubst_rename.
Qed.

(** Opening commutes with an arbitrary outer renaming.  The body uses the
    lifted renaming because its variable zero belongs to the binder being
    opened, whereas the replacement lives outside that binder. *)
Theorem templateFormulaRename_open : forall body replacement renaming,
  templateFormulaRename renaming
    (templateFormulaOpen replacement body) =
  templateFormulaOpen
    (templateTermRename renaming replacement)
    (templateFormulaRename (templateUpRenaming renaming) body).
Proof.
  intros body replacement renaming.
  unfold templateFormulaOpen.
  rewrite templateFormulaRename_subst.
  rewrite templateFormulaSubst_rename.
  apply templateFormulaSubst_ext.
  intros [|index]; reflexivity.
Qed.

End PABoundedRawCodedTemplateRenamingSubstitution.
