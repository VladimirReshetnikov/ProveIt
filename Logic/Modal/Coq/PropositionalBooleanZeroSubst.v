(**
  Valuation-selected zero substitutions.

  This module ports [Propositional/Boolean/ZeroSubst.lean].  Its central
  observation is factored as [pboolean_eval_vf_substitute_iff]: replacing
  each atom by truth or falsity according to a valuation makes evaluation
  under every target valuation equal to the original truth value.

  Constructing formula data by branching on an arbitrary proposition uses
  Coq's informative excluded middle, matching the source's noncomputable
  classical definition.  The target atom type is generalized independently
  of the source atom type because every replacement formula is letterless.
*)

From Stdlib Require Import Logic.Classical_Prop Logic.ClassicalDescription.
From FoundationModal Require Import
  GenericSemantics PropositionalFormula PropositionalBoolean.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pboolean_vf_substitution {A B : Type}
    (v : pvaluation A) : pzero_substitution A B.
Proof.
  refine {| pzero_substitution_apply := fun a =>
      if excluded_middle_informative (v a) then ptop else PFalsum |}.
  intro a. destruct (excluded_middle_informative (v a)); simpl; tauto.
Defined.

Lemma pboolean_vf_substitution_atom :
  forall (A B : Type) (v : pvaluation A)
         (u : pvaluation B) (a : A),
    pboolean_eval u
      (pzero_substitution_apply (pboolean_vf_substitution v) a) <->
    v a.
Proof.
  intros A B v u a. unfold pboolean_vf_substitution; simpl.
  destruct (excluded_middle_informative (v a)); simpl; tauto.
Qed.

Lemma pboolean_eval_vf_substitute_iff :
  forall (A B : Type) (v : pvaluation A)
         (u : pvaluation B) (p : pformula A),
    pboolean_eval u
      (pformula_substitute
        (pzero_substitution_apply (pboolean_vf_substitution v)) p) <->
    pboolean_eval v p.
Proof.
  intros A B v u p.
  pose (derived := fun a : A =>
    pboolean_eval u
      (pzero_substitution_apply (pboolean_vf_substitution v) a)).
  transitivity (pboolean_eval derived p).
  - symmetry. apply pboolean_eval_substitute.
  - apply pboolean_eval_ext. intro a.
    apply pboolean_vf_substitution_atom.
Qed.

Lemma pboolean_exists_neg_zero_subst_of_not_tautology :
  forall (Atom : Type) (p : pformula Atom),
    ~ pformula_is_tautology p ->
    exists sigma : pzero_substitution Atom Atom,
      pformula_is_tautology
        (pneg (pformula_substitute
          (pzero_substitution_apply sigma) p)).
Proof.
  intros Atom p Hnot.
  unfold pformula_is_tautology, generic_valid in Hnot.
  apply not_all_ex_not in Hnot.
  destruct Hnot as [v Hv].
  exists (pboolean_vf_substitution v).
  intros u Hu. apply Hv.
  apply (proj1 (@pboolean_eval_vf_substitute_iff
    Atom Atom v u p)). exact Hu.
Qed.

Lemma pboolean_tautology_of_forall_zero_subst :
  forall (Atom : Type) (p : pformula Atom),
    (forall sigma : pzero_substitution Atom Atom,
      ~ pformula_is_tautology
        (pneg (pformula_substitute
          (pzero_substitution_apply sigma) p))) ->
    pformula_is_tautology p.
Proof.
  intros Atom p Hall.
  destruct (classic (pformula_is_tautology p)) as [Hvalid | Hnot].
  - exact Hvalid.
  - destruct (@pboolean_exists_neg_zero_subst_of_not_tautology Atom p Hnot)
      as [sigma Hsigma].
    exfalso. exact (Hall sigma Hsigma).
Qed.

Lemma pboolean_vf_substitution_tautology :
  forall (A B : Type) (v : pvaluation A) (p : pformula A),
    pboolean_eval v p <->
    pformula_is_tautology
      (pformula_substitute
        (pzero_substitution_apply
          (@pboolean_vf_substitution A B v)) p).
Proof.
  intros A B v p; split.
  - intros Hp u.
    apply (proj2 (@pboolean_eval_vf_substitute_iff A B v u p)).
    exact Hp.
  - intro Hvalid.
    set (u0 := fun _ : B => False).
    apply (proj1 (@pboolean_eval_vf_substitute_iff A B v u0 p)).
    apply Hvalid.
Qed.
