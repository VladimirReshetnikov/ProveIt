(**
  Truth-functional semantics for primitive propositional formulas.

  This module ports [Propositional/Boolean/Basic.lean].  Valuations take
  atoms to propositions, and formula evaluation is the direct recursive
  interpretation of the five primitive constructors.  The final letterless
  dichotomy is proved constructively: letterless formulas have decidable
  truth values, so no global excluded-middle or choice principle is needed.
*)

From FoundationModal Require Import
  GenericSemantics GenericLogicSymbol PropositionalFormula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition pvaluation (Atom : Type) : Type := Atom -> Prop.

Fixpoint pboolean_eval {Atom : Type}
    (v : pvaluation Atom) (p : pformula Atom) : Prop :=
  match p with
  | PAtom a => v a
  | PFalsum => False
  | PAnd q r => pboolean_eval v q /\ pboolean_eval v r
  | POr q r => pboolean_eval v q \/ pboolean_eval v r
  | PImp q r => pboolean_eval v q -> pboolean_eval v r
  end.

Definition pboolean_semantics (Atom : Type) :
    generic_semantics (pvaluation Atom) (pformula Atom) :=
  {| generic_models := pboolean_eval |}.

Lemma pboolean_models_iff_eval :
  forall (Atom : Type) (v : pvaluation Atom) (p : pformula Atom),
    generic_models (pboolean_semantics Atom) v p <-> pboolean_eval v p.
Proof. reflexivity. Qed.

Lemma pboolean_tarski_top :
  forall Atom : Type,
    generic_semantics_top
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof. intros Atom; constructor; intros v; exact (fun H => H). Qed.

Lemma pboolean_tarski_bottom :
  forall Atom : Type,
    generic_semantics_bottom
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof. intros Atom; constructor; intros v H; exact H. Qed.

Lemma pboolean_tarski_and :
  forall Atom : Type,
    generic_semantics_and
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof. intros Atom; constructor; reflexivity. Qed.

Lemma pboolean_tarski_or :
  forall Atom : Type,
    generic_semantics_or
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof. intros Atom; constructor; reflexivity. Qed.

Lemma pboolean_tarski_imp :
  forall Atom : Type,
    generic_semantics_imp
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof. intros Atom; constructor; reflexivity. Qed.

Lemma pboolean_tarski_neg :
  forall Atom : Type,
    generic_semantics_neg
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof. intros Atom; constructor; reflexivity. Qed.

Lemma pboolean_tarski :
  forall Atom : Type,
    generic_tarski
      (pformula_connectives Atom) (pboolean_semantics Atom).
Proof.
  intro Atom. constructor.
  - apply pboolean_tarski_top.
  - apply pboolean_tarski_bottom.
  - apply pboolean_tarski_and.
  - apply pboolean_tarski_or.
  - apply pboolean_tarski_imp.
  - apply pboolean_tarski_neg.
Qed.

Lemma pboolean_models_atom :
  forall (Atom : Type) (v : pvaluation Atom) (a : Atom),
    generic_models (pboolean_semantics Atom) v (PAtom a) <-> v a.
Proof. reflexivity. Qed.

(** Logical equivalence of atomic valuations extends to every formula. *)
Lemma pboolean_eval_ext :
  forall (Atom : Type) (v w : pvaluation Atom),
    (forall a, v a <-> w a) ->
    forall p : pformula Atom,
      pboolean_eval v p <-> pboolean_eval w p.
Proof.
  intros Atom v w Hatoms p; induction p; simpl; try apply Hatoms; tauto.
Qed.

(** Substitution is semantic composition.  The atom types may differ, which
    strictly generalizes the source theorem about endosubstitutions. *)
Lemma pboolean_eval_substitute :
  forall (A B : Type) (v : pvaluation B)
         (sigma : psubstitution A B) (p : pformula A),
    pboolean_eval (fun a => pboolean_eval v (sigma a)) p <->
    pboolean_eval v (pformula_substitute sigma p).
Proof.
  intros A B v sigma p; induction p; simpl; tauto.
Qed.

Lemma pboolean_letterless_invariant :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    forall v w : pvaluation Atom,
      pboolean_eval v p <-> pboolean_eval w p.
Proof.
  intros Atom p; induction p as
    [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; simpl.
  - contradiction.
  - intros _ v w. tauto.
  - intros [Hp Hq] v w. specialize (IHp Hp v w).
    specialize (IHq Hq v w). tauto.
  - intros [Hp Hq] v w. specialize (IHp Hp v w).
    specialize (IHq Hq v w). tauto.
  - intros [Hp Hq] v w. specialize (IHp Hp v w).
    specialize (IHq Hq v w). tauto.
Qed.

(** Letterless truth is executable even when atomic propositions are not. *)
Lemma pboolean_letterless_eval_dec :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    forall v : pvaluation Atom,
      {pboolean_eval v p} + {~ pboolean_eval v p}.
Proof.
  intros Atom p; induction p as
    [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; simpl.
  - contradiction.
  - intros _ v. now right.
  - intros [Hp Hq] v.
    destruct (IHp Hp v), (IHq Hq v); simpl; tauto.
  - intros [Hp Hq] v.
    destruct (IHp Hp v), (IHq Hq v); simpl; tauto.
  - intros [Hp Hq] v.
    destruct (IHp Hp v), (IHq Hq v); simpl; tauto.
Defined.

Definition pformula_is_tautology {Atom : Type}
    (p : pformula Atom) : Prop :=
  generic_valid (pboolean_semantics Atom) p.

Lemma pboolean_substitute_tautology :
  forall (A B : Type) (p : pformula A),
    pformula_is_tautology p ->
    forall sigma : psubstitution A B,
      pformula_is_tautology (pformula_substitute sigma p).
Proof.
  intros A B p Hvalid sigma v.
  apply (proj1 (pboolean_eval_substitute v sigma p)).
  apply Hvalid.
Qed.

Lemma pboolean_and_tautology_iff :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_is_tautology (PAnd p q) <->
    pformula_is_tautology p /\ pformula_is_tautology q.
Proof.
  intros Atom p q.
  unfold pformula_is_tautology, generic_valid; simpl.
  split.
  - intro H. split; intro v; specialize (H v); tauto.
  - intros [Hp Hq] v. split; [apply Hp | apply Hq].
Qed.

Lemma pboolean_or_tautology_of :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_is_tautology p \/ pformula_is_tautology q ->
    pformula_is_tautology (POr p q).
Proof.
  intros Atom p q [Hp | Hq] v; [left; apply Hp | right; apply Hq].
Qed.

Lemma pboolean_imp_tautology_of_consequent :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_is_tautology q ->
    pformula_is_tautology (PImp p q).
Proof. intros Atom p q Hq v _. apply Hq. Qed.

Lemma pboolean_bottom_not_tautology :
  forall Atom : Type,
    ~ pformula_is_tautology (@PFalsum Atom).
Proof.
  intros Atom H. exact (H (fun _ => True)).
Qed.

Lemma pboolean_top_tautology :
  forall Atom : Type,
    pformula_is_tautology (@ptop Atom).
Proof. intros Atom v H. exact H. Qed.

Lemma pboolean_letterless_tautology_of_not_neg_tautology :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    ~ pformula_is_tautology (pneg p) ->
    pformula_is_tautology p.
Proof.
  intros Atom p Hletterless Hnotneg.
  unfold pformula_is_tautology, generic_valid in Hnotneg |- *; simpl in Hnotneg |- *.
  set (v0 := fun _ : Atom => False).
  destruct (@pboolean_letterless_eval_dec Atom p Hletterless v0)
    as [Hp | Hnp].
  - intros v.
    apply (proj1 (@pboolean_letterless_invariant Atom p Hletterless v0 v)).
    exact Hp.
  - exfalso. apply Hnotneg. intros v Hv.
    apply Hnp.
    apply (proj2 (@pboolean_letterless_invariant Atom p Hletterless v0 v)).
    exact Hv.
Qed.

Lemma pboolean_neg_tautology_of_letterless_not_tautology :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless p ->
    ~ pformula_is_tautology p ->
    pformula_is_tautology (pneg p).
Proof.
  intros Atom p Hletterless Hnot v Hp.
  unfold pformula_is_tautology, generic_valid in Hnot; simpl in Hnot.
  apply Hnot. intros w.
  apply (proj1 (@pboolean_letterless_invariant Atom p Hletterless v w)).
  exact Hp.
Qed.
