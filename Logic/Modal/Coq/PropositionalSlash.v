(** Aczel's context-free slash interpretation.

    This ports Foundation/Propositional/Slash.  The interpretation is stated
    for an arbitrary formula predicate, strictly generalizing the source's
    entailment-indexed provability predicate. *)

From FoundationModal Require Import PropositionalFormula PropositionalLogic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint p_aczel_slash {Atom : Type}
    (Prov : pformula Atom -> Prop) (p : pformula Atom) : Prop :=
  match p with
  | PAtom a => Prov (PAtom a)
  | PFalsum => False
  | PAnd q r => p_aczel_slash Prov q /\ p_aczel_slash Prov r
  | POr q r => p_aczel_slash Prov q \/ p_aczel_slash Prov r
  | PImp q r =>
      Prov (PImp q r) /\
      (p_aczel_slash Prov q -> p_aczel_slash Prov r)
  end.

Arguments p_aczel_slash {Atom} Prov p.

Lemma p_aczel_slash_atom :
  forall (Atom : Type) (Prov : pformula Atom -> Prop) a,
    p_aczel_slash Prov (PAtom a) <-> Prov (PAtom a).
Proof. reflexivity. Qed.

Lemma p_aczel_slash_falsum :
  forall (Atom : Type) (Prov : pformula Atom -> Prop),
    ~ p_aczel_slash Prov (@PFalsum Atom).
Proof. intros; exact (fun H => H). Qed.

Lemma p_aczel_slash_or :
  forall (Atom : Type) (Prov : pformula Atom -> Prop) p q,
    p_aczel_slash Prov (POr p q) <->
    p_aczel_slash Prov p \/ p_aczel_slash Prov q.
Proof. reflexivity. Qed.

Lemma p_aczel_slash_and :
  forall (Atom : Type) (Prov : pformula Atom -> Prop) p q,
    p_aczel_slash Prov (PAnd p q) <->
    p_aczel_slash Prov p /\ p_aczel_slash Prov q.
Proof. reflexivity. Qed.

Lemma p_aczel_slash_imp :
  forall (Atom : Type) (Prov : pformula Atom -> Prop) p q,
    p_aczel_slash Prov (PImp p q) <->
    Prov (PImp p q) /\
    (p_aczel_slash Prov p -> p_aczel_slash Prov q).
Proof. reflexivity. Qed.

Lemma p_aczel_slash_neg :
  forall (Atom : Type) (Prov : pformula Atom -> Prop) p,
    p_aczel_slash Prov (pneg p) <->
    Prov (pneg p) /\ ~ p_aczel_slash Prov p.
Proof. reflexivity. Qed.

Lemma p_aczel_slash_top :
  forall (Atom : Type) (Prov : pformula Atom -> Prop),
    p_aczel_slash Prov (@ptop Atom) <-> Prov ptop.
Proof.
  intros Atom Prov. unfold ptop; cbn. tauto.
Qed.

Lemma p_aczel_slash_modus_ponens :
  forall (Atom : Type) (Prov : pformula Atom -> Prop) p q,
    p_aczel_slash Prov (PImp p q) ->
    p_aczel_slash Prov p -> p_aczel_slash Prov q.
Proof. intros Atom Prov p q [_ Hpq] Hp; now apply Hpq. Qed.

Definition pformula_predicate_disjunctive {Atom : Type}
    (Prov : pformula Atom -> Prop) : Prop :=
  forall p q, Prov (POr p q) -> Prov p \/ Prov q.

(** If slash truth coincides with provability, disjunctions have the
    disjunction property.  No other entailment law is used. *)
Theorem pformula_disjunctive_of_aczel_slash_iff :
  forall (Atom : Type) (Prov : pformula Atom -> Prop),
    (forall p, p_aczel_slash Prov p <-> Prov p) ->
    pformula_predicate_disjunctive Prov.
Proof.
  intros Atom Prov Hiff p q Hor.
  apply (proj2 (Hiff (POr p q))) in Hor.
  destruct Hor as [Hp | Hq].
  - left. now apply (proj1 (Hiff p)).
  - right. now apply (proj1 (Hiff q)).
Qed.

Definition pformula_logic_aczel_slash {Atom : Type}
    (L : pformula_logic Atom) : pformula Atom -> Prop :=
  p_aczel_slash (pformula_logic_theorems L).

Corollary pformula_logic_disjunctive_of_aczel_slash_iff :
  forall (Atom : Type) (L : pformula_logic Atom),
    (forall p, pformula_logic_aczel_slash L p <->
      pformula_logic_theorems L p) ->
    pformula_predicate_disjunctive (pformula_logic_theorems L).
Proof. intros Atom L; apply pformula_disjunctive_of_aczel_slash_iff. Qed.
