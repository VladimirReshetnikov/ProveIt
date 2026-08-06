(**
  A small syntax for classical normal modal logic.

  This is an idiomatic Rocq port of the primitive modal syntax in
  FormalizedFormalLogic/Foundation, pinned in this repository at commit
  32e1a0956a8622fad067328ca1959729a7634428.  The upstream development is
  read-only; this file is an independent implementation.

  As in Foundation, implication, falsity, and box are primitive.  The other
  Boolean connectives and diamond are definitions, so later correspondence
  theorems state exactly the usual modal schemata without enlarging the
  trusted syntax.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive formula (AtomType : Type) : Type :=
| Atom : AtomType -> formula AtomType
| Bottom : formula AtomType
| Imp : formula AtomType -> formula AtomType -> formula AtomType
| Box : formula AtomType -> formula AtomType.

Arguments Atom {AtomType} _.
Arguments Bottom {AtomType}.
Arguments Imp {AtomType} _ _.
Arguments Box {AtomType} _.

Definition Neg {AtomType} (p : formula AtomType) : formula AtomType :=
  Imp p Bottom.

Definition Top {AtomType} : formula AtomType := Neg Bottom.

Definition Or {AtomType} (p q : formula AtomType) : formula AtomType :=
  Imp (Neg p) q.

Definition And {AtomType} (p q : formula AtomType) : formula AtomType :=
  Neg (Imp p (Neg q)).

Definition Iff {AtomType} (p q : formula AtomType) : formula AtomType :=
  And (Imp p q) (Imp q p).

Definition Dia {AtomType} (p : formula AtomType) : formula AtomType :=
  Neg (Box (Neg p)).

Lemma formula_imp_injective : forall A (p q r s : formula A),
  Imp p q = Imp r s <-> p = r /\ q = s.
Proof. intros; split; [injection 1; auto | intros [-> ->]; reflexivity]. Qed.

Lemma formula_neg_injective : forall A (p q : formula A),
  Neg p = Neg q <-> p = q.
Proof.
  intros. unfold Neg. rewrite formula_imp_injective. tauto.
Qed.

Lemma formula_or_injective : forall A (p q r s : formula A),
  Or p q = Or r s <-> p = r /\ q = s.
Proof.
  intros. unfold Or. rewrite formula_imp_injective, formula_neg_injective.
  tauto.
Qed.

Lemma formula_and_injective : forall A (p q r s : formula A),
  And p q = And r s <-> p = r /\ q = s.
Proof.
  intros. unfold And.
  rewrite formula_neg_injective, formula_imp_injective,
    formula_neg_injective. tauto.
Qed.

Lemma formula_box_injective : forall A (p q : formula A),
  Box p = Box q <-> p = q.
Proof. intros; split; [injection 1; auto | intros ->; reflexivity]. Qed.

Lemma formula_dia_injective : forall A (p q : formula A),
  Dia p = Dia q <-> p = q.
Proof.
  intros. unfold Dia.
  rewrite formula_neg_injective, formula_box_injective,
    formula_neg_injective. reflexivity.
Qed.

(** Foundation's boxdot modality [p /\ box p]. *)
Definition Boxdot {AtomType} (p : formula AtomType) : formula AtomType :=
  And p (Box p).

Fixpoint box_iter {AtomType} (n : nat) (p : formula AtomType)
  : formula AtomType :=
  match n with
  | 0 => p
  | S k => Box (box_iter k p)
  end.

Fixpoint dia_iter {AtomType} (n : nat) (p : formula AtomType)
  : formula AtomType :=
  match n with
  | 0 => p
  | S k => Dia (dia_iter k p)
  end.

Fixpoint complexity {AtomType} (p : formula AtomType) : nat :=
  match p with
  | Atom _ => 0
  | Bottom => 0
  | Imp q r => S (Nat.max (complexity q) (complexity r))
  | Box q => S (complexity q)
  end.

Fixpoint modal_degree {AtomType} (p : formula AtomType) : nat :=
  match p with
  | Atom _ => 0
  | Bottom => 0
  | Imp q r => Nat.max (modal_degree q) (modal_degree r)
  | Box q => S (modal_degree q)
  end.

Fixpoint formula_eq_dec {AtomType}
    (atom_eq_dec : forall x y : AtomType, {x = y} + {x <> y})
    (p q : formula AtomType) : {p = q} + {p <> q}.
Proof. decide equality. Defined.

Definition formula_is_box {AtomType} (p : formula AtomType) : bool :=
  match p with Box _ => true | _ => false end.

Definition formula_negated {AtomType} (p : formula AtomType) : bool :=
  match p with
  | Imp _ Bottom => true
  | _ => false
  end.

Lemma formula_negated_iff : forall A (p : formula A),
  formula_negated p = true <-> exists q, p = Neg q.
Proof.
  intros A p. destruct p as [a | | q r | q]; simpl.
  - split; [discriminate | intros [u H]; discriminate].
  - split; [discriminate | intros [u H]; discriminate].
  - destruct r as [a | | r s | r]; simpl.
    + split; [discriminate | intros [u H]; discriminate].
    + split.
      * intro. exists q. reflexivity.
      * intros [u H]. injection H. reflexivity.
    + split; [discriminate | intros [u H]; discriminate].
    + split; [discriminate | intros [u H]; discriminate].
  - split; [discriminate | intros [u H]; discriminate].
Qed.

Lemma formula_not_negated_iff : forall A (p : formula A),
  formula_negated p = false <-> forall q, p <> Neg q.
Proof.
  intros A p. split.
  - intros Hfalse q Heq. subst p. discriminate.
  - intro H. destruct (formula_negated p) eqn:Hneg; [|reflexivity].
    destruct (proj1 (formula_negated_iff p) Hneg) as [q Hq].
    exact (False_rect _ (H q Hq)).
Qed.

Fixpoint formula_letterless {AtomType} (p : formula AtomType) : Prop :=
  match p with
  | Atom _ => False
  | Bottom => True
  | Imp q r => formula_letterless q /\ formula_letterless r
  | Box q => formula_letterless q
  end.

Fixpoint substitute {AtomType OtherAtoms}
    (sigma : AtomType -> formula OtherAtoms) (p : formula AtomType)
    : formula OtherAtoms :=
  match p with
  | Atom a => sigma a
  | Bottom => Bottom
  | Imp q r => Imp (substitute sigma q) (substitute sigma r)
  | Box q => Box (substitute sigma q)
  end.

Lemma substitute_id :
  forall (AtomType : Type) (p : formula AtomType),
    substitute (@Atom AtomType) p = p.
Proof.
  intros AtomType p; induction p; simpl; now f_equal.
Qed.

Lemma substitute_comp :
  forall (A B C : Type) (tau : B -> formula C)
         (sigma : A -> formula B) (p : formula A),
    substitute tau (substitute sigma p) =
    substitute (fun a => substitute tau (sigma a)) p.
Proof.
  intros A B C tau sigma p; induction p; simpl; now f_equal.
Qed.

Lemma substitute_neg :
  forall (A B : Type) (sigma : A -> formula B) (p : formula A),
    substitute sigma (Neg p) = Neg (substitute sigma p).
Proof. reflexivity. Qed.

Lemma substitute_and :
  forall (A B : Type) (sigma : A -> formula B) (p q : formula A),
    substitute sigma (And p q) =
    And (substitute sigma p) (substitute sigma q).
Proof. reflexivity. Qed.

Lemma substitute_or :
  forall (A B : Type) (sigma : A -> formula B) (p q : formula A),
    substitute sigma (Or p q) =
    Or (substitute sigma p) (substitute sigma q).
Proof. reflexivity. Qed.

Lemma substitute_dia :
  forall (A B : Type) (sigma : A -> formula B) (p : formula A),
    substitute sigma (Dia p) = Dia (substitute sigma p).
Proof. reflexivity. Qed.

Lemma substitute_boxdot :
  forall (A B : Type) (sigma : A -> formula B) (p : formula A),
    substitute sigma (Boxdot p) = Boxdot (substitute sigma p).
Proof. reflexivity. Qed.

Lemma substitute_box_iter :
  forall (A B : Type) (sigma : A -> formula B) n (p : formula A),
    substitute sigma (box_iter n p) = box_iter n (substitute sigma p).
Proof.
  intros A B sigma n; induction n as [|n IH]; intros p; simpl; auto.
  now rewrite IH.
Qed.

Lemma substitute_dia_iter :
  forall (A B : Type) (sigma : A -> formula B) n (p : formula A),
    substitute sigma (dia_iter n p) = dia_iter n (substitute sigma p).
Proof.
  intros A B sigma n; induction n as [|n IH]; intros p; simpl; auto.
  now rewrite IH.
Qed.

Fixpoint subformulas {AtomType} (p : formula AtomType)
  : list (formula AtomType) :=
  p ::
  match p with
  | Atom _ | Bottom => []
  | Imp q r => subformulas q ++ subformulas r
  | Box q => subformulas q
  end.

Lemma subformulas_self :
  forall (AtomType : Type) (p : formula AtomType),
    In p (subformulas p).
Proof. intros AtomType p; destruct p; simpl; auto. Qed.

Lemma subformulas_imp_left :
  forall (AtomType : Type) (p q r : formula AtomType),
    In r (subformulas p) -> In r (subformulas (Imp p q)).
Proof.
  intros; simpl; right; apply in_or_app; auto.
Qed.

Lemma subformulas_imp_right :
  forall (AtomType : Type) (p q r : formula AtomType),
    In r (subformulas q) -> In r (subformulas (Imp p q)).
Proof.
  intros; simpl; right; apply in_or_app; auto.
Qed.

Lemma subformulas_box :
  forall (AtomType : Type) (p q : formula AtomType),
    In q (subformulas p) -> In q (subformulas (Box p)).
Proof. intros; simpl; auto. Qed.

(** Subformula membership is transitive.  This is the closure property used
    by filtration: once a formula belongs to a closed target, all of its own
    subformulas belong to that target as well. *)
Lemma subformulas_trans :
  forall (AtomType : Type) (p q r : formula AtomType),
    In q (subformulas p) ->
    In r (subformulas q) ->
    In r (subformulas p).
Proof.
  intros AtomType p; induction p as [a | | p IHp q IHq | p IHp];
    intros s r Hs Hr; simpl in Hs |- *.
  - destruct Hs as [Hs | []].
    subst s. exact Hr.
  - destruct Hs as [Hs | []].
    subst s. exact Hr.
  - destruct Hs as [Hs | Hs].
    + subst s. exact Hr.
    + right. apply in_app_iff in Hs. apply in_app_iff.
      destruct Hs as [Hs | Hs].
      * left. eapply IHp; eauto.
      * right. eapply IHq; eauto.
  - destruct Hs as [Hs | Hs].
    + subst s. exact Hr.
    + right. eapply IHp; eauto.
Qed.

(** * Atoms and freshness *)

Fixpoint formula_atoms {AtomType : Type} (p : formula AtomType)
    : list AtomType :=
  match p with
  | Atom a => [a]
  | Bottom => []
  | Imp q r => formula_atoms q ++ formula_atoms r
  | Box q => formula_atoms q
  end.

Lemma formula_atom_in_atoms_iff_subformula :
  forall (AtomType : Type) (p : formula AtomType) (a : AtomType),
    In a (formula_atoms p) <-> In (Atom a) (subformulas p).
Proof.
  intros AtomType p; induction p as [b | | q IHq r IHr | q IHq];
    intro a; simpl.
  - split.
    + intros [-> | []]. now left.
    + intros [H | []]. injection H. now left.
  - split; [contradiction | intros [H | []]; discriminate].
  - rewrite in_app_iff, IHq, IHr. split.
    + intro H. right. now apply in_app_iff.
    + intros [H | H]; [discriminate | now apply in_app_iff].
  - rewrite IHq. split.
    + intro H. now right.
    + intros [H | H]; [discriminate | exact H].
Qed.

Fixpoint formula_fresh_atom (p : formula nat) : nat :=
  match p with
  | Atom a => S a
  | Bottom => 0
  | Imp q r => Nat.max (formula_fresh_atom q) (formula_fresh_atom r)
  | Box q => formula_fresh_atom q
  end.

Lemma formula_atom_lt_fresh : forall (p : formula nat) a,
  In a (formula_atoms p) -> a < formula_fresh_atom p.
Proof.
  induction p as [b | | q IHq r IHr | q IHq]; intros a Ha; simpl in *.
  - destruct Ha as [-> | []]. lia.
  - contradiction.
  - apply in_app_iff in Ha. destruct Ha as [Ha | Ha].
    + eapply Nat.lt_le_trans; [now apply IHq | apply Nat.le_max_l].
    + eapply Nat.lt_le_trans; [now apply IHr | apply Nat.le_max_r].
  - now apply IHq.
Qed.

Lemma formula_fresh_atom_not_in : forall p : formula nat,
  ~ In (formula_fresh_atom p) (formula_atoms p).
Proof.
  intros p H. pose proof (formula_atom_lt_fresh H). lia.
Qed.

Lemma formula_fresh_atom_not_subformula : forall (p : formula nat) a,
  In (Atom a) (subformulas p) -> formula_fresh_atom p <> a.
Proof.
  intros p a Ha Heq.
  apply (proj2 (formula_atom_in_atoms_iff_subformula p a)) in Ha.
  pose proof (formula_atom_lt_fresh Ha). lia.
Qed.
