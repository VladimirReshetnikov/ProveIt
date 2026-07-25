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

From Stdlib Require Import Arith.PeanoNat.
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
