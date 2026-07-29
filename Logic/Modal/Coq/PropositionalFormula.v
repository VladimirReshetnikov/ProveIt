(**
  Primitive propositional formulas.

  This module begins the port of the pinned Foundation module
  [Propositional/Formula/Basic.lean].  Unlike the modal syntax, conjunction
  and disjunction are primitive, so the datatype supports Minimal and
  Intuitionistic developments without a classical encoding.

  Substitutions are generalized to change the atom type.  Subformula sets
  use duplicate-tolerant lists, removing every equality-decision premise from
  the structural API.
*)

From Stdlib Require Import Lists.List Arith.PeanoNat.
From FoundationModal Require Import GenericSemantics GenericLogicSymbol.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive pformula (Atom : Type) : Type :=
| PAtom : Atom -> pformula Atom
| PFalsum : pformula Atom
| PAnd : pformula Atom -> pformula Atom -> pformula Atom
| POr : pformula Atom -> pformula Atom -> pformula Atom
| PImp : pformula Atom -> pformula Atom -> pformula Atom.

Arguments PAtom {Atom} _.
Arguments PFalsum {Atom}.
Arguments PAnd {Atom} _ _.
Arguments POr {Atom} _ _.
Arguments PImp {Atom} _ _.

Definition pneg {Atom : Type} (p : pformula Atom) : pformula Atom :=
  PImp p PFalsum.

Definition ptop {Atom : Type} : pformula Atom :=
  PImp PFalsum PFalsum.

Definition pformula_connectives (Atom : Type) :
    generic_connectives (pformula Atom) :=
  {| generic_top := ptop;
     generic_bottom := PFalsum;
     generic_and := PAnd;
     generic_or := POr;
     generic_imp := PImp;
     generic_neg := pneg |}.

Lemma pformula_and_inj :
  forall (Atom : Type) (p1 p2 q1 q2 : pformula Atom),
    PAnd p1 p2 = PAnd q1 q2 <-> p1 = q1 /\ p2 = q2.
Proof.
  intros Atom p1 p2 q1 q2; split.
  - intro H. inversion H. now split.
  - intros [-> ->]. reflexivity.
Qed.

Lemma pformula_or_inj :
  forall (Atom : Type) (p1 p2 q1 q2 : pformula Atom),
    POr p1 p2 = POr q1 q2 <-> p1 = q1 /\ p2 = q2.
Proof.
  intros Atom p1 p2 q1 q2; split.
  - intro H. inversion H. now split.
  - intros [-> ->]. reflexivity.
Qed.

Lemma pformula_imp_inj :
  forall (Atom : Type) (p1 p2 q1 q2 : pformula Atom),
    PImp p1 p2 = PImp q1 q2 <-> p1 = q1 /\ p2 = q2.
Proof.
  intros Atom p1 p2 q1 q2; split.
  - intro H. inversion H. now split.
  - intros [-> ->]. reflexivity.
Qed.

Lemma pformula_neg_inj :
  forall (Atom : Type) (p q : pformula Atom),
    pneg p = pneg q <-> p = q.
Proof.
  intros Atom p q. unfold pneg. rewrite pformula_imp_inj.
  split; [tauto | intro H; now split].
Qed.

Lemma pformula_neg_def :
  forall (Atom : Type) (p : pformula Atom),
    pneg p = PImp p PFalsum.
Proof. reflexivity. Qed.

Lemma pformula_top_def :
  forall Atom : Type,
    @ptop Atom = PImp PFalsum PFalsum.
Proof. reflexivity. Qed.

Lemma pformula_iff_def :
  forall (Atom : Type) (p q : pformula Atom),
    generic_formula_iff (pformula_connectives Atom) p q =
    PAnd (PImp p q) (PImp q p).
Proof. reflexivity. Qed.

(** * Complexity and decidable equality *)

Fixpoint pformula_complexity {Atom : Type}
    (p : pformula Atom) : nat :=
  match p with
  | PAtom _ | PFalsum => 0
  | PAnd q r | POr q r | PImp q r =>
      S (Nat.max (pformula_complexity q) (pformula_complexity r))
  end.

Lemma pformula_complexity_atom :
  forall (Atom : Type) (a : Atom), pformula_complexity (PAtom a) = 0.
Proof. reflexivity. Qed.

Lemma pformula_complexity_bottom :
  forall Atom : Type, pformula_complexity (@PFalsum Atom) = 0.
Proof. reflexivity. Qed.

Lemma pformula_complexity_and :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_complexity (PAnd p q) =
    S (Nat.max (pformula_complexity p) (pformula_complexity q)).
Proof. reflexivity. Qed.

Lemma pformula_complexity_or :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_complexity (POr p q) =
    S (Nat.max (pformula_complexity p) (pformula_complexity q)).
Proof. reflexivity. Qed.

Lemma pformula_complexity_imp :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_complexity (PImp p q) =
    S (Nat.max (pformula_complexity p) (pformula_complexity q)).
Proof. reflexivity. Qed.

Fixpoint pformula_eq_dec {Atom : Type}
    (atom_eq_dec : forall a b : Atom, {a = b} + {a <> b})
    (p q : pformula Atom) : {p = q} + {p <> q}.
Proof. decide equality. Defined.

(** * Letterless formulas *)

Fixpoint pformula_letterless {Atom : Type}
    (p : pformula Atom) : Prop :=
  match p with
  | PAtom _ => False
  | PFalsum => True
  | PAnd q r | POr q r | PImp q r =>
      pformula_letterless q /\ pformula_letterless r
  end.

Lemma pformula_atom_not_letterless :
  forall (Atom : Type) (a : Atom), ~ pformula_letterless (PAtom a).
Proof. intros Atom a H. exact H. Qed.

Lemma pformula_bottom_letterless :
  forall Atom : Type, pformula_letterless (@PFalsum Atom).
Proof. intros Atom. exact I. Qed.

Lemma pformula_top_letterless :
  forall Atom : Type, pformula_letterless (@ptop Atom).
Proof. intros Atom. now split. Qed.

Lemma pformula_and_letterless_iff :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_letterless (PAnd p q) <->
    pformula_letterless p /\ pformula_letterless q.
Proof. reflexivity. Qed.

Lemma pformula_or_letterless_iff :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_letterless (POr p q) <->
    pformula_letterless p /\ pformula_letterless q.
Proof. reflexivity. Qed.

Lemma pformula_imp_letterless_iff :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_letterless (PImp p q) <->
    pformula_letterless p /\ pformula_letterless q.
Proof. reflexivity. Qed.

Lemma pformula_neg_letterless_iff :
  forall (Atom : Type) (p : pformula Atom),
    pformula_letterless (pneg p) <-> pformula_letterless p.
Proof.
  intros Atom p. unfold pneg. simpl. tauto.
Qed.

(** * List-backed subformula closure *)

Fixpoint pformula_subformulas {Atom : Type}
    (p : pformula Atom) : list (pformula Atom) :=
  p ::
  match p with
  | PAtom _ | PFalsum => []
  | PAnd q r | POr q r | PImp q r =>
      pformula_subformulas q ++ pformula_subformulas r
  end.

Definition pformula_is_subformula {Atom : Type}
    (q p : pformula Atom) : Prop :=
  In q (pformula_subformulas p).

Lemma pformula_subformulas_self :
  forall (Atom : Type) (p : pformula Atom),
    pformula_is_subformula p p.
Proof.
  intros Atom p. unfold pformula_is_subformula.
  destruct p; simpl; now left.
Qed.

Lemma pformula_subformulas_left :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_is_subformula p (PAnd p q) /\
    pformula_is_subformula p (POr p q) /\
    pformula_is_subformula p (PImp p q).
Proof.
  intros Atom p q. unfold pformula_is_subformula; simpl.
  repeat split; right; apply in_app_iff; left;
    apply pformula_subformulas_self.
Qed.

Lemma pformula_subformulas_right :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_is_subformula q (PAnd p q) /\
    pformula_is_subformula q (POr p q) /\
    pformula_is_subformula q (PImp p q).
Proof.
  intros Atom p q. unfold pformula_is_subformula; simpl.
  repeat split; right; apply in_app_iff; right;
    apply pformula_subformulas_self.
Qed.

Lemma pformula_subformula_trans :
  forall (Atom : Type) (p q r : pformula Atom),
    pformula_is_subformula q p ->
    pformula_is_subformula r q ->
    pformula_is_subformula r p.
Proof.
  intros Atom p; induction p as [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq];
    intros u r Hu Hr; unfold pformula_is_subformula in *; simpl in Hu |- *.
  - destruct Hu as [<- | Hfalse]; [exact Hr | contradiction].
  - destruct Hu as [<- | Hfalse]; [exact Hr | contradiction].
  - destruct Hu as [<- | Hu]; [exact Hr |].
    apply in_app_iff in Hu. right. apply in_app_iff.
    destruct Hu as [Hu | Hu].
    + left. exact (IHp u r Hu Hr).
    + right. exact (IHq u r Hu Hr).
  - destruct Hu as [<- | Hu]; [exact Hr |].
    apply in_app_iff in Hu. right. apply in_app_iff.
    destruct Hu as [Hu | Hu].
    + left. exact (IHp u r Hu Hr).
    + right. exact (IHq u r Hu Hr).
  - destruct Hu as [<- | Hu]; [exact Hr |].
    apply in_app_iff in Hu. right. apply in_app_iff.
    destruct Hu as [Hu | Hu].
    + left. exact (IHp u r Hu Hr).
    + right. exact (IHq u r Hu Hr).
Qed.

Lemma pformula_subformula_and_components :
  forall (Atom : Type) (whole p q : pformula Atom),
    pformula_is_subformula (PAnd p q) whole ->
    pformula_is_subformula p whole /\ pformula_is_subformula q whole.
Proof.
  intros Atom whole p q H; split.
  - eapply pformula_subformula_trans; [exact H |].
    exact (proj1 (pformula_subformulas_left p q)).
  - eapply pformula_subformula_trans; [exact H |].
    exact (proj1 (pformula_subformulas_right p q)).
Qed.

Lemma pformula_subformula_or_components :
  forall (Atom : Type) (whole p q : pformula Atom),
    pformula_is_subformula (POr p q) whole ->
    pformula_is_subformula p whole /\ pformula_is_subformula q whole.
Proof.
  intros Atom whole p q H; split.
  - eapply pformula_subformula_trans; [exact H |].
    exact (proj1 (proj2 (pformula_subformulas_left p q))).
  - eapply pformula_subformula_trans; [exact H |].
    exact (proj1 (proj2 (pformula_subformulas_right p q))).
Qed.

Lemma pformula_subformula_imp_components :
  forall (Atom : Type) (whole p q : pformula Atom),
    pformula_is_subformula (PImp p q) whole ->
    pformula_is_subformula p whole /\ pformula_is_subformula q whole.
Proof.
  intros Atom whole p q H; split.
  - eapply pformula_subformula_trans; [exact H |].
    exact (proj2 (proj2 (pformula_subformulas_left p q))).
  - eapply pformula_subformula_trans; [exact H |].
    exact (proj2 (proj2 (pformula_subformulas_right p q))).
Qed.

Definition pformula_subformula_closed {Atom : Type}
    (Gamma : list (pformula Atom)) : Prop :=
  forall p q,
    In p Gamma -> pformula_is_subformula q p -> In q Gamma.

Lemma pformula_subformulas_closed :
  forall (Atom : Type) (p : pformula Atom),
    pformula_subformula_closed (pformula_subformulas p).
Proof.
  intros Atom p q r Hq Hr.
  exact (pformula_subformula_trans Hq Hr).
Qed.

(** * Heterogeneous substitution *)

Definition psubstitution (A B : Type) := A -> pformula B.

Definition psubstitution_id {A : Type} : psubstitution A A := PAtom.

Fixpoint pformula_substitute {A B : Type}
    (sigma : psubstitution A B) (p : pformula A) : pformula B :=
  match p with
  | PAtom a => sigma a
  | PFalsum => PFalsum
  | PAnd q r => PAnd (pformula_substitute sigma q)
                      (pformula_substitute sigma r)
  | POr q r => POr (pformula_substitute sigma q)
                    (pformula_substitute sigma r)
  | PImp q r => PImp (pformula_substitute sigma q)
                      (pformula_substitute sigma r)
  end.

Lemma pformula_substitute_atom :
  forall (A B : Type) (sigma : psubstitution A B) (a : A),
    pformula_substitute sigma (PAtom a) = sigma a.
Proof. reflexivity. Qed.

Lemma pformula_substitute_bottom :
  forall (A B : Type) (sigma : psubstitution A B),
    pformula_substitute sigma (@PFalsum A) = @PFalsum B.
Proof. reflexivity. Qed.

Lemma pformula_substitute_top :
  forall (A B : Type) (sigma : psubstitution A B),
    pformula_substitute sigma (@ptop A) = @ptop B.
Proof. reflexivity. Qed.

Lemma pformula_substitute_neg :
  forall (A B : Type) (sigma : psubstitution A B) (p : pformula A),
    pformula_substitute sigma (pneg p) =
    pneg (pformula_substitute sigma p).
Proof. reflexivity. Qed.

Lemma pformula_substitute_and :
  forall (A B : Type) (sigma : psubstitution A B)
         (p q : pformula A),
    pformula_substitute sigma (PAnd p q) =
    PAnd (pformula_substitute sigma p) (pformula_substitute sigma q).
Proof. reflexivity. Qed.

Lemma pformula_substitute_or :
  forall (A B : Type) (sigma : psubstitution A B)
         (p q : pformula A),
    pformula_substitute sigma (POr p q) =
    POr (pformula_substitute sigma p) (pformula_substitute sigma q).
Proof. reflexivity. Qed.

Lemma pformula_substitute_imp :
  forall (A B : Type) (sigma : psubstitution A B)
         (p q : pformula A),
    pformula_substitute sigma (PImp p q) =
    PImp (pformula_substitute sigma p) (pformula_substitute sigma q).
Proof. reflexivity. Qed.

Lemma pformula_substitute_iff :
  forall (A B : Type) (sigma : psubstitution A B)
         (p q : pformula A),
    pformula_substitute sigma
      (generic_formula_iff (pformula_connectives A) p q) =
    generic_formula_iff (pformula_connectives B)
      (pformula_substitute sigma p) (pformula_substitute sigma q).
Proof. reflexivity. Qed.

Lemma pformula_substitute_id :
  forall (A : Type) (p : pformula A),
    pformula_substitute psubstitution_id p = p.
Proof.
  intros A p. unfold psubstitution_id.
  induction p; simpl; congruence.
Qed.

Definition psubstitution_compose {A B C : Type}
    (tau : psubstitution B C) (sigma : psubstitution A B) :
    psubstitution A C :=
  fun a => pformula_substitute tau (sigma a).

Lemma pformula_substitute_compose :
  forall (A B C : Type)
         (tau : psubstitution B C) (sigma : psubstitution A B)
         (p : pformula A),
    pformula_substitute (psubstitution_compose tau sigma) p =
    pformula_substitute tau (pformula_substitute sigma p).
Proof.
  intros A B C tau sigma p. unfold psubstitution_compose.
  induction p; simpl; congruence.
Qed.

Lemma pformula_substitute_letterless :
  forall (A B : Type) (sigma : psubstitution A B),
    (forall a, pformula_letterless (sigma a)) ->
    forall p : pformula A,
      pformula_letterless (pformula_substitute sigma p).
Proof.
  intros A B sigma Hsigma p; induction p; simpl; auto; now split.
Qed.
