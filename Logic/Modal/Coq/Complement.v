(**
  Syntactic complements and complement-closed finite contexts.

  This is the dependency-free part of
  Foundation/Modal/Formula/Complement.lean.  Foundation's complement removes
  one outer syntactic negation when present and adds one otherwise; it is not
  quotienting formulas by double-negation equivalence.  Lists provide the
  finite-context representation here, so no decidable equality on atoms is
  needed.

  The source file's final derivability lemmas depend on Foundation's abstract
  classical entailment layer.  Their semantic analogues are included now;
  proof-theoretic versions belong with the Hilbert port.
*)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import Syntax Kripke.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

(** Remove exactly one outer [Imp _ Bottom], or add such an implication. *)
Definition complement {AtomType} (p : formula AtomType) : formula AtomType :=
  match p with
  | Imp q r =>
      match r with
      | Bottom => q
      | _ => Neg p
      end
  | _ => Neg p
  end.

Lemma complement_neg :
  forall (AtomType : Type) (p : formula AtomType),
    complement (Neg p) = p.
Proof. reflexivity. Qed.

Lemma complement_bottom :
  forall AtomType,
    complement (@Bottom AtomType) = Neg Bottom.
Proof. reflexivity. Qed.

Lemma complement_box :
  forall (AtomType : Type) (p : formula AtomType),
    complement (Box p) = Neg (Box p).
Proof. reflexivity. Qed.

Lemma complement_imp_nonbottom :
  forall (AtomType : Type) (p q : formula AtomType),
    q <> Bottom -> complement (Imp p q) = Neg (Imp p q).
Proof.
  intros AtomType p q Hq. destruct q; simpl; try reflexivity.
  contradiction.
Qed.

Lemma complement_imp_bottom :
  forall (AtomType : Type) (p : formula AtomType),
    complement (Imp p Bottom) = p.
Proof. reflexivity. Qed.

Lemma complement_resort_box :
  forall (AtomType : Type) (p q : formula AtomType),
    complement p = Box q -> p = Neg (Box q).
Proof.
  intros AtomType p q H.
  destruct p as [a | | p r | p]; simpl in H; try discriminate.
  destruct r; simpl in H; try discriminate.
  inversion H. reflexivity.
Qed.

Lemma complement_cases :
  forall (AtomType : Type) (p : formula AtomType),
    complement p = Neg p \/ exists q, Neg q = p.
Proof.
  intros AtomType p.
  destruct p as [a | | p q | p]; simpl; try (left; reflexivity).
  destruct q; simpl; try (left; reflexivity).
  right. exists p. reflexivity.
Qed.

(** A finite context together with every syntactic complement. *)
Definition complementary {AtomType} (P : list (formula AtomType))
    : list (formula AtomType) :=
  P ++ map complement P.

Lemma complementary_mem :
  forall (AtomType : Type) (P : list (formula AtomType)) p,
    In p P -> In p (complementary P).
Proof.
  intros AtomType P p Hp. unfold complementary.
  apply in_or_app. now left.
Qed.

Lemma complementary_comp :
  forall (AtomType : Type) (P : list (formula AtomType)) p,
    In p P -> In (complement p) (complementary P).
Proof.
  intros AtomType P p Hp. unfold complementary.
  apply in_or_app. right. apply in_map. exact Hp.
Qed.

Lemma complementary_member_cases :
  forall (AtomType : Type) (P : list (formula AtomType)) p,
    In p (complementary P) ->
    In p P \/ exists q, In q P /\ complement q = p.
Proof.
  intros AtomType P p Hp. unfold complementary in Hp.
  apply in_app_iff in Hp. destruct Hp as [Hp | Hp].
  - now left.
  - right. apply in_map_iff in Hp.
    destruct Hp as [q [Hq Hmem]]. exists q. auto.
Qed.

Lemma complementary_mem_box :
  forall (AtomType : Type) (P : list (formula AtomType)) p,
    (forall q r, In (Imp q r) P -> In q P) ->
    In (Box p) (complementary P) ->
    In (Box p) P.
Proof.
  intros AtomType P p Hantecedent Hbox.
  destruct (complementary_member_cases Hbox)
    as [Hdirect | [q [Hq Hcomp]]]; [exact Hdirect |].
  apply complement_resort_box in Hcomp. subst q.
  exact (Hantecedent (Box p) Bottom Hq).
Qed.

Record complementary_closed {AtomType}
    (P S : list (formula AtomType)) : Prop := {
  complementary_closed_subset :
    forall p, In p P -> In p (complementary S);
  complementary_closed_either :
    forall p, In p S -> In p P \/ In (complement p) P
}.

Definition subformulas_complementary_closed {AtomType}
    (P : list (formula AtomType)) (p : formula AtomType) : Prop :=
  complementary_closed P (subformulas p).

(** A formula and its syntactic complement cannot both hold. *)
Lemma satisfies_complement_incompatible :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F) w p,
    satisfies F V w p ->
    satisfies F V w (complement p) -> False.
Proof.
  intros AtomType F V w p.
  destruct p as [a | | p q | p]; simpl; try tauto.
  destruct q; simpl; tauto.
Qed.

Lemma satisfies_neg_complement_incompatible :
  forall (AtomType : Type) (F : frame) (V : valuation AtomType F) w p,
    satisfies F V w (Neg p) ->
    satisfies F V w (Neg (complement p)) -> False.
Proof.
  intros AtomType F V w p.
  destruct p as [a | | p q | p]; simpl; try tauto.
  destruct q; simpl; tauto.
Qed.
