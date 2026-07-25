(**
  Negation-normal modal formulas.

  This is an idiomatic Rocq port of
  Foundation/Modal/Formula/NNFormula.lean at the read-only source revision
  32e1a0956a8622fad067328ca1959729a7634428.  Positive and negative atoms,
  both constants, both Boolean connectives, and both modalities are primitive.
  Consequently [nn_neg] pushes negation all the way to atoms by construction.
*)

From Stdlib Require Import Arith.PeanoNat Lia Lists.List.
From FoundationModal Require Import Syntax.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive nnformula (AtomType : Type) : Type :=
| NAtom : AtomType -> nnformula AtomType
| NNegAtom : AtomType -> nnformula AtomType
| NBottom : nnformula AtomType
| NTop : nnformula AtomType
| NOr : nnformula AtomType -> nnformula AtomType -> nnformula AtomType
| NAnd : nnformula AtomType -> nnformula AtomType -> nnformula AtomType
| NBox : nnformula AtomType -> nnformula AtomType
| NDia : nnformula AtomType -> nnformula AtomType.

Arguments NAtom {AtomType} _.
Arguments NNegAtom {AtomType} _.
Arguments NBottom {AtomType}.
Arguments NTop {AtomType}.
Arguments NOr {AtomType} _ _.
Arguments NAnd {AtomType} _ _.
Arguments NBox {AtomType} _.
Arguments NDia {AtomType} _.

Definition nnformula_eq_dec {AtomType}
    (atom_eq_dec : forall a b : AtomType, {a = b} + {a <> b})
    : forall p q : nnformula AtomType, {p = q} + {p <> q}.
Proof. decide equality. Defined.

(** Boolean negation is a structural involution. *)
Fixpoint nn_neg {AtomType} (p : nnformula AtomType) : nnformula AtomType :=
  match p with
  | NAtom a => NNegAtom a
  | NNegAtom a => NAtom a
  | NBottom => NTop
  | NTop => NBottom
  | NOr q r => NAnd (nn_neg q) (nn_neg r)
  | NAnd q r => NOr (nn_neg q) (nn_neg r)
  | NBox q => NDia (nn_neg q)
  | NDia q => NBox (nn_neg q)
  end.

Definition nn_imp {AtomType} (p q : nnformula AtomType)
    : nnformula AtomType :=
  NOr (nn_neg p) q.

Definition nn_iff {AtomType} (p q : nnformula AtomType)
    : nnformula AtomType :=
  NAnd (nn_imp p q) (nn_imp q p).

Lemma nn_neg_atom :
  forall (AtomType : Type) (a : AtomType),
    nn_neg (NAtom a) = NNegAtom a.
Proof. reflexivity. Qed.

Lemma nn_neg_natom :
  forall (AtomType : Type) (a : AtomType),
    nn_neg (NNegAtom a) = NAtom a.
Proof. reflexivity. Qed.

Lemma nn_neg_or :
  forall (AtomType : Type) (p q : nnformula AtomType),
    nn_neg (NOr p q) = NAnd (nn_neg p) (nn_neg q).
Proof. reflexivity. Qed.

Lemma nn_neg_and :
  forall (AtomType : Type) (p q : nnformula AtomType),
    nn_neg (NAnd p q) = NOr (nn_neg p) (nn_neg q).
Proof. reflexivity. Qed.

Lemma nn_neg_box :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_neg (NBox p) = NDia (nn_neg p).
Proof. reflexivity. Qed.

Lemma nn_neg_dia :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_neg (NDia p) = NBox (nn_neg p).
Proof. reflexivity. Qed.

Theorem nn_neg_involutive :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_neg (nn_neg p) = p.
Proof.
  intros AtomType p; induction p; simpl; now f_equal.
Qed.

Corollary nn_neg_injective :
  forall (AtomType : Type) (p q : nnformula AtomType),
    nn_neg p = nn_neg q <-> p = q.
Proof.
  intros AtomType p q; split.
  - intro H. apply (f_equal nn_neg) in H.
    now rewrite !nn_neg_involutive in H.
  - now intros ->.
Qed.

(** Forget the normal-form representation and recover an ordinary modal
    formula.  Defined connectives in [Syntax] make this translation compact. *)
Fixpoint nn_to_formula {AtomType} (p : nnformula AtomType)
    : formula AtomType :=
  match p with
  | NAtom a => Atom a
  | NNegAtom a => Neg (Atom a)
  | NBottom => Bottom
  | NTop => Top
  | NOr q r => Or (nn_to_formula q) (nn_to_formula r)
  | NAnd q r => And (nn_to_formula q) (nn_to_formula r)
  | NBox q => Box (nn_to_formula q)
  | NDia q => Dia (nn_to_formula q)
  end.

Lemma nn_to_formula_atom :
  forall (AtomType : Type) (a : AtomType),
    nn_to_formula (NAtom a) = Atom a.
Proof. reflexivity. Qed.

Lemma nn_to_formula_natom :
  forall (AtomType : Type) (a : AtomType),
    nn_to_formula (NNegAtom a) = Neg (Atom a).
Proof. reflexivity. Qed.

Lemma nn_to_formula_bottom :
  forall AtomType : Type,
    nn_to_formula (@NBottom AtomType) = Bottom.
Proof. reflexivity. Qed.

Lemma nn_to_formula_top :
  forall AtomType : Type,
    nn_to_formula (@NTop AtomType) = Top.
Proof. reflexivity. Qed.

(** Every primitive modal formula has a negation-normal presentation. *)
Fixpoint formula_to_nnf {AtomType} (p : formula AtomType)
    : nnformula AtomType :=
  match p with
  | Atom a => NAtom a
  | Bottom => NBottom
  | Imp q r => nn_imp (formula_to_nnf q) (formula_to_nnf r)
  | Box q => NBox (formula_to_nnf q)
  end.

Lemma formula_to_nnf_atom :
  forall (AtomType : Type) (a : AtomType),
    formula_to_nnf (Atom a) = NAtom a.
Proof. reflexivity. Qed.

Lemma formula_to_nnf_bottom :
  forall AtomType : Type,
    formula_to_nnf (@Bottom AtomType) = NBottom.
Proof. reflexivity. Qed.

(** * Modal shape and degree *)

Definition nn_is_prebox {AtomType} (p : nnformula AtomType) : Prop :=
  match p with
  | NBox _ => True
  | _ => False
  end.

Definition nn_is_predia {AtomType} (p : nnformula AtomType) : Prop :=
  match p with
  | NDia _ => True
  | _ => False
  end.

Lemma nn_is_prebox_exists :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_prebox p -> exists q, p = NBox q.
Proof.
  intros AtomType p H; destruct p; simpl in H; try contradiction.
  eauto.
Qed.

Lemma nn_is_predia_exists :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_predia p -> exists q, p = NDia q.
Proof.
  intros AtomType p H; destruct p; simpl in H; try contradiction.
  eauto.
Qed.

Fixpoint nn_degree {AtomType} (p : nnformula AtomType) : nat :=
  match p with
  | NAtom _ | NNegAtom _ | NBottom | NTop => 0
  | NOr q r | NAnd q r => Nat.max (nn_degree q) (nn_degree r)
  | NBox q | NDia q => S (nn_degree q)
  end.

Lemma nn_degree_neg :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_degree (nn_neg p) = nn_degree p.
Proof.
  intros AtomType p; induction p; simpl; now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.

Lemma nn_degree_to_formula :
  forall (AtomType : Type) (p : nnformula AtomType),
    modal_degree (nn_to_formula p) = nn_degree p.
Proof.
  intros AtomType p; induction p; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold Or, Neg; simpl.
    now rewrite Nat.max_0_r, IHp1, IHp2.
  - unfold And, Neg; simpl.
    now rewrite !Nat.max_0_r, IHp1, IHp2.
  - now rewrite IHp.
  - unfold Dia, Neg; simpl.
    now rewrite !Nat.max_0_r, IHp.
Qed.

(** * Modal conjunctive and disjunctive normal-form predicates

    Foundation uses finite big conjunctions and disjunctions.  The folds below
    retain singleton formulas literally, which makes the elementary normal-
    form introduction lemmas computational equalities. *)

Fixpoint nn_disjunction {AtomType} (ps : list (nnformula AtomType))
    : nnformula AtomType :=
  match ps with
  | [] => NBottom
  | [p] => p
  | p :: rest => NOr p (nn_disjunction rest)
  end.

Fixpoint nn_conjunction {AtomType} (ps : list (nnformula AtomType))
    : nnformula AtomType :=
  match ps with
  | [] => NTop
  | [p] => p
  | p :: rest => NAnd p (nn_conjunction rest)
  end.

Definition nn_modal_literal {AtomType} (p : nnformula AtomType) : Prop :=
  nn_is_prebox p \/ nn_is_predia p \/ nn_degree p = 0.

Definition nn_is_modal_cnf_part {AtomType} (p : nnformula AtomType) : Prop :=
  exists ps, Forall nn_modal_literal ps /\ p = nn_disjunction ps.

Definition nn_is_modal_cnf {AtomType} (p : nnformula AtomType) : Prop :=
  exists ps, Forall nn_is_modal_cnf_part ps /\ p = nn_conjunction ps.

Fixpoint nn_is_modal_dnf_part {AtomType} (p : nnformula AtomType) : Prop :=
  match p with
  | NAnd q r => nn_is_modal_dnf_part q /\ nn_is_modal_dnf_part r
  | _ => nn_modal_literal p
  end.

Fixpoint nn_is_modal_dnf {AtomType} (p : nnformula AtomType) : Prop :=
  match p with
  | NOr q r => nn_is_modal_dnf q /\ nn_is_modal_dnf r
  | _ => nn_is_modal_dnf_part p
  end.

Lemma nn_modal_literal_atom :
  forall (AtomType : Type) (a : AtomType), nn_modal_literal (NAtom a).
Proof. intros; unfold nn_modal_literal; simpl; auto. Qed.

Lemma nn_modal_literal_natom :
  forall (AtomType : Type) (a : AtomType), nn_modal_literal (NNegAtom a).
Proof. intros; unfold nn_modal_literal; simpl; auto. Qed.

Lemma nn_modal_literal_bottom :
  forall AtomType : Type, nn_modal_literal (@NBottom AtomType).
Proof. intros; unfold nn_modal_literal; simpl; auto. Qed.

Lemma nn_modal_literal_top :
  forall AtomType : Type, nn_modal_literal (@NTop AtomType).
Proof. intros; unfold nn_modal_literal; simpl; auto. Qed.

Lemma nn_modal_literal_box :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_modal_literal (NBox p).
Proof. intros; unfold nn_modal_literal, nn_is_prebox; auto. Qed.

Lemma nn_modal_literal_dia :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_modal_literal (NDia p).
Proof. intros; unfold nn_modal_literal, nn_is_prebox, nn_is_predia; auto. Qed.

Lemma nn_modal_cnf_part_singleton :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_modal_literal p -> nn_is_modal_cnf_part p.
Proof.
  intros AtomType p Hp. exists [p]; split; simpl; auto.
Qed.

Lemma nn_modal_cnf_singleton :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_modal_cnf_part p -> nn_is_modal_cnf p.
Proof.
  intros AtomType p Hp. exists [p]; split; simpl; auto.
Qed.

Lemma nn_dnf_part_degree_zero :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_degree p = 0 -> nn_is_modal_dnf_part p.
Proof.
  fix IH 2.
  intros AtomType p H.
  destruct p as [a | a | | | p q | p q | p | p]; simpl in H |- *.
  - right; right; reflexivity.
  - right; right; reflexivity.
  - right; right; reflexivity.
  - right; right; reflexivity.
  - right; right; exact H.
  - split.
    + apply IH. pose proof (Nat.le_max_l (nn_degree p) (nn_degree q)).
      lia.
    + apply IH. pose proof (Nat.le_max_r (nn_degree p) (nn_degree q)).
      lia.
  - left; exact I.
  - right; left; exact I.
Qed.

Lemma nn_modal_cnf_atom :
  forall (AtomType : Type) (a : AtomType), nn_is_modal_cnf (NAtom a).
Proof.
  intros. apply nn_modal_cnf_singleton, nn_modal_cnf_part_singleton.
  apply nn_modal_literal_atom.
Qed.

Lemma nn_modal_cnf_natom :
  forall (AtomType : Type) (a : AtomType), nn_is_modal_cnf (NNegAtom a).
Proof.
  intros. apply nn_modal_cnf_singleton, nn_modal_cnf_part_singleton.
  apply nn_modal_literal_natom.
Qed.

Lemma nn_modal_cnf_bottom :
  forall AtomType : Type, nn_is_modal_cnf (@NBottom AtomType).
Proof.
  intros. apply nn_modal_cnf_singleton, nn_modal_cnf_part_singleton.
  apply nn_modal_literal_bottom.
Qed.

Lemma nn_modal_cnf_top :
  forall AtomType : Type, nn_is_modal_cnf (@NTop AtomType).
Proof.
  intros. apply nn_modal_cnf_singleton, nn_modal_cnf_part_singleton.
  apply nn_modal_literal_top.
Qed.

Lemma nn_modal_cnf_box :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_modal_cnf (NBox p).
Proof.
  intros. apply nn_modal_cnf_singleton, nn_modal_cnf_part_singleton.
  apply nn_modal_literal_box.
Qed.

Lemma nn_modal_cnf_dia :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_modal_cnf (NDia p).
Proof.
  intros. apply nn_modal_cnf_singleton, nn_modal_cnf_part_singleton.
  apply nn_modal_literal_dia.
Qed.

Lemma nn_modal_dnf_atom :
  forall (AtomType : Type) (a : AtomType), nn_is_modal_dnf (NAtom a).
Proof. intros; simpl; apply nn_modal_literal_atom. Qed.

Lemma nn_modal_dnf_natom :
  forall (AtomType : Type) (a : AtomType), nn_is_modal_dnf (NNegAtom a).
Proof. intros; simpl; apply nn_modal_literal_natom. Qed.

Lemma nn_modal_dnf_bottom :
  forall AtomType : Type, nn_is_modal_dnf (@NBottom AtomType).
Proof. intros; simpl; apply nn_modal_literal_bottom. Qed.

Lemma nn_modal_dnf_top :
  forall AtomType : Type, nn_is_modal_dnf (@NTop AtomType).
Proof. intros; simpl; apply nn_modal_literal_top. Qed.

Lemma nn_modal_dnf_box :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_modal_dnf (NBox p).
Proof. intros; simpl; apply nn_modal_literal_box. Qed.

Lemma nn_modal_dnf_dia :
  forall (AtomType : Type) (p : nnformula AtomType),
    nn_is_modal_dnf (NDia p).
Proof. intros; simpl; apply nn_modal_literal_dia. Qed.
