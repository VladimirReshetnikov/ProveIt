(** A generic propositional literal tree.

    This module ports the mathematical core of [Foundation/Meta/Lit.lean].
    The source uses Lean expressions as atoms and quotes the result back into
    the elaborator.  Separating the syntax from quotation gives a more useful
    Coq interface: atoms may have any type and a single fold interprets the
    tree in any target connective algebra.

    The explicit biconditional constructor is intentionally distinct from
    the biconditional derived by [generic_literal_connectives], matching the
    source representation.  Its interpretation is the target's standard
    derived biconditional. *)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import GenericSemantics GenericLogicSymbol.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive generic_literal_formula@{u} (A : Type@{u}) : Type@{u} :=
| GLF_atom : A -> generic_literal_formula A
| GLF_top : generic_literal_formula A
| GLF_bottom : generic_literal_formula A
| GLF_and : generic_literal_formula A -> generic_literal_formula A ->
    generic_literal_formula A
| GLF_or : generic_literal_formula A -> generic_literal_formula A ->
    generic_literal_formula A
| GLF_neg : generic_literal_formula A -> generic_literal_formula A
| GLF_imp : generic_literal_formula A -> generic_literal_formula A ->
    generic_literal_formula A
| GLF_iff : generic_literal_formula A -> generic_literal_formula A ->
    generic_literal_formula A.

Arguments GLF_atom {A} _.
Arguments GLF_top {A}.
Arguments GLF_bottom {A}.
Arguments GLF_and {A} _ _.
Arguments GLF_or {A} _ _.
Arguments GLF_neg {A} _.
Arguments GLF_imp {A} _ _.
Arguments GLF_iff {A} _ _.

(** The source [LogicalConnective (Litform A)] instance.  As upstream, the
    ordinary derived biconditional is built from [GLF_and] and [GLF_imp]; it
    does not collapse to the separate [GLF_iff] syntax constructor. *)
Definition generic_literal_connectives {A : Type} :
    generic_connectives (generic_literal_formula A) :=
  {| generic_top := GLF_top;
     generic_bottom := GLF_bottom;
     generic_and := GLF_and;
     generic_or := GLF_or;
     generic_imp := GLF_imp;
     generic_neg := GLF_neg |}.

(** Generalized source [Litform.toExpr]. *)
Fixpoint generic_literal_denote {A F : Type}
    (C : generic_connectives F) (atom : A -> F)
    (p : generic_literal_formula A) : F :=
  match p with
  | GLF_atom a => atom a
  | GLF_top => generic_top C
  | GLF_bottom => generic_bottom C
  | GLF_and q r => generic_and C
      (generic_literal_denote C atom q)
      (generic_literal_denote C atom r)
  | GLF_or q r => generic_or C
      (generic_literal_denote C atom q)
      (generic_literal_denote C atom r)
  | GLF_neg q => generic_neg C (generic_literal_denote C atom q)
  | GLF_imp q r => generic_imp C
      (generic_literal_denote C atom q)
      (generic_literal_denote C atom r)
  | GLF_iff q r => generic_formula_iff C
      (generic_literal_denote C atom q)
      (generic_literal_denote C atom r)
  end.

(** Primitive connective preservation packages the fold as a homomorphism.
    The explicit [GLF_iff] case is available through its own computation law
    below, exactly as in the source quotation function. *)
Definition generic_literal_denote_hom {A F : Type}
    (C : generic_connectives F) (atom : A -> F) :
    generic_connective_hom (@generic_literal_connectives A) C.
Proof.
  refine {| generic_connective_hom_apply :=
      generic_literal_denote C atom |}; reflexivity.
Defined.

Lemma generic_literal_denote_iff : forall (A F : Type)
    (C : generic_connectives F) (atom : A -> F)
    (p q : generic_literal_formula A),
  generic_literal_denote C atom (GLF_iff p q) =
  generic_formula_iff C
    (generic_literal_denote C atom p)
    (generic_literal_denote C atom q).
Proof. reflexivity. Qed.

(** Source [Litform.complexity]. *)
Fixpoint generic_literal_complexity {A : Type}
    (p : generic_literal_formula A) : nat :=
  match p with
  | GLF_atom _ | GLF_top | GLF_bottom => 0
  | GLF_and q r | GLF_or q r | GLF_imp q r | GLF_iff q r =>
      S (Nat.max (generic_literal_complexity q)
                 (generic_literal_complexity r))
  | GLF_neg q => S (generic_literal_complexity q)
  end.

Lemma generic_literal_complexity_child_left : forall (A : Type)
    (p q : generic_literal_formula A),
  generic_literal_complexity p <
    generic_literal_complexity (GLF_and p q) /\
  generic_literal_complexity p <
    generic_literal_complexity (GLF_or p q) /\
  generic_literal_complexity p <
    generic_literal_complexity (GLF_imp p q) /\
  generic_literal_complexity p <
    generic_literal_complexity (GLF_iff p q).
Proof.
  intros A p q. simpl. repeat split; apply Nat.lt_succ_r;
    apply Nat.le_max_l.
Qed.

Lemma generic_literal_complexity_child_right : forall (A : Type)
    (p q : generic_literal_formula A),
  generic_literal_complexity q <
    generic_literal_complexity (GLF_and p q) /\
  generic_literal_complexity q <
    generic_literal_complexity (GLF_or p q) /\
  generic_literal_complexity q <
    generic_literal_complexity (GLF_imp p q) /\
  generic_literal_complexity q <
    generic_literal_complexity (GLF_iff p q).
Proof.
  intros A p q. simpl. repeat split; apply Nat.lt_succ_r;
    apply Nat.le_max_r.
Qed.

Lemma generic_literal_complexity_neg_child : forall (A : Type)
    (p : generic_literal_formula A),
  generic_literal_complexity p <
    generic_literal_complexity (GLF_neg p).
Proof. intros A p. simpl. apply Nat.lt_succ_diag_r. Qed.

(** Atom maps act structurally on literal trees. *)
Fixpoint generic_literal_map {A B : Type} (f : A -> B)
    (p : generic_literal_formula A) : generic_literal_formula B :=
  match p with
  | GLF_atom a => GLF_atom (f a)
  | GLF_top => GLF_top
  | GLF_bottom => GLF_bottom
  | GLF_and q r => GLF_and (generic_literal_map f q)
      (generic_literal_map f r)
  | GLF_or q r => GLF_or (generic_literal_map f q)
      (generic_literal_map f r)
  | GLF_neg q => GLF_neg (generic_literal_map f q)
  | GLF_imp q r => GLF_imp (generic_literal_map f q)
      (generic_literal_map f r)
  | GLF_iff q r => GLF_iff (generic_literal_map f q)
      (generic_literal_map f r)
  end.

Lemma generic_literal_denote_map : forall (A B F : Type)
    (C : generic_connectives F) (atom : B -> F) (f : A -> B)
    (p : generic_literal_formula A),
  generic_literal_denote C atom (generic_literal_map f p) =
  generic_literal_denote C (fun a => atom (f a)) p.
Proof.
  intros A B F C atom f p. induction p; simpl; congruence.
Qed.

Lemma generic_literal_complexity_map : forall (A B : Type)
    (f : A -> B) (p : generic_literal_formula A),
  generic_literal_complexity (generic_literal_map f p) =
  generic_literal_complexity p.
Proof.
  intros A B f p. induction p; simpl; now rewrite ?IHp, ?IHp1, ?IHp2.
Qed.
