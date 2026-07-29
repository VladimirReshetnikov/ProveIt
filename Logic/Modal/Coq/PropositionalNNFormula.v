(**
  Primitive propositional formulas in negation normal form.

  This module ports the mathematical surface of the pinned Foundation module
  [Propositional/Formula/NNFormula.lean].  Negation is structural: it swaps
  truth constants and atom polarities and exchanges conjunction with
  disjunction.  Implication is consequently derived as [~p \/ q].

  The generic connective records expose the resulting involution and De
  Morgan laws to the rest of the port without coupling this syntax to a
  particular proof system or semantics.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import GenericSemantics GenericLogicSymbol.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive pnnformula (Atom : Type) : Type :=
| PNNTop : pnnformula Atom
| PNNBottom : pnnformula Atom
| PNNAtom : Atom -> pnnformula Atom
| PNNNegAtom : Atom -> pnnformula Atom
| PNNAnd : pnnformula Atom -> pnnformula Atom -> pnnformula Atom
| PNNOr : pnnformula Atom -> pnnformula Atom -> pnnformula Atom.

Arguments PNNTop {Atom}.
Arguments PNNBottom {Atom}.
Arguments PNNAtom {Atom} _.
Arguments PNNNegAtom {Atom} _.
Arguments PNNAnd {Atom} _ _.
Arguments PNNOr {Atom} _ _.

Fixpoint pnn_neg {Atom : Type} (p : pnnformula Atom) : pnnformula Atom :=
  match p with
  | PNNTop => PNNBottom
  | PNNBottom => PNNTop
  | PNNAtom a => PNNNegAtom a
  | PNNNegAtom a => PNNAtom a
  | PNNAnd q r => PNNOr (pnn_neg q) (pnn_neg r)
  | PNNOr q r => PNNAnd (pnn_neg q) (pnn_neg r)
  end.

Lemma pnn_neg_involutive :
  forall (Atom : Type) (p : pnnformula Atom),
    pnn_neg (pnn_neg p) = p.
Proof.
  intros Atom p; induction p; simpl; now rewrite ?IHp1, ?IHp2.
Qed.

Definition pnnformula_connectives (Atom : Type) :
    generic_connectives (pnnformula Atom) :=
  {| generic_top := PNNTop;
     generic_bottom := PNNBottom;
     generic_and := PNNAnd;
     generic_or := PNNOr;
     generic_imp := fun p q => PNNOr (pnn_neg p) q;
     generic_neg := pnn_neg |}.

(** Definitional equations for the structural operations. *)
Lemma pnn_neg_top :
  forall Atom : Type, @pnn_neg Atom PNNTop = PNNBottom.
Proof. reflexivity. Qed.

Lemma pnn_neg_bottom :
  forall Atom : Type, @pnn_neg Atom PNNBottom = PNNTop.
Proof. reflexivity. Qed.

Lemma pnn_neg_atom :
  forall (Atom : Type) (a : Atom), pnn_neg (PNNAtom a) = PNNNegAtom a.
Proof. reflexivity. Qed.

Lemma pnn_neg_neg_atom :
  forall (Atom : Type) (a : Atom), pnn_neg (PNNNegAtom a) = PNNAtom a.
Proof. reflexivity. Qed.

Lemma pnn_neg_and :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_neg (PNNAnd p q) = PNNOr (pnn_neg p) (pnn_neg q).
Proof. reflexivity. Qed.

Lemma pnn_neg_or :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_neg (PNNOr p q) = PNNAnd (pnn_neg p) (pnn_neg q).
Proof. reflexivity. Qed.

Lemma pnn_neg_inj :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_neg p = pnn_neg q <-> p = q.
Proof.
  intros Atom p q; split.
  - intro H. pose proof (f_equal (@pnn_neg Atom) H) as Hneg.
    now rewrite !pnn_neg_involutive in Hneg.
  - now intros ->.
Qed.

Lemma pnn_imp_def :
  forall (Atom : Type) (p q : pnnformula Atom),
    generic_imp (pnnformula_connectives Atom) p q =
    PNNOr (pnn_neg p) q.
Proof. reflexivity. Qed.

Lemma pnn_iff_def :
  forall (Atom : Type) (p q : pnnformula Atom),
    generic_formula_iff (pnnformula_connectives Atom) p q =
    PNNAnd (PNNOr (pnn_neg p) q) (PNNOr (pnn_neg q) p).
Proof. reflexivity. Qed.

Lemma pnn_neg_imp :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_neg (generic_imp (pnnformula_connectives Atom) p q) =
    PNNAnd p (pnn_neg q).
Proof.
  intros Atom p q. simpl. now rewrite pnn_neg_involutive.
Qed.

Lemma pnn_and_inj :
  forall (Atom : Type) (p1 p2 q1 q2 : pnnformula Atom),
    PNNAnd p1 p2 = PNNAnd q1 q2 <-> p1 = q1 /\ p2 = q2.
Proof.
  intros Atom p1 p2 q1 q2; split.
  - intro H. inversion H. now split.
  - intros [-> ->]. reflexivity.
Qed.

Lemma pnn_or_inj :
  forall (Atom : Type) (p1 p2 q1 q2 : pnnformula Atom),
    PNNOr p1 p2 = PNNOr q1 q2 <-> p1 = q1 /\ p2 = q2.
Proof.
  intros Atom p1 p2 q1 q2; split.
  - intro H. inversion H. now split.
  - intros [-> ->]. reflexivity.
Qed.

Lemma pnn_de_morgan_laws :
  forall Atom : Type,
    generic_de_morgan_laws (pnnformula_connectives Atom).
Proof.
  intro Atom. constructor.
  - reflexivity.
  - reflexivity.
  - intros p q. reflexivity.
  - intros p q. reflexivity.
  - intros p q. reflexivity.
Qed.

Lemma pnn_neg_involutive_law :
  forall Atom : Type,
    generic_neg_involutive_law (pnnformula_connectives Atom).
Proof. intros Atom p. apply pnn_neg_involutive. Qed.

(** * Complexity and decidable equality *)

Fixpoint pnn_complexity {Atom : Type} (p : pnnformula Atom) : nat :=
  match p with
  | PNNTop | PNNBottom | PNNAtom _ | PNNNegAtom _ => 0
  | PNNAnd q r | PNNOr q r =>
      S (Nat.max (pnn_complexity q) (pnn_complexity r))
  end.

Lemma pnn_complexity_top :
  forall Atom : Type, pnn_complexity (@PNNTop Atom) = 0.
Proof. reflexivity. Qed.

Lemma pnn_complexity_bottom :
  forall Atom : Type, pnn_complexity (@PNNBottom Atom) = 0.
Proof. reflexivity. Qed.

Lemma pnn_complexity_atom :
  forall (Atom : Type) (a : Atom), pnn_complexity (PNNAtom a) = 0.
Proof. reflexivity. Qed.

Lemma pnn_complexity_neg_atom :
  forall (Atom : Type) (a : Atom), pnn_complexity (PNNNegAtom a) = 0.
Proof. reflexivity. Qed.

Lemma pnn_complexity_and :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_complexity (PNNAnd p q) =
    S (Nat.max (pnn_complexity p) (pnn_complexity q)).
Proof. reflexivity. Qed.

Lemma pnn_complexity_or :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_complexity (PNNOr p q) =
    S (Nat.max (pnn_complexity p) (pnn_complexity q)).
Proof. reflexivity. Qed.

Lemma pnn_complexity_neg :
  forall (Atom : Type) (p : pnnformula Atom),
    pnn_complexity (pnn_neg p) = pnn_complexity p.
Proof.
  intros Atom p; induction p; simpl; now rewrite ?IHp1, ?IHp2.
Qed.

Fixpoint pnnformula_eq_dec {Atom : Type}
    (atom_eq_dec : forall a b : Atom, {a = b} + {a <> b})
    (p q : pnnformula Atom) : {p = q} + {p <> q}.
Proof. decide equality. Defined.

Lemma pnn_ne_of_ne_complexity :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_complexity p <> pnn_complexity q -> p <> q.
Proof. intros Atom p q Hneq ->. exact (Hneq eq_refl). Qed.

(** Foundation's [Theory] is a predicate set. *)
Definition pnn_theory (Atom : Type) : Type := pnnformula Atom -> Prop.
