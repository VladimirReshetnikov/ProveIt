(**
  Translations between primitive propositional formulas and their
  negation-normal-form syntax.

  This module ports [Propositional/Translation.lean].  The forward map uses
  NNF's derived implication, while the reverse map reads a negative atom as
  an ordinary negated atom and NNF truth as the derived ordinary truth.
*)

From FoundationModal Require Import
  GenericSemantics GenericLogicSymbol
  PropositionalFormula PropositionalNNFormula.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Fixpoint pformula_to_pnn {Atom : Type}
    (p : pformula Atom) : pnnformula Atom :=
  match p with
  | PAtom a => PNNAtom a
  | PFalsum => PNNBottom
  | PAnd q r => PNNAnd (pformula_to_pnn q) (pformula_to_pnn r)
  | POr q r => PNNOr (pformula_to_pnn q) (pformula_to_pnn r)
  | PImp q r =>
      generic_imp (pnnformula_connectives Atom)
        (pformula_to_pnn q) (pformula_to_pnn r)
  end.

Lemma pformula_to_pnn_atom :
  forall (Atom : Type) (a : Atom),
    pformula_to_pnn (PAtom a) = PNNAtom a.
Proof. reflexivity. Qed.

Lemma pformula_to_pnn_bottom :
  forall Atom : Type,
    pformula_to_pnn (@PFalsum Atom) = PNNBottom.
Proof. reflexivity. Qed.

Lemma pformula_to_pnn_and :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_to_pnn (PAnd p q) =
    PNNAnd (pformula_to_pnn p) (pformula_to_pnn q).
Proof. reflexivity. Qed.

Lemma pformula_to_pnn_or :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_to_pnn (POr p q) =
    PNNOr (pformula_to_pnn p) (pformula_to_pnn q).
Proof. reflexivity. Qed.

Lemma pformula_to_pnn_imp :
  forall (Atom : Type) (p q : pformula Atom),
    pformula_to_pnn (PImp p q) =
    generic_imp (pnnformula_connectives Atom)
      (pformula_to_pnn p) (pformula_to_pnn q).
Proof. reflexivity. Qed.

Fixpoint pnn_to_pformula {Atom : Type}
    (p : pnnformula Atom) : pformula Atom :=
  match p with
  | PNNTop => ptop
  | PNNBottom => PFalsum
  | PNNAtom a => PAtom a
  | PNNNegAtom a => pneg (PAtom a)
  | PNNAnd q r => PAnd (pnn_to_pformula q) (pnn_to_pformula r)
  | PNNOr q r => POr (pnn_to_pformula q) (pnn_to_pformula r)
  end.

Lemma pnn_to_pformula_top :
  forall Atom : Type,
    pnn_to_pformula (@PNNTop Atom) = ptop.
Proof. reflexivity. Qed.

Lemma pnn_to_pformula_bottom :
  forall Atom : Type,
    pnn_to_pformula (@PNNBottom Atom) = PFalsum.
Proof. reflexivity. Qed.

Lemma pnn_to_pformula_atom :
  forall (Atom : Type) (a : Atom),
    pnn_to_pformula (PNNAtom a) = PAtom a.
Proof. reflexivity. Qed.

Lemma pnn_to_pformula_neg_atom :
  forall (Atom : Type) (a : Atom),
    pnn_to_pformula (PNNNegAtom a) = pneg (PAtom a).
Proof. reflexivity. Qed.

Lemma pnn_to_pformula_and :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_to_pformula (PNNAnd p q) =
    PAnd (pnn_to_pformula p) (pnn_to_pformula q).
Proof. reflexivity. Qed.

Lemma pnn_to_pformula_or :
  forall (Atom : Type) (p q : pnnformula Atom),
    pnn_to_pformula (PNNOr p q) =
    POr (pnn_to_pformula p) (pnn_to_pformula q).
Proof. reflexivity. Qed.
