(** Atom-polymorphic proof theory for syntactic complements.

    The final section of Foundation/Modal/Formula/Complement.lean assumes an
    abstract classical entailment.  A fixed entailment theory is exactly a
    predicate on formulas closed under classical tautologies and modus ponens,
    so [classical_logic] is the minimal local interface.  No modal rule,
    substitution closure, atom equality decision, or formula equality decision
    is needed. *)

From FoundationModal Require Import Syntax Complement LogicInfrastructure.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** The two double-negation directions are factored because complement
    elimination and downstream finite-context arguments use them separately. *)
Lemma classical_logic_double_neg_elim :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L (Imp (Neg (Neg p)) p).
Proof.
  intros AtomType L Hclass p.
  apply (logic_classical_tautology Hclass).
  intro rho. unfold Neg. simpl. tauto.
Qed.

Lemma classical_logic_double_neg_intro :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p, L (Imp p (Neg (Neg p))).
Proof.
  intros AtomType L Hclass p.
  apply (logic_classical_tautology Hclass).
  intro rho. unfold Neg. simpl. tauto.
Qed.

(** A formula and its one-layer syntactic complement derive falsity.  This is
    Foundation's [complement_derive_bot], generalized by dropping
    [DecidableEq AtomType]. *)
Theorem logic_complement_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    L p -> L (complement p) -> L Bottom.
Proof.
  intros AtomType L Hclass p Hp Hcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - rewrite Hneg in Hcomp.
    exact (logic_modus_ponens Hclass Hcomp Hp).
  - rewrite <- Hq in *. rewrite complement_neg in Hcomp.
    exact (logic_modus_ponens Hclass Hp Hcomp).
Qed.

(** Negating both a formula and its syntactic complement also derives
    falsity.  This is Foundation's [neg_complement_derive_bot]. *)
Theorem logic_neg_complement_bottom :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    L (Neg p) -> L (Neg (complement p)) -> L Bottom.
Proof.
  intros AtomType L Hclass p Hneg Hnegcomp.
  destruct (complement_cases p) as [Hcomp | [q Hq]].
  - rewrite Hcomp in Hnegcomp.
    exact (logic_modus_ponens Hclass Hnegcomp Hneg).
  - rewrite <- Hq in *. rewrite complement_neg in Hnegcomp.
    exact (logic_modus_ponens Hclass Hneg Hnegcomp).
Qed.

(** Refuting the syntactic complement proves the original formula.  This is
    Foundation's [of_imply_complement_bot]. *)
Theorem logic_of_neg_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    L (Neg (complement p)) -> L p.
Proof.
  intros AtomType L Hclass p Hnegcomp.
  destruct (complement_cases p) as [Hcomp | [q Hq]].
  - rewrite Hcomp in Hnegcomp.
    exact (logic_modus_ponens Hclass
      (classical_logic_double_neg_elim Hclass p) Hnegcomp).
  - rewrite <- Hq in *. now rewrite complement_neg in Hnegcomp.
Qed.

(** The converse direction is useful when complement-closed theories are
    manipulated extensionally. *)
Theorem logic_neg_of_complement :
  forall (AtomType : Type) (L : modal_logic_set AtomType),
    classical_logic L -> forall p,
    L (complement p) -> L (Neg p).
Proof.
  intros AtomType L Hclass p Hcomp.
  destruct (complement_cases p) as [Hneg | [q Hq]].
  - now rewrite Hneg in Hcomp.
  - rewrite <- Hq in *. rewrite complement_neg in Hcomp.
    exact (logic_modus_ponens Hclass
      (classical_logic_double_neg_intro Hclass q) Hcomp).
Qed.
