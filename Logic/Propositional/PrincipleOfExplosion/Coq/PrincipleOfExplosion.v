(* Principle of explosion for intuitionistic and classical natural deduction. *)

From Stdlib Require Import List.
From NaturalDeduction Require Import Calculus.
Import ListNotations.
Import NaturalDeduction.

Set Implicit Arguments.

Module Explosion.

(** Ex falso quodlibet, the primitive falsity-elimination rule. *)
Theorem derives_ex_falso : forall A (axiom : formula A -> Prop) Gamma q,
    derives axiom Gamma Falsum -> derives axiom Gamma q.
Proof.
  intros A axiom Gamma q Hfalse.
  exact (@D_falseElim A axiom Gamma q Hfalse).
Qed.

(** Derive falsity from [p] and [~p], then eliminate it. *)
Theorem derives_explosion : forall A (axiom : formula A -> Prop) Gamma p q,
    derives axiom Gamma p ->
    derives axiom Gamma (Neg p) ->
    derives axiom Gamma q.
Proof.
  intros A axiom Gamma p q Hp Hnp.
  apply D_falseElim.
  apply D_impElim with (p := p).
  - exact Hnp.
  - exact Hp.
Qed.

Theorem derives_explosion_from_conjunction :
    forall A (axiom : formula A -> Prop) Gamma p q,
    derives axiom Gamma (Conj p (Neg p)) -> derives axiom Gamma q.
Proof.
  intros A axiom Gamma p q H.
  apply derives_explosion with (p := p).
  - apply D_andElimLeft with (q := Neg p). exact H.
  - apply D_andElimRight with (p := p). exact H.
Qed.

(** The exact Wikipedia sequent [p, ~p, Gamma |- q]. *)
Theorem derives_explosion_sequent :
    forall A (axiom : formula A -> Prop) (Gamma : context A) p q,
    derives axiom (p :: Neg p :: Gamma) q.
Proof.
  intros A axiom Gamma p q.
  apply derives_explosion with (p := p).
  - apply D_assumption. left. reflexivity.
  - apply D_assumption. right. left. reflexivity.
Qed.

Theorem derives_explosion_conj_sequent :
    forall A (axiom : formula A -> Prop) (Gamma : context A) p q,
    derives axiom (Conj p (Neg p) :: Gamma) q.
Proof.
  intros A axiom Gamma p q.
  apply derives_explosion_from_conjunction with (p := p).
  apply D_assumption. left. reflexivity.
Qed.

Theorem derives_explosion_implication :
    forall A (axiom : formula A -> Prop) (Gamma : context A) p q,
    derives axiom Gamma (Impl (Conj p (Neg p)) q).
Proof.
  intros A axiom Gamma p q.
  apply D_impIntro.
  apply derives_explosion_from_conjunction with (p := p).
  apply D_assumption. left. reflexivity.
Qed.

(**
  The twelve results below are the six generic theorems above read at the two
  concrete axiom sets.  Both [intuitionistically_derives] and
  [classically_derives] are by definition [derives] at a fixed axiom
  predicate, so each specialization *is* the generic theorem: no proof step
  beyond instantiating [axiom] is needed, and every proof is the corresponding
  one-liner.
*)

(* Intuitionistic specializations: [axiom] is empty. *)

Theorem intuitionistic_ex_falso : forall A (Gamma : context A) q,
    intuitionistically_derives Gamma Falsum ->
    intuitionistically_derives Gamma q.
Proof. exact (fun A => @derives_ex_falso A (fun _ => False)). Qed.

Theorem intuitionistic_explosion : forall A (Gamma : context A) p q,
    intuitionistically_derives Gamma p ->
    intuitionistically_derives Gamma (Neg p) ->
    intuitionistically_derives Gamma q.
Proof. exact (fun A => @derives_explosion A (fun _ => False)). Qed.

Theorem intuitionistic_explosion_from_conjunction :
    forall A (Gamma : context A) p q,
    intuitionistically_derives Gamma (Conj p (Neg p)) ->
    intuitionistically_derives Gamma q.
Proof.
  exact (fun A => @derives_explosion_from_conjunction A (fun _ => False)).
Qed.

Theorem intuitionistic_explosion_sequent :
    forall A (Gamma : context A) p q,
    intuitionistically_derives (p :: Neg p :: Gamma) q.
Proof. exact (fun A => @derives_explosion_sequent A (fun _ => False)). Qed.

Theorem intuitionistic_explosion_conj_sequent :
    forall A (Gamma : context A) p q,
    intuitionistically_derives (Conj p (Neg p) :: Gamma) q.
Proof.
  exact (fun A => @derives_explosion_conj_sequent A (fun _ => False)).
Qed.

Theorem intuitionistic_explosion_implication :
    forall A (Gamma : context A) p q,
    intuitionistically_derives Gamma (Impl (Conj p (Neg p)) q).
Proof.
  exact (fun A => @derives_explosion_implication A (fun _ => False)).
Qed.

(* Classical specializations: [axiom] is excluded middle. *)

Theorem classical_ex_falso : forall A (Gamma : context A) q,
    classically_derives Gamma Falsum -> classically_derives Gamma q.
Proof. exact (fun A => @derives_ex_falso A classical_axiom). Qed.

Theorem classical_explosion : forall A (Gamma : context A) p q,
    classically_derives Gamma p ->
    classically_derives Gamma (Neg p) ->
    classically_derives Gamma q.
Proof. exact (fun A => @derives_explosion A classical_axiom). Qed.

Theorem classical_explosion_from_conjunction :
    forall A (Gamma : context A) p q,
    classically_derives Gamma (Conj p (Neg p)) ->
    classically_derives Gamma q.
Proof.
  exact (fun A => @derives_explosion_from_conjunction A classical_axiom).
Qed.

Theorem classical_explosion_sequent : forall A (Gamma : context A) p q,
    classically_derives (p :: Neg p :: Gamma) q.
Proof. exact (fun A => @derives_explosion_sequent A classical_axiom). Qed.

Theorem classical_explosion_conj_sequent :
    forall A (Gamma : context A) p q,
    classically_derives (Conj p (Neg p) :: Gamma) q.
Proof. exact (fun A => @derives_explosion_conj_sequent A classical_axiom). Qed.

Theorem classical_explosion_implication : forall A (Gamma : context A) p q,
    classically_derives Gamma (Impl (Conj p (Neg p)) q).
Proof. exact (fun A => @derives_explosion_implication A classical_axiom). Qed.

End Explosion.
