(** Thin natural-code adapter for the shared truth-free implication proof.
    The DomImp record and rho8_all statement preserve the production API.
    dtruth remains available to clients but is not used in this derivation. *)
From Stdlib Require Import Arith.
From K230L Require Import Codes230.
From K215F Require Import DominatedImplication58.
Module DI := DominatedImplication58.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Lemma pair_below_imp x y : P x y <= wim x y.
Proof. exact (Nat.le_add_r _ _). Qed.
Lemma le_l {u x} y : u <= x -> u <= wim x y.
Proof. intro H. exact (Nat.le_trans _ _ _ H
  (Nat.le_trans _ _ _ (P_ge_l x y) (pair_below_imp x y))). Qed.
Lemma le_r {u y} x : u <= y -> u <= wim x y.
Proof. intro H. exact (Nat.le_trans _ _ _ H
  (Nat.le_trans _ _ _ (P_ge_r x y) (pair_below_imp x y))). Qed.

Definition restricted T (h : DomImp T) : DI.Restricted wim le T :=
  {| DI.dmp := dmp h; DI.drho8 := drho8 h |}.

Theorem rho8_all T (h : DomImp T) a b c u : T (rho8 a b c u).
Proof.
  exact (DI.rho8_all wim le Nat.le_refl
    (fun u x y => @le_l u x y) (fun u y x => @le_r u y x)
    T (restricted T h) a b c u).
Qed.

Print Assumptions rho8_all.
