(** Dominated rho8 derives every rho8 instance: [DominatedCore] at natural codes, where
    [u <= a] is the domination relation (implication codes dominate both inputs). *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K217F Require DominatedCore.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Lemma le_l u x y : u <= x -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r u y x : u <= y -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

(** Every rho8 instance follows from the dominated ones. *)
Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u : T (rho8 a b c u).
Proof. exact (DominatedCore.rho8_all nat wim le le_n le_l le_r T (dmp h) (drho8 h) a b c u). Qed.
Print Assumptions rho8_all.
