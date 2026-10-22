(** Numerical adapter for the shared representation-independent proof.
    DomImp and rho8_all retain the maintained production interfaces.
    The inherited truth field is retained but is unnecessary for the proof. *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K215F Require DominatedImplication.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Module Adapter.
Module Core := DominatedImplication.
Definition language : Core.Language nat.
Proof.
  refine {| Core.imp := wim; Core.below := le; Core.refl := le_n |}.
  - intros u x y H. unfold wim. pose proof (P_ge_l x y). lia.
  - intros u y x H. unfold wim. pose proof (P_ge_r x y). lia.
Defined.

Definition restricted T (h : DomImp T) : Core.Restricted language T.
Proof. constructor; [exact (dmp h) | exact (drho8 h)]. Defined.
End Adapter.

Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u : T (rho8 a b c u).
Proof.
  exact (DominatedImplication.rho8_all Adapter.language T
    (Adapter.restricted T h) a b c u).
Qed.
