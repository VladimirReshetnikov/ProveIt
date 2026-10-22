(** k225-formal/rocqperm/DomRho8.v (SHA256 fbdccff873239208b247facea55b5f63defbafb5031937a90a0c3f3aad09f350) under namespace K215F. *)
(** Nat-code compatibility adapter for the shared abstract implication core.
    The production DomImp and rho8_all interfaces are retained exactly.
    The truth field remains for compatibility, but the new theorem does not use it. *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K215F Require Import DominatedImplication.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (Codes230.rho8 a b c u)
}.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Lemma le_l {u x} y : u <= x -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {u y} x : u <= y -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

Definition language : DominatedImplication.Language nat := {|
  DominatedImplication.imp := wim;
  DominatedImplication.below := le;
  DominatedImplication.refl := le_n;
  DominatedImplication.grow_left := fun u x y H => @le_l u x y H;
  DominatedImplication.grow_right := fun u y x H => @le_r u y x H
|}.

Definition restricted (T : nat -> Prop)
    (mp : forall a b, T (wim a b) -> T a -> T b)
    (row : forall a b c u, u <= a -> T (Codes230.rho8 a b c u)) :
    DominatedImplication.Restricted language T.
Proof. constructor; [exact mp | exact row]. Defined.

Theorem rho8_all_of_restricted (T : nat -> Prop)
    (mp : forall a b, T (wim a b) -> T a -> T b)
    (row : forall a b c u, u <= a -> T (Codes230.rho8 a b c u)) a b c u :
    T (Codes230.rho8 a b c u).
Proof. exact (DominatedImplication.rho8_all language T (restricted T mp row) a b c u). Qed.

Theorem rho8_all T (h : DomImp T) a b c u : T (Codes230.rho8 a b c u).
Proof. exact (rho8_all_of_restricted T (dmp h) (drho8 h) a b c u). Qed.

Theorem composition T (h : DomImp T) a b c :
    T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof. exact (DominatedImplication.composition language T (restricted T (dmp h) (drho8 h)) a b c). Qed.

Theorem lift_right T (h : DomImp T) a b :
    T (wim a b) -> forall x, T (wim (wim x a) (wim x b)).
Proof. exact (DominatedImplication.lift_right language T (restricted T (dmp h) (drho8 h)) a b). Qed.

Print Assumptions rho8_all.
Print Assumptions rho8_all_of_restricted.
