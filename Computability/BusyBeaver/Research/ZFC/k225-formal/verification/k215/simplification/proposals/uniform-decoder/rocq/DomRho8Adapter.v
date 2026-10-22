(** Proposed replacement for the production numeric DomRho8.v.
    Depends on the separately checked generic core. The full K215F production
    build and this adapter against K230L are integration obligations. *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K215F Require Import DominatedImplication.
Module DI := DominatedImplication.DominatedImplication.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (Codes230.rho8 a b c u)
}.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Local Lemma le_left u x y : u <= x -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Local Lemma le_right u y x : u <= y -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

Local Definition language : DI.Language nat :=
  {| DI.imp := wim;
     DI.below := le;
     DI.refl := le_n;
     DI.grow_left := le_left;
     DI.grow_right := le_right |}.

Local Definition restricted {T : nat -> Prop} (h : DomImp T) :
    DI.Restricted language T :=
  @DI.Build_Restricted nat language T (dmp h) (drho8 h).

Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u :
    T (Codes230.rho8 a b c u).
Proof. exact (DI.rho8_all (restricted h) a b c u). Qed.

Print Assumptions rho8_all.
