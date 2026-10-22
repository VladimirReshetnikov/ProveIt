(** Compatibility adapter for the shared, truth-free implication derivation.
    The public DomImp record and rho8_all signature are unchanged. *)
From Stdlib Require Import Arith Lia.
From K230L Require Import Codes230.
From K215F Require Import DominatedImplication.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

Lemma le_l {u x} y : u <= x -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_l x y). lia. Qed.
Lemma le_r {u y} x : u <= y -> u <= wim x y.
Proof. intro H. unfold wim. pose proof (P_ge_r x y). lia. Qed.

(** All codes are admitted; neither a formula decoder nor truth is needed. *)
Theorem rho8_all_of_restricted (T : nat -> Prop)
  (mp : forall a b, T (wim a b) -> T a -> T b)
  (row : forall a b c u, u <= a -> T (rho8 a b c u)) a b c u :
  T (rho8 a b c u).
Proof.
  exact (@DominatedImplication.rho8_all nat wim le le_n
    (fun u x y H => @le_l u x y H)
    (fun u x y H => @le_r u y x H) T mp row a b c u).
Qed.

Theorem rho8_all (T : nat -> Prop) (h : DomImp T) a b c u :
  T (rho8 a b c u).
Proof. exact (rho8_all_of_restricted T (dmp h) (drho8 h) a b c u). Qed.

Theorem composition (T : nat -> Prop) (h : DomImp T) a b c :
  T (wim (wim a b) (wim (wim b c) (wim a c))).
Proof.
  exact (@DominatedImplication.composition nat wim le le_n
    (fun u x y H => @le_l u x y H)
    (fun u x y H => @le_r u y x H) T (dmp h) (drho8 h) a b c).
Qed.

Theorem lift_right (T : nat -> Prop) (h : DomImp T) a b
  (hab : T (wim a b)) x : T (wim (wim x a) (wim x b)).
Proof.
  exact (@DominatedImplication.lift_right nat wim le le_n
    (fun u x y H => @le_l u x y H)
    (fun u x y H => @le_r u y x H) T (dmp h) (drho8 h) a b hab x).
Qed.

Print Assumptions rho8_all_of_restricted.
Print Assumptions rho8_all.
Print Assumptions composition.
Print Assumptions lift_right.
