(**
  Standard-model forms of Foundation's arithmetic induction principles.

  The Lean source works inside nonstandard models and expends substantial
  machinery showing that bounded families of induction hypotheses can be
  coded by HFS sequences.  Over Coq's standard naturals, well-foundedness is
  already available.  The same conclusions therefore hold for completely
  arbitrary predicates and bounding functions: no hierarchy classification,
  formula definability, replacement, or sequence coding is needed.

  The measured theorem is further generalized to an arbitrary carrier with
  a natural-valued rank.  Source-shaped bounded and multi-parameter results
  are then small corollaries of one well-founded argument.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Lia.

Set Implicit Arguments.
Unset Strict Implicit.

(** * Positive successor induction *)

Theorem nat_positive_successor_induction : forall (P : nat -> Prop),
  P 0 ->
  P 1 ->
  (forall x, P (S x) -> P (S (S x))) ->
  forall x, P x.
Proof.
  intros P Hzero Hone Hsucc [|x]; [exact Hzero|].
  induction x as [|x IH]; [exact Hone|now apply Hsucc].
Qed.

(** * Bounded families below the induction variable *)

Theorem nat_bounded_order_induction : forall
    (bound : nat -> nat -> nat) (P : nat -> nat -> Prop),
  (forall x y,
    (forall x', x' < x ->
      forall y', y' <= bound x y -> P x' y') ->
    P x y) ->
  forall x y, P x y.
Proof.
  intros bound P Hstep x.
  induction x using lt_wf_ind. intro y. apply Hstep.
  intros x' Hx' y' Hy'. now apply H.
Qed.

Corollary nat_bounded_order_induction_unary : forall
    (bound : nat -> nat) (P : nat -> nat -> Prop),
  (forall x y,
    (forall x', x' < x ->
      forall y', y' <= bound y -> P x' y') ->
    P x y) ->
  forall x y, P x y.
Proof.
  intros bound P Hstep.
  apply (@nat_bounded_order_induction (fun _ y => bound y) P).
  exact Hstep.
Qed.

Theorem nat_bounded_order_induction_two_parameters : forall
    (bound_y bound_z : nat -> nat -> nat -> nat)
    (P : nat -> nat -> nat -> Prop),
  (forall x y z,
    (forall x', x' < x ->
      forall y', y' <= bound_y x y z ->
      forall z', z' <= bound_z x y z -> P x' y' z') ->
    P x y z) ->
  forall x y z, P x y z.
Proof.
  intros bound_y bound_z P Hstep x.
  induction x using lt_wf_ind. intros y z. apply Hstep.
  intros x' Hx' y' Hy' z' Hz'. now apply H.
Qed.

Theorem nat_bounded_order_induction_three_parameters : forall
    (bound_y bound_z bound_w : nat -> nat -> nat -> nat -> nat)
    (P : nat -> nat -> nat -> nat -> Prop),
  (forall x y z w,
    (forall x', x' < x ->
      forall y', y' <= bound_y x y z w ->
      forall z', z' <= bound_z x y z w ->
      forall w', w' <= bound_w x y z w -> P x' y' z' w') ->
    P x y z w) ->
  forall x y z w, P x y z w.
Proof.
  intros bound_y bound_z bound_w P Hstep x.
  induction x using lt_wf_ind. intros y z w. apply Hstep.
  intros x' Hx' y' Hy' z' Hz' w' Hw'. now apply H.
Qed.

(** The arity is immaterial.  This indexed-family form subsumes every fixed
    number of bounded auxiliary parameters, including the source arities two
    and three above. *)
Theorem nat_bounded_order_induction_family : forall I
    (bound : nat -> (I -> nat) -> I -> nat)
    (P : nat -> (I -> nat) -> Prop),
  (forall x parameters,
    (forall x', x' < x ->
      forall parameters',
        (forall i, parameters' i <= bound x parameters i) ->
        P x' parameters') ->
    P x parameters) ->
  forall x parameters, P x parameters.
Proof.
  intros I bound P Hstep x.
  induction x using lt_wf_ind. intro parameters. apply Hstep.
  intros x' Hx' parameters' Hbounded. now apply H.
Qed.

(** * Measured well-founded induction *)

Theorem nat_measure_induction : forall A
    (measure : A -> nat) (P : A -> Prop),
  (forall a, (forall b, measure b < measure a -> P b) -> P a) ->
  forall a, P a.
Proof.
  intros A measure P Hstep a.
  remember (measure a) as rank eqn:Hrank.
  revert a Hrank.
  induction rank using lt_wf_ind. intros a Hrank.
  apply Hstep. intros b Hb.
  apply (H (measure b)); [lia|reflexivity].
Qed.

Corollary nat_measured_bounded_order_induction : forall A
    (measure : A -> nat) (allowed : A -> A -> Prop) (P : A -> Prop),
  (forall a,
    (forall b, allowed a b -> measure b < measure a -> P b) -> P a) ->
  forall a, P a.
Proof.
  intros A measure allowed P Hstep.
  apply (@nat_measure_induction A measure P). intros a IH.
  apply Hstep. intros b Hallowed Hmeasure. now apply IH.
Qed.

Corollary nat_measured_numeric_bounded_order_induction : forall
    (measure bound : nat -> nat) (P : nat -> Prop),
  (forall a,
    (forall b, b <= bound a -> measure b < measure a -> P b) -> P a) ->
  forall a, P a.
Proof.
  intros measure bound P Hstep.
  apply (@nat_measured_bounded_order_induction nat measure
    (fun a b => b <= bound a) P). exact Hstep.
Qed.

(** * Disjunctive induction *)

Theorem nat_disjunctive_successor_induction : forall
    (P Q : nat -> Prop),
  P 0 \/ Q 0 ->
  (forall x, P x \/ Q x -> P (S x) \/ Q (S x)) ->
  forall x, P x \/ Q x.
Proof.
  intros P Q Hzero Hsucc x. induction x as [|x IH].
  - exact Hzero.
  - now apply Hsucc.
Qed.

Theorem nat_disjunctive_order_induction : forall
    (P Q : nat -> Prop),
  (forall x, (forall y, y < x -> P y \/ Q y) -> P x \/ Q x) ->
  forall x, P x \/ Q x.
Proof.
  intros P Q Hstep x. induction x using lt_wf_ind.
  apply Hstep. exact H.
Qed.

(** A finite disjunction need not be binary. *)
Theorem nat_indexed_disjunctive_order_induction : forall I
    (R : I -> nat -> Prop),
  (forall x,
    (forall y, y < x -> exists i, R i y) ->
    exists i, R i x) ->
  forall x, exists i, R i x.
Proof.
  intros I R Hstep x. induction x using lt_wf_ind.
  apply Hstep. exact H.
Qed.
