(*
  The minimal order of a perfect squared square.

  Coq port of the Lean module SquaredSquare.MinimalOrder.  perfectOrder n
  says that some perfect squared square has exactly n pieces.  It is proved
  that 21 is achieved (Duijvestijn), that every achievable order is at
  least 7, and that the full minimality statement — 21 is achieved and is a
  lower bound for every achievable order — is equivalent to the single
  proposition DuijvestijnSearchClaim: every perfect squared square has at
  least 21 pieces.  That claim is the result of A. J. W. Duijvestijn's 1978
  exhaustive computer search; it is stated and reduced to here but not
  proved, and no axiom is introduced for it.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From SquaredSquare Require Import Defs Duijvestijn Intervals Minimality.
Import ListNotations.
Import Defs.LeanProofs.SquaredSquare.
Import Duijvestijn.LeanProofs.SquaredSquare.
Import Minimality.LeanProofs.SquaredSquare.

Open Scope R_scope.

Module LeanProofs.
Module SquaredSquare.

(* The piece counts realized by perfect squared squares. *)
Definition perfectOrder (n : nat) : Prop :=
  exists (L : R) (l : list Sq),
    IsPerfectSquaredSquare L l /\ length l = n.

(* The result of Duijvestijn's exhaustive search, as a proposition. *)
Definition DuijvestijnSearchClaim : Prop :=
  forall (L : R) (l : list Sq),
    IsPerfectSquaredSquare L l -> (21 <= length l)%nat.

(* Order 21 is achieved. *)
Theorem perfectOrder_21 : perfectOrder 21.
Proof.
  exists 112, duijvestijnTiles.
  split; [exact duijvestijn_perfect | exact duijvestijnTiles_length].
Qed.

(* Every achievable order is at least 7. *)
Theorem seven_le_of_perfectOrder :
  forall n, perfectOrder n -> (7 <= n)%nat.
Proof.
  intros n [L [l [Hp Hn]]].
  subst n.
  exact (seven_le_length L l Hp).
Qed.

(* The minimality statement, reduced: "the minimal number of pieces of a
   perfect squared square is 21" holds iff Duijvestijn's search claim
   does. *)
Theorem minimal_order_21_iff :
  (perfectOrder 21 /\ forall n, perfectOrder n -> (21 <= n)%nat)
  <-> DuijvestijnSearchClaim.
Proof.
  split.
  - intros [_ Hlb] L l Hp.
    apply (Hlb (length l)).
    exists L, l; auto.
  - intros Hclaim.
    split; [exact perfectOrder_21 |].
    intros n [L [l [Hp Hn]]].
    subst n.
    exact (Hclaim L l Hp).
Qed.

End SquaredSquare.
End LeanProofs.
