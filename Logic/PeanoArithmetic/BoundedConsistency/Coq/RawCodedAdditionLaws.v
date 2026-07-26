(**
  The two additive identities that the coded-context layer needs.

  [FiniteBetaCoding] proves commutativity and the successor law for raw
  addition but not either identity law, and the model-internal context
  relations need the *left* identity: the depth bound of an insertion at
  position zero is [0 < bound + 1], which unfolds to [0 + (bound + 1)] being
  [bound + 1].

  No definable induction is required.  The right identity is the ordinary PA
  axiom instance, and commutativity — already available — turns it into the
  left identity.
*)

From Stdlib Require Import List.
From FirstOrder Require Import Fol.
From PAHF Require Import PAHF.
From PAFiniteBasisReduction Require Import
  HierarchyReduction CanonicalSelector CanonicalSelectorPA FiniteBetaCoding.
From BoundedPAConsistency Require Import RawCodedAssignment.

Import ListNotations.

Module PABoundedRawCodedAdditionLaws.

Import PA.
Import PAHierarchyReduction.
Import PACanonicalSelector.
Import PACanonicalSelectorPA.
Import PAFiniteBetaCoding.
Import PABoundedRawCodedAssignment.

Lemma raw_add_zero_right : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  raw_add M x (raw_zero M) = x.
Proof.
  intros M hPA x.
  set (e := scons M x (fun _ : nat => raw_zero M)).
  pose proof (raw_eq_of_closed_bprov M hPA
    (PA.tAdd (PA.tVar 0) PA.tZero) (PA.tVar 0) e
    (PA.Formula.BProv_Ax_s_addZero_term [] (PA.tVar 0))) as h.
  unfold e in h. cbn [raw_term_eval scons] in h. exact h.
Qed.

Lemma raw_add_zero_left : forall (M : RawPAModel),
  RawPASatisfies M -> forall x : M,
  raw_add M (raw_zero M) x = x.
Proof.
  intros M hPA x.
  rewrite (raw_add_comm M hPA (raw_zero M) x).
  exact (raw_add_zero_right M hPA x).
Qed.

(** The depth bound consumed by insertion at position zero. *)
Corollary raw_lt_zero_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall bound : M,
  rawLt M (raw_zero M) (raw_succ M bound).
Proof.
  intros M hPA bound.
  exists bound.
  exact (raw_add_zero_left M hPA (raw_succ M bound)).
Qed.

(** ------------------------------------------------------------------
    Two order facts the coded-context descent needs.

    Both follow from [raw_lt_succ_cases] together with transitivity and
    [x < x + 1]; neither needs the additive definition of [rawLt] to be
    unfolded, and neither needs definable induction. *)

(** Successors reflect strict order. *)
Lemma raw_lt_succ_succ_inv : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y : M,
  rawLt M (raw_succ M x) (raw_succ M y) -> rawLt M x y.
Proof.
  intros M hPA x y hlt.
  destruct (raw_lt_succ_cases M hPA (raw_succ M x) y hlt) as [h | h].
  - exact (raw_assignment_lt_trans M hPA x (raw_succ M x) y
      (raw_assignment_lt_self_succ M hPA x) h).
  - rewrite <- h. exact (raw_assignment_lt_self_succ M hPA x).
Qed.

(** Strictly below something that is at most [z] is strictly below [z]. *)
Lemma raw_lt_of_lt_of_lt_succ : forall (M : RawPAModel),
  RawPASatisfies M -> forall x y z : M,
  rawLt M x y -> rawLt M y (raw_succ M z) -> rawLt M x z.
Proof.
  intros M hPA x y z hxy hyz.
  destruct (raw_lt_succ_cases M hPA y z hyz) as [h | h].
  - exact (raw_assignment_lt_trans M hPA x y z hxy h).
  - rewrite <- h. exact hxy.
Qed.

End PABoundedRawCodedAdditionLaws.
