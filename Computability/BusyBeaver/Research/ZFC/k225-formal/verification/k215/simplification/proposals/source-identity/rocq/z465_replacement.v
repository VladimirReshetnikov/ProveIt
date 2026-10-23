(** Proposed local proof reuse for K215. NOT COMPILED in this review.
    Pin: cbf94cb552a3b49509e0eee80e7455d4eb5974c6.
    This is a standalone comparison client, not a production replacement.
    In the production producer, replace z465's body with the proof below,
    retaining its existing name and statement. *)
From Coq Require Import Lia.
From K230 Require Import RM.
From K215F Require Import DagPerm ProgLibPerm.

Lemma z465_reuse a : forall m, get m 5 = a ->
  sem (ENode 465) m XNormal (set m 5 0).
Proof.
  intros m _. revert m.
  while_tac (fun m : St => m) (fun m : St => set m 5 0).
Qed.

Definition z465_original_type :
  forall a m, get m 5 = a -> sem (ENode 465) m XNormal (set m 5 0) := z465.
Definition z465_proposed_type :
  forall a m, get m 5 = a -> sem (ENode 465) m XNormal (set m 5 0) := z465_reuse.

Print Assumptions z465_reuse.
