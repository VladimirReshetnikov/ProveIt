(** Optional cross-candidate comparison; not in the 215 contract import closure. *)
From K230 Require Import RM.
From KLocal Require Import Macro215Binding Macro217Binding.
From K215F Require Import DagPerm.
From K217F Require Import DagDom.
Theorem macro_215_217_iff n : macro_ok n = true -> forall R x R',
  run DagPerm.dagPerm (ENode n) R x R' <-> run DagDom.dagDom (ENode n) R x R'.
Proof.
  intros Hn R x R'. split; intro H.
  - apply (node_transfer _ _ _ canonical_to_217 _ Hn).
    apply (node_transfer _ _ _ macros_215_to_canonical _ Hn), H.
  - apply (node_transfer _ _ _ canonical_to_215 _ Hn).
    apply (node_transfer _ _ _ macros_217_to_canonical _ Hn), H.
Qed.
Print Assumptions macro_215_217_iff.
