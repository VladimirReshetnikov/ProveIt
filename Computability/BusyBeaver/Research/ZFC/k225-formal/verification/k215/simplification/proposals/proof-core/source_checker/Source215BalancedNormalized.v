(** Exact K215 source theorem, simultaneously quotienting zero padding and
    using balanced lookup. No bounded-execution hypothesis is used. *)
From Coq Require Import List NArith.
From K230 Require Import RM.
From K230P Require Import Bisim230.
From K215F Require Import Prog215 DagPerm.
Require Import NormalizedCert215 BalancedBisim BalancedNormalized.
Import ListNotations.

Definition NormalizedTree215 : CTree := Eval vm_compute in buildTree 11 Normalized215.

Lemma normalized_tree_exact : flatten NormalizedTree215 = Normalized215.
Proof. vm_compute. reflexivity. Qed.
Lemma normalized_tree_valid : validb NormalizedTree215 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma normalized_tree_size : csize NormalizedTree215 = 1426%N.
Proof. vm_compute. reflexivity. Qed.
Lemma normalized_tree_height : height NormalizedTree215 = 12.
Proof. vm_compute. reflexivity. Qed.

Lemma balanced_normalized_forward :
  ncheckTree (ptree p215) (ptree dagPerm) NormalizedTree215 = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem p215_dagPerm_balanced_normalized R :
  rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
Proof. exact (ncheckTree_halts_iff p215 dagPerm NormalizedTree215
  normalized_tree_valid balanced_normalized_forward R). Qed.

Print Assumptions normalized_tree_exact.
Print Assumptions balanced_normalized_forward.
Print Assumptions p215_dagPerm_balanced_normalized.
