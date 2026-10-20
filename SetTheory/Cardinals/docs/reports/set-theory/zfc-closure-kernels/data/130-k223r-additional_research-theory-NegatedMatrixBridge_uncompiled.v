(** Minimal proposed port for the new negated-input matrix family.
    This file has NOT been compiled in this environment.  Its imports and
    invoked theorems are from K230 commit
    3142e4dd980f0be12f4abb636c4ae2528afc17eb.
    It records only two local corollaries, not a new machine theorem. *)
From ZF Require Import Logic.
From K230S Require Import KCode230 KDecoder230 KDecodeBundle KDecodeFresh.

Lemma negated_input_core_decodes a b c :
  c <> b ->
  D (kcore a b c (wn c)) = KCore a b c (Wn (D c)).
Proof.
  intros Hcb. rewrite D_kcore by exact Hcb.
  now rewrite D_wn.
Qed.

Lemma negated_input_private_fresh c :
  fr c (Wn (D c)) = false.
Proof.
  change (fr c (D c) = false).
  apply D_private_fresh.
Qed.
