(** * Main254: the program layer of zfc_254.

    [prog254 : rm_halts p254 ([], R0) <-> enum254_halts]

    p254 and R0 are the TM layer's frozen definitions (M254.Prog254, zf/m254/tm/coq): the decoder
    tree the Turing machine runs, in the path semantics of M254.RM, started at the IP [] with
    R0 = nextproof 2, all other registers 0 (where the blank-tape boot lands).  enum254_halts is the frozen abstract enumerator of
    zf/m254/logic/coq/Enum254.v started from s0 = all zeros.

    Chain: p254 ~ dag254 in the path semantics (Bisim254, checked certificate); path semantics =
    structured semantics for the well-formed dag254 (RMEquiv); one structured run of the root of
    dag254 = one enum_step (L2Root254); the boot state R0 encodes s2, which s0 reaches in two steps. *)
From Coq Require Import Lists.List Arith.Arith.
From M254 Require Import RM RMEquiv Prog254.
From M254P Require Import Bisim Dag254 Bisim254 ProgLib254 L2Root254.
From M254L Require Import Codes254 Enum254.
Import ListNotations.

Definition s2 : state := mkState 0 2 0 0 0 0.

Lemma dag254_wf : wf dag254.
Proof. apply wf_check_sound. vm_compute. reflexivity. Qed.

Lemma R0_enc : approx R0 (enc s2).
Proof. intros i. do 9 (destruct i as [|i]; [reflexivity|]). reflexivity. Qed.

Lemma halts_from_step s s' : enum_step s = Some s' -> halts_from s <-> halts_from s'.
Proof.
  intros E. split.
  - intros ([|n] & s1 & Hr & Hs).
    + injection Hr as <-. congruence.
    + cbn [run] in Hr. rewrite E in Hr. exists n, s1. auto.
  - intros (n & s1 & Hr & Hs). exists (S n), s1. cbn [run]. rewrite E. auto.
Qed.

(* s0 -> (MP with h = wim 0 0 = 0) -> mkState 0 1 0 0 0 0 -> (DROP) -> s2 *)
Lemma s0_step1 : enum_step s0 = Some (mkState 0 1 0 0 0 0).
Proof. vm_compute. reflexivity. Qed.

Lemma s0_step2 : enum_step (mkState 0 1 0 0 0 0) = Some s2.
Proof. vm_compute. reflexivity. Qed.

Lemma enum_s2 : enum254_halts <-> halts_from s2.
Proof.
  change enum254_halts with (halts_from s0).
  rewrite (halts_from_step _ _ s0_step1). apply halts_from_step, s0_step2.
Qed.

Theorem prog254 : rm_halts p254 ([], R0) <-> enum254_halts.
Proof.
  rewrite p254_dag, (rm_halts_iff_iter _ dag254_wf), (iter_halts_dag s2 R0 R0_enc).
  symmetry. exact enum_s2.
Qed.

Corollary prog254_iter : iter_halts p254 R0 <-> enum254_halts.
Proof. rewrite <- (rm_halts_iff_iter _ p254_wf). exact prog254. Qed.

Print Assumptions prog254.
Print Assumptions prog254_iter.
