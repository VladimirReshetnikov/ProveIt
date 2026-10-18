(** * L1_s2: the TM's boot reaches main with nextproof = 2 (all other registers 0).
    That state is exactly two enumerator steps after s0: candidate 0 = MP 0 (wim 0 0 = 0 = cache,
    success, pushes 0 onto the zero stream), candidate 1 = unP 1 = (1, 0): DROP of zeros. *)
From Coq Require Import Arith Lia.
From M254L Require Import Codes254 Enum254 Thm254 L1_254.

Definition s2 : state := mkState 0 2 0 0 0 0.

Lemma run2_s0 : run 2 s0 = Some s2.
Proof. reflexivity. Qed.

Lemma run_add n m s :
  run (n + m) s = match run n s with Some s' => run m s' | None => None end.
Proof.
  revert s; induction n as [|n IH]; intro s; [reflexivity|].
  cbn. destruct (enum_step s); [apply IH | reflexivity].
Qed.

Definition enum254_halts_from (s : state) : Prop := exists n s', run n s = Some s' /\ enum_step s' = None.

Lemma enum254_halts_s2 : enum254_halts <-> enum254_halts_from s2.
Proof.
  split.
  - intros [n [s [H1 H2]]].
    destruct n as [|[|n]].
    + injection H1 as <-. discriminate.
    + cbn in H1. injection H1 as <-. discriminate.
    + exists n, s. split; [|exact H2].
      replace (S (S n)) with (2 + n) in H1 by lia. rewrite run_add, run2_s0 in H1. exact H1.
  - intros [n [s [H1 H2]]]. exists (2 + n), s. split; [|exact H2].
    rewrite run_add, run2_s0. exact H1.
Qed.

Theorem L1_254_s2 : enum254_halts_from s2 <-> thm254 1.
Proof. rewrite <- enum254_halts_s2. exact L1_254. Qed.

Print Assumptions L1_254_s2.
