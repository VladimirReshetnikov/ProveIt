(** k225-formal/rocqperm/SeedPerm.v (SHA256 a7662af746d4bd10b0ea856780d464eebcc41cbe3df3454d9a122b37842116e3) under namespace K215F. *)
(** Seed endpoint derived from the reusable scheduler and existing compiler.
    Machine, seed state, calculus and public theorem types are unchanged. *)
From Coq Require Import Arith Lia List.
From K230L Require Import Codes230.
From K215F Require Import Codes222 Thm222 ThmDom EnumPerm L1_SoundPerm L1_CompPerm CandidateScheduler.

Definition seedPerm : state := mkState 0 4 0 0 0 0.

Lemma reach_from seed k : pl seed = 0 ->
  halts_from seed \/ exists n s, run n seed = Some s /\ pl s = 0 /\ np s = np seed + k.
Proof. intros _. apply scheduler_seek. lia. Qed.

Lemma halts_from_reached seed n s : run n seed = Some s -> halts_from s -> halts_from seed.
Proof. exact (@CandidateScheduler.halts_after state enum_step n seed s). Qed.

Theorem enum_from_iff seed : Inv seed -> (halts_from seed <-> thm222 1).
Proof.
  intro HI. split; [|apply enum_complete_from].
  intros [n [s [Hr Hs]]]. exact (halt_step s (Inv_run n seed s HI Hr) Hs).
Qed.

Theorem seedPerm_complete : thm222 1 -> halts_from seedPerm.
Proof. exact (enum_complete_from seedPerm). Qed.

Theorem seedPerm_sound : halts_from seedPerm -> thm222 1.
Proof.
  apply enum_from_iff. repeat split; [exact W_true|exact W_true|exact good_0].
Qed.

Theorem seedPerm_iff_thm : halts_from seedPerm <-> thm222 1.
Proof. split; [apply seedPerm_sound|apply seedPerm_complete]. Qed.
