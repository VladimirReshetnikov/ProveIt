(** * SeedPerm: the unchanged seed endpoint from arbitrary-state completeness.
    The three old public endpoint statements are preserved exactly. *)
From Coq Require Import Arith Lia List.
From K230L Require Import Codes230.
From K215F Require Import Codes222 Thm222 ThmDom EnumPerm L1_SoundPerm L1_CompPerm.

Definition seedPerm : state := mkState 0 4 0 0 0 0.

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
