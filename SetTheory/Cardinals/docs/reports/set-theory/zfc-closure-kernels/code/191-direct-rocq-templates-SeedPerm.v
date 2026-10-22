(** * SeedPerm: the 215's bootstrap starts candidate 4 with every other register zero.
    The proof search is complete from that state (Source 159's cofinal argument): the program
    START 4 ++ Build_F ++ SUFFIX has candidate number P 3 (P 4 (P 1 r)) >= 4. *)
From Coq Require Import Arith Lia List.
From K230L Require Import Codes230.
From NS Require Import Codes222 Thm222 ThmDom EnumPerm L1_SoundPerm L1_CompPerm.
Import ListNotations.

Definition seedPerm : state := mkState 0 4 0 0 0 0.

Lemma reach_from seed k : pl seed = 0 ->
  halts_from seed \/ exists n s, run n seed = Some s /\ pl s = 0 /\ np s = np seed + k.
Proof. exact (reach_from_boundary seed k). Qed.

Lemma halts_from_reached seed n s : run n seed = Some s ->
  halts_from s -> halts_from seed.
Proof. exact (halts_from_run seed n s). Qed.

Theorem seedPerm_complete : thm222 1 -> halts_from seedPerm.
Proof. exact (enum_complete_from_boundary seedPerm eq_refl). Qed.

Theorem seedPerm_sound : halts_from seedPerm -> thm222 1.
Proof.
  intros [n [s [Hr Hs]]]. apply (halt_step s); [|exact Hs].
  apply (Inv_run n seedPerm s); [|exact Hr].
  repeat split; [exact W_true|exact W_true|exact good_0].
Qed.

Theorem seedPerm_iff_thm : halts_from seedPerm <-> thm222 1.
Proof. split; [apply seedPerm_sound|apply seedPerm_complete]. Qed.
