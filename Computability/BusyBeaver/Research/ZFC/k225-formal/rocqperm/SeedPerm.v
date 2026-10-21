(** * SeedPerm: L1 for the 215's enumerator, and its seed.

    Between candidates, with theorems in the registers, the enumerator halts iff [thm222 1]
    (soundness: the stack invariant; completeness: [complete_from]). The 215's bootstrap starts
    candidate 4 with every other register zero, such a state. *)
From Coq Require Import Arith Lia List.
From K230L Require Import Codes230.
From NS Require Import Codes222 Thm222 ThmDom EnumPerm L1_SoundPerm L1_CompPerm.

Theorem halts_from_iff s : pl s = 0 -> Inv s -> halts_from s <-> thm222 1.
Proof.
  intros Hp Hs. split; [|exact (complete_from s Hp)].
  intros [n [s' [Hr H]]]. exact (halt_step s' (Inv_run n s s' Hs Hr) H).
Qed.

Definition seedPerm : state := mkState 0 4 0 0 0 0.

Theorem seedPerm_iff_thm : halts_from seedPerm <-> thm222 1.
Proof. apply halts_from_iff; [reflexivity | cbn; repeat split; [exact W_true | exact W_true | exact good_0]]. Qed.
