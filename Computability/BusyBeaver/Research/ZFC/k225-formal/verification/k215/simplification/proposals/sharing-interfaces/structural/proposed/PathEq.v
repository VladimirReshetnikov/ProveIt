(** PROPOSED source-only extraction; not compiled in this environment. *)
From Coq Require Import List Bool Arith Lia NArith.
From K230 Require Import RM RMEquiv.
Import ListNotations.

Fixpoint zeros (P : list bool) : bool :=
  match P with [] => true | b :: P => negb b && zeros P end.

Lemma zeros_ok P : zeros P = true -> ipeq P [].
Proof.
  induction P as [|b P IH].
  - intros _ i. reflexivity.
  - destruct b; cbn [zeros]; [discriminate|].
    intros H [|i]; [reflexivity|].
    change (bit P i = false). rewrite <- (bit_nil i). apply (IH H i).
Qed.

Fixpoint ibeq (P Q : list bool) : bool :=
  match P, Q with
  | [], Q => zeros Q
  | P, [] => zeros P
  | b :: P, c :: Q => Bool.eqb b c && ibeq P Q
  end.

Lemma ibeq_ok P Q : ibeq P Q = true -> ipeq P Q.
Proof.
  revert Q. induction P as [|b P IH]; intros [|c Q] H.
  - apply ipeq_refl.
  - apply ipeq_sym, zeros_ok, H.
  - apply zeros_ok, H.
  - cbn [ibeq] in H. apply andb_prop in H as [Hbc HPQ].
    apply Bool.eqb_prop in Hbc. subst c.
    intros [|i]; [reflexivity|]. apply (IH _ HPQ i).
Qed.

Lemma ibeq_sym P Q : ibeq P Q = ibeq Q P.
Proof.
  revert Q. induction P as [|b P IH]; intros [|c Q]; try reflexivity.
  cbn [ibeq]. rewrite IH. destruct b,c; reflexivity.
Qed.

Lemma halts_ipeq p P Q R : ipeq P Q -> rm_halts p (P,R) -> rm_halts p (Q,R).
Proof.
  intros H [N HN]. exists N. exact (hn_ipeq p N P Q R H HN).
Qed.

