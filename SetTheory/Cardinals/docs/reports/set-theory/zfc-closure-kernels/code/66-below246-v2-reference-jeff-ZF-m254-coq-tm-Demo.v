(** * Demo.  Two instruction sites of zfc_254 proved by the certified symbolic
    executor and the register lemmas of Box.v (no axioms), and a timing
    run of the executor over all 6460 sites (8391 cases). *)

From Coq Require Import Lists.List Bool.Bool Arith.Arith PArith.
From BusyCoq Require Import TM.
From M254 Require Import TM254 Zip SymExec Site Sites254 Box.
Import ListNotations.

(* site 0: path 000, prooflist.decnz (physical register 5) -- the first instruction after boot *)
Lemma site0_check : check_site [false; false; false] (ODec 5) = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem site0 : forall n vs, 9 <= length vs ->
  (nth 5 vs 0 = 0 ->
   zc (st 96) [true] ([false; false; false] ++ zeros (n + 37) ++ true :: sepsR vs) -->+
   zc (st 96) [true] ([false; true] ++ zeros (n + 38) ++ true :: sepsR vs)) /\
  (nth 5 vs 0 <> 0 ->
   zc (st 96) [true] ([false; false; false] ++ zeros (n + 37) ++ true :: sepsR vs) -->+
   zc (st 96) [true] ([false; false; true] ++ zeros (n + 37) ++ true :: sepsR (decr 5 vs ++ [0]))).
Proof.
  intros n vs V. exact (site_dec box_mark box_inc box_dec0 box_decp _ _ site0_check n vs V).
Qed.

(* site 4: path 010110, scratch1.inc (physical register 4) *)
Lemma site4_check : check_site [false; true; false; true; true; false] (OInc 4) = true.
Proof. Time vm_compute. reflexivity. Qed.

Theorem site4 : forall n vs, 9 <= length vs ->
  zc (st 96) [true] ([false; true; false; true; true; false] ++ zeros (n + 34) ++ true :: sepsR vs) -->+
  zc (st 96) [true] ([false; true; false; true; true; true] ++ zeros (n + 34) ++ true :: sepsR (incr 4 vs)).
Proof.
  intros n vs V. exact (site_inc box_mark box_inc box_dec0 box_decp _ _ site4_check n vs V).
Qed.

(* every site: the paths of Sites254 are those of the file, the checks all pass *)
Lemma all_sites_check : forallb (fun '(p, o) => check_site (path_of p) o) sites = true.
Proof. Time vm_compute. reflexivity. Qed.

Print Assumptions site4.
Print Assumptions site0.
