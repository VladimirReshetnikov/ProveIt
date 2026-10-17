(** * Box: the four register-file excursions of zfc_254, for arbitrary register files.

    The register file is [sepsR vs] (each block [0 1^(v+1)]), to the right of the header,
    with blank beyond.  [sepsM r vs] has the first 1 of block [r] erased (the mark).
    - [box_mark]: a skip state entering the file marks its target block and leaves the file
      to the left in the dispatcher (state 2 for block 0, state 6 otherwise);
    - [box_inc]:  seek.inc (73) finds the mark, restores it, increments the block (shifting the
      later blocks right) and returns (state 48);
    - [box_dec0]: seek.dec (43) on a zero block restores the mark and returns (state 3);
    - [box_decp]: seek.dec on a positive block shifts the later blocks left, which shortens the
      target by one and appends a new zero block, and returns (63 for block 0, else 48). *)

From Coq Require Import Lists.Streams Lists.List Bool.Bool Arith.Arith Lia.
From BusyCoq Require Import TM.
From M254 Require Import Table254 TM254 Zip SymExec.
Import ListNotations.

(** ** List facts *)
Definition sepsL (vs : list nat) : list bool := flat_map (fun v => ones (S v) ++ [false]) vs.

Lemma rev_ones n : rev (ones n) = ones n.
Proof. induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. symmetry. apply (rep_snoc true n). Qed.

Lemma sepsR_app A B : sepsR (A ++ B) = sepsR A ++ sepsR B.
Proof. unfold sepsR. apply flat_map_app. Qed.

Lemma sepsR_cons v vs : sepsR (v :: vs) = false :: true :: ones v ++ sepsR vs.
Proof. reflexivity. Qed.

Lemma sepsL_cons v vs : sepsL (v :: vs) = true :: ones v ++ false :: sepsL vs.
Proof. unfold sepsL. simpl. rewrite <- app_assoc. reflexivity. Qed.

Lemma sepsL_app A B : sepsL (A ++ B) = sepsL A ++ sepsL B.
Proof. unfold sepsL. apply flat_map_app. Qed.

Lemma rev_sepsR vs : rev (sepsR vs) = sepsL (rev vs).
Proof.
  induction vs as [|v vs IH]; [reflexivity|].
  change (sepsR (v :: vs)) with ((false :: ones (S v)) ++ sepsR vs).
  rewrite rev_app_distr, IH.
  change (rev (false :: ones (S v))) with (rev (ones (S v)) ++ [false]).
  rewrite rev_ones. change (rev (v :: vs)) with (rev vs ++ [v]).
  rewrite sepsL_app. f_equal. unfold sepsL. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma split_at (vs : list nat) r : r < length vs ->
  exists pre v rest, vs = pre ++ v :: rest /\ length pre = r.
Proof.
  revert r. induction vs as [|x vs IH]; intros r H; [simpl in H; lia|].
  destruct r as [|r].
  - exists (@nil nat), x, vs. split; reflexivity.
  - destruct (IH r) as (pre & v & rest & E & L); [simpl in H; lia|].
    exists (x :: pre), v, rest. subst. split; reflexivity.
Qed.

Lemma nth_split (pre rest : list nat) (v d : nat) : nth (length pre) (pre ++ v :: rest) d = v.
Proof. induction pre; simpl; auto. Qed.

Lemma incr_split pre v rest : incr (length pre) (pre ++ v :: rest) = pre ++ S v :: rest.
Proof. induction pre; simpl; f_equal; auto. Qed.

Lemma decr_split pre v rest : decr (length pre) (pre ++ v :: rest) = pre ++ pred v :: rest.
Proof. induction pre; simpl; f_equal; auto. Qed.

Lemma sepsM_split pre v rest :
  sepsM (length pre) (pre ++ v :: rest) = sepsR pre ++ false :: false :: ones v ++ sepsR rest.
Proof.
  induction pre as [|p pre IH]; [reflexivity|].
  cbn [length app sepsM]. rewrite IH, sepsR_cons. cbn [app]. rewrite <- app_assoc. reflexivity.
Qed.

(* the left context after crossing [pre] rightwards *)
Lemma rev_sepsR_snoc pre w : rev (sepsR (pre ++ [w])) = ones w ++ true :: false :: sepsL (rev pre).
Proof.
  rewrite rev_sepsR, rev_app_distr. cbn [rev app]. rewrite sepsL_cons, rep_comm. reflexivity.
Qed.

Lemma rev_sepsR_cons p pre l : rev (sepsR (p :: pre)) ++ l = rev (sepsR pre) ++ ones p ++ true :: false :: l.
Proof.
  rewrite sepsR_cons. change (false :: true :: ones p ++ sepsR pre) with ([false; true] ++ ones p ++ sepsR pre).
  rewrite !rev_app_distr, rev_ones. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma sepsR_one w Y : sepsR [w] ++ Y = false :: true :: ones w ++ Y.
Proof. unfold sepsR. simpl. rewrite app_nil_r. reflexivity. Qed.

(** ** Single steps *)
Lemma stR q b w q' l r X : tmn q b = Some (w, R, q') ->
  zc (st q') (w :: l) r -->* X -> zc (st q) l (b :: r) -->* X.
Proof. intros T H. eapply evstep_step; [apply zR, tm_st, T | exact H]. Qed.

Lemma stL q b w q' l r X : tmn q b = Some (w, L, q') ->
  zl (st q') l (w :: r) -->* X -> zc (st q) l (b :: r) -->* X.
Proof. intros T H. eapply evstep_step; [apply zL, tm_st, T | exact H]. Qed.

Ltac go := first [ eapply stR; [reflexivity|] | eapply stL; [reflexivity|] ].

Lemma zl_c q x l r : zl q (x :: l) r = zc q l (x :: r).
Proof. reflexivity. Qed.

Lemma zc_blank q l : zc q l [] = zc q l [false].
Proof. reflexivity. Qed.

Lemma zl_blank q l : zl q l [] = zl q l [false].
Proof. unfold zl. symmetry. apply (zc_padr _ _ [hd false l] 1). Qed.

(** ** Generic scans across register blocks *)
Section Scans.
Variables qa qb : nat.

(* rightwards: [qa] crosses ones, a 0 sends it to [qb], which returns to [qa] on a 1 *)
Hypothesis F1 : tmn qa true = Some (true, R, qa).
Hypothesis F2 : tmn qa false = Some (false, R, qb).
Hypothesis F3 : tmn qb true = Some (true, R, qa).

Lemma fwd pre l X : zc (st qa) l (sepsR pre ++ X) -->* zc (st qa) (rev (sepsR pre) ++ l) X.
Proof.
  revert l. induction pre as [|p pre IH]; intros l; [apply evstep_refl|].
  rewrite sepsR_cons. cbn [app]. rewrite <- app_assoc.
  eapply stR; [exact F2|]. eapply stR; [exact F3|].
  eapply evstep_trans; [apply scanR, tm_st, F1|].
  eapply evstep_trans; [apply IH|].
  rewrite <- sepsR_cons, rev_sepsR_cons. apply evstep_refl.
Qed.
End Scans.

Section Ret.
Variables qa qb : nat.

(* leftwards: the same pattern, ending one cell left of the file in state [qb] *)
Hypothesis R1 : tmn qa true = Some (true, L, qa).
Hypothesis R2 : tmn qa false = Some (false, L, qb).
Hypothesis R3 : tmn qb true = Some (true, L, qa).

Lemma ret rp w l Y q : tmn q true = Some (true, L, qa) ->
  zc (st q) (ones w ++ false :: sepsL rp ++ l) (true :: Y) -->* zl (st qb) l (sepsR (rev rp ++ [w]) ++ Y).
Proof.
  revert w Y q. induction rp as [|w' rp IH]; intros w Y q T.
  - eapply stL; [exact T|]. eapply evstep_trans; [apply scanL, tm_st, R1|].
    rewrite zl_c. eapply stL; [exact R2|]. apply eq_ev.
    change (rev [] ++ [w]) with [w]. rewrite sepsR_one, rep_comm. reflexivity.
  - eapply stL; [exact T|]. eapply evstep_trans; [apply scanL, tm_st, R1|].
    rewrite zl_c. eapply stL; [exact R2|].
    rewrite sepsL_cons. cbn [app]. rewrite <- app_assoc. cbn [app]. rewrite zl_c.
    eapply evstep_trans; [apply IH, R3|].
    apply eq_ev. f_equal. change (rev (w' :: rp)) with (rev rp ++ [w']).
    rewrite (sepsR_app (rev rp ++ [w']) [w]), <- app_assoc, sepsR_one, rep_comm. reflexivity.
Qed.

(* the same from a zl configuration on the last 1 of a nonempty file *)
Lemma ret_file vs l Y q : vs <> [] -> tmn q true = Some (true, L, qa) ->
  zl (st q) (rev (sepsR vs) ++ l) Y -->* zl (st qb) l (sepsR vs ++ Y).
Proof.
  intros Hne T. destruct (exists_last Hne) as (pre & w & ->).
  rewrite rev_sepsR_snoc, <- app_assoc. cbn [app]. rewrite rep_comm, zl_c.
  eapply evstep_trans; [apply (ret (rev pre) w l Y q T)|].
  rewrite rev_involutive. apply evstep_refl.
Qed.
End Ret.

(** ** The skip chain *)
Definition sk (j : nat) : nat := nth j [60; 44; 31; 56; 38; 40; 28; 64; 69] 0.

Lemma sk_self j : j < 9 -> tmn (sk j) true = Some (true, R, sk j).
Proof. intros H. do 9 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma sk_next j : j < 8 -> tmn (sk (S j)) false = Some (false, R, sk j).
Proof. intros H. do 8 (destruct j as [|j]; [reflexivity|]). lia. Qed.

Lemma skip_target_sk q r : skip_target q = Some r -> q = sk r /\ r < 9.
Proof.
  intros H. unfold skip_target in H.
  do 70 (destruct q as [|q]; [simpl in H; first [discriminate | injection H as <-; split; [reflexivity | lia]]|]).
  simpl in H. discriminate.
Qed.

Lemma skip pre m l X : length pre + m < 9 ->
  zc (st (sk (length pre + m))) l (sepsR pre ++ X) -->* zc (st (sk m)) (rev (sepsR pre) ++ l) X.
Proof.
  revert l. induction pre as [|p pre IH]; intros l H; [apply evstep_refl|].
  simpl length in *. rewrite Nat.add_succ_l in *. rewrite sepsR_cons. cbn [app]. rewrite <- app_assoc.
  eapply stR; [apply (sk_next (length pre + m)); lia|].
  eapply evstep_trans; [apply (scanR _ true true (S p)), tm_st, (sk_self (length pre + m)); lia|].
  eapply evstep_trans; [apply IH; lia|].
  rewrite <- sepsR_cons, rev_sepsR_cons. apply eq_ev. f_equal. f_equal. simpl. rewrite rep_comm. reflexivity.
Qed.

(** ** Increment: shifting the later blocks right *)
Lemma shift_inc rest a K :
  zc (st 95) K (ones a ++ sepsR rest) -->* zl (st 63) (rev (ones (S a) ++ sepsR rest) ++ K) [].
Proof.
  revert a K. induction rest as [|m rest IH]; intros a K.
  - change (sepsR []) with (@nil bool).
    eapply evstep_trans; [apply (scanR _ true true a), tm_st; reflexivity|].
    rewrite zc_blank. go. rewrite zc_blank. go.
    apply eq_ev. rewrite zl_blank. rewrite app_nil_r, rev_ones. reflexivity.
  - rewrite sepsR_cons.
    eapply evstep_trans; [apply (scanR _ true true a), tm_st; reflexivity|].
    go. go. eapply evstep_trans; [apply IH|].
    apply eq_ev. f_equal.
    change (ones (S a) ++ false :: true :: ones m ++ sepsR rest) with (ones (S a) ++ [false] ++ (ones (S m) ++ sepsR rest)).
    rewrite !rev_app_distr, !rev_ones. rewrite <- !app_assoc. reflexivity.
Qed.

(** ** Positive decrement: shifting the later blocks left *)
Definition Wf (rr : list nat) (Y : list bool) : list bool :=
  fold_left (fun acc m => ones m ++ false :: true :: acc) rr Y.

Lemma shift_dec_block m X Y :
  zc (st 112) (ones (S m) ++ false :: X) (false :: Y) -->* zc (st 112) X (false :: ones m ++ false :: true :: Y).
Proof.
  go. simpl app. rewrite zl_c. go.
  eapply evstep_trans; [apply (scanL _ true true m), tm_st; reflexivity|].
  rewrite zl_c. apply evstep_refl.
Qed.

Lemma shift_dec rr Z Y :
  zc (st 112) (sepsL rr ++ Z) (false :: Y) -->* zc (st 112) Z (false :: Wf rr Y).
Proof.
  revert Y. induction rr as [|m rr IH]; intros Y; [apply evstep_refl|].
  rewrite sepsL_cons. cbn [app]. rewrite <- app_assoc. cbn [app].
  eapply evstep_trans; [apply (shift_dec_block m (sepsL rr ++ Z) Y)|]. apply IH.
Qed.

Lemma Wf_rev rest Y : false :: true :: Wf (rev rest) Y = sepsR rest ++ false :: true :: Y.
Proof.
  revert Y. induction rest as [|m rest IH]; intros Y; [reflexivity|].
  simpl rev. unfold Wf. rewrite fold_left_app. simpl fold_left at 1. fold (Wf (rev rest) Y).
  rewrite sepsR_cons. cbn [app]. rewrite <- app_assoc. rewrite <- IH. reflexivity.
Qed.

(** ** The four excursions *)
Lemma box_mark q r l vs : skip_target q = Some r -> 9 <= length vs ->
  zc (st q) l (sepsR vs) -->* zl (st (mark_exit r)) l (sepsM r vs).
Proof.
  intros Hq Hl. apply skip_target_sk in Hq as [-> Hr].
  destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite sepsR_app, sepsM_split.
  replace (sk (length pre)) with (sk (length pre + 0)) by (rewrite Nat.add_0_r; reflexivity).
  eapply evstep_trans; [apply skip; lia|]. rewrite sepsR_cons.
  go. go. rewrite zl_c. go.
  destruct pre as [|p pre'].
  - apply evstep_refl.
  - change (mark_exit (length (p :: pre'))) with 6.
    eapply evstep_trans; [apply (ret_file 4 6); try reflexivity; discriminate|]. apply evstep_refl.
Qed.

Lemma box_inc r l vs : r < 9 -> 9 <= length vs ->
  zc (st 73) l (sepsM r vs) -->* zl (st 48) l (sepsR (incr r vs)).
Proof.
  intros Hr Hl. destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite sepsM_split, incr_split.
  eapply evstep_trans; [apply (fwd 73 83); reflexivity|].
  go. go. eapply evstep_trans; [apply shift_inc|].
  assert (E : rev (ones (S v) ++ sepsR rest) ++ true :: false :: rev (sepsR pre) ++ l =
              rev (sepsR (pre ++ S v :: rest)) ++ l).
  { rewrite sepsR_app, sepsR_cons.
    change (false :: true :: ones (S v) ++ sepsR rest) with ([false; true] ++ (ones (S v) ++ sepsR rest)).
    rewrite !rev_app_distr. rewrite <- !app_assoc. reflexivity. }
  rewrite E. eapply evstep_trans; [apply (ret_file 63 48); try reflexivity; destruct pre; discriminate|].
  rewrite app_nil_r. apply evstep_refl.
Qed.

Lemma zl_padr q l r n : zl q l (r ++ zeros n) = zl q l r.
Proof. unfold zl. rewrite app_comm_cons. apply zc_padr. Qed.

Lemma sepsR_pad rest : exists W, sepsR rest ++ [false] = false :: W.
Proof. destruct rest; eexists; reflexivity. Qed.

Lemma box_dec0 r l vs : r < 9 -> 9 <= length vs -> nth r vs 0 = 0 ->
  zc (st 43) l (sepsM r vs) -->* zl (st 3) l (sepsR vs).
Proof.
  intros Hr Hl Hz. destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite nth_split in Hz. subst v. rewrite sepsM_split.
  eapply evstep_trans; [apply (fwd 43 59); reflexivity|].
  destruct (sepsR_pad rest) as [W EW].
  rewrite <- (zc_padr _ _ _ 1). change (zeros 1) with [false]. cbn [repeat app]. rewrite EW.
  go. go. go. rewrite zl_c. go. rewrite zl_c. go.
  rewrite <- (zl_padr (st 3) l (sepsR (pre ++ 0 :: rest)) 1). change (zeros 1) with [false].
  rewrite sepsR_app, sepsR_cons. cbn [repeat app]. rewrite <- app_assoc. cbn [app]. rewrite EW.
  destruct pre as [|p pre'].
  - apply evstep_refl.
  - apply (ret_file 1 3); try reflexivity; discriminate.
Qed.

Lemma box_decp r l vs : r < 9 -> 9 <= length vs -> nth r vs 0 <> 0 ->
  zc (st 43) l (sepsM r vs) -->* zl (st (decp_exit r)) l (sepsR (decr r vs ++ [0])).
Proof.
  intros Hr Hl Hz. destruct (split_at vs r) as (pre & v & rest & -> & <-); [lia|].
  rewrite nth_split in Hz. destruct v as [|v']; [congruence|]. clear Hz.
  rewrite sepsM_split, decr_split. simpl pred.
  eapply evstep_trans; [apply (fwd 43 59); reflexivity|].
  go. go. go.
  eapply evstep_trans; [apply (scanR _ true true v'), tm_st; reflexivity|].
  rewrite <- (zc_padr _ _ (sepsR rest) 2). change (zeros 2) with [false; false].
  eapply evstep_trans; [apply (fwd 85 97); reflexivity|].
  go. go. rewrite zl_c. rewrite rev_sepsR.
  eapply evstep_trans; [apply shift_dec|].
  rewrite rep_comm.
  eapply evstep_trans; [apply (shift_dec_block v' (false :: rev (sepsR pre) ++ l))|].
  go. rewrite zl_c. go.
  rewrite Wf_rev.
  rewrite <- (zl_padr _ l _ 1). change (zeros 1) with [false].
  assert (E : sepsR ((pre ++ v' :: rest) ++ [0]) ++ [false] =
              sepsR pre ++ false :: true :: ones v' ++ sepsR rest ++ [false; true; false]).
  { rewrite !sepsR_app, sepsR_cons. rewrite <- !app_assoc. cbn [app]. rewrite <- !app_assoc. reflexivity. }
  rewrite E. clear E.
  destruct pre as [|p pre'].
  - apply evstep_refl.
  - change (decp_exit (length (p :: pre'))) with 48.
    apply (ret_file 63 48); try reflexivity; discriminate.
Qed.

(** No axioms: *)
Print Assumptions box_decp.
