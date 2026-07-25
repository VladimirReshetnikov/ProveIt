(*
  Small orders are impossible: a perfect squared square has at least 7
  pieces.

  Coq port of the Lean module SquaredSquare.Minimality.  The arguments are
  the classical corner/edge ones: corner tiles exist and are unique and
  pairwise distinct (at least 4 pieces); the tiles touching a fixed edge
  partition it, so their sides sum to L; a non-corner piece touches at most
  one edge, and with at most two non-corner pieces either two adjacent edges
  are touched by corner tiles only (forcing two opposite corner tiles to
  have equal sides, contradicting pairwise non-congruence) or the two extras
  sit on opposite edges (forcing their sides to sum to 0).

  The remaining gap of the true minimality statement (no perfect squared
  square with 7..20 pieces, so that Duijvestijn's order-21 dissection is
  optimal) is Duijvestijn's exhaustive computer search and is not
  formalized; see the project README.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
From SquaredSquare Require Import Defs Intervals.
Import ListNotations.
Import Defs.LeanProofs.SquaredSquare.
Import Intervals.LeanProofs.SquaredSquare.

Open Scope R_scope.

Module LeanProofs.
Module SquaredSquare.

(* ---------------------------------------------------------------------- *)
(* Generic list helpers.                                                   *)
(* ---------------------------------------------------------------------- *)

(* ForallOrdPairs transports along permutations of symmetric relations. *)
Lemma FOP_perm {A : Type} (R : A -> A -> Prop)
  (Hsym : forall a b, R a b -> R b a) :
  forall l l', Permutation l l' ->
  ForallOrdPairs R l -> ForallOrdPairs R l'.
Proof.
  intros l l' Hp; induction Hp; intros H.
  - exact H.
  - destruct (FOP_cons_inv _ _ _ H) as [Hf Ht].
    constructor; [| apply IHHp, Ht].
    rewrite Forall_forall in Hf |- *.
    intros b Hb.
    apply Hf.
    apply Permutation_in with (l := l'); [apply Permutation_sym; exact Hp |].
    exact Hb.
  - destruct (FOP_cons_inv _ _ _ H) as [Hfy Ht].
    destruct (FOP_cons_inv _ _ _ Ht) as [Hfx Htl].
    rewrite Forall_forall in Hfy, Hfx.
    constructor.
    + rewrite Forall_forall.
      intros b Hb; destruct Hb as [<- | Hb].
      * apply Hsym, Hfy; left; reflexivity.
      * apply Hfx, Hb.
    + constructor; [| exact Htl].
      rewrite Forall_forall; intros b Hb.
      apply Hfy; right; exact Hb.
  - auto.
Qed.

(* A duplicate-free list included in l can be permuted to a prefix of l. *)
Lemma nodup_incl_perm_append {A : Type} :
  forall (l1 l2 : list A),
  NoDup l1 -> incl l1 l2 -> exists l3, Permutation l2 (l1 ++ l3).
Proof.
  induction l1 as [|a t IH]; intros l2 Hnd Hincl.
  - exists l2; apply Permutation_refl.
  - inversion Hnd as [|? ? Hnin Hnd']; subst.
    assert (Ha : In a l2) by (apply Hincl; left; reflexivity).
    destruct (in_split a l2 Ha) as [u [v Huv]]; subst l2.
    assert (Hincl' : incl t (u ++ v)).
    { intros x Hx.
      assert (Hx2 : In x (u ++ a :: v)) by (apply Hincl; right; exact Hx).
      apply in_app_or in Hx2; apply in_or_app.
      destruct Hx2 as [Hx2 | [Hx2 | Hx2]]; auto.
      subst x; contradiction. }
    destruct (IH (u ++ v) Hnd' Hincl') as [l3 Hl3].
    exists l3.
    eapply Permutation_trans.
    + apply Permutation_sym, Permutation_middle.
    + simpl; apply perm_skip, Hl3.
Qed.

Lemma list_nonempty {A : Type} (l : list A) : l <> [] -> exists x, In x l.
Proof.
  destruct l as [|x t]; [congruence |].
  intros _; exists x; left; reflexivity.
Qed.

Lemma list_two_split {A : Type} (l : list A) :
  (2 <= length l)%nat -> exists x y t, l = x :: y :: t.
Proof.
  destruct l as [|x [|y t]]; simpl; intros H; try lia.
  exists x, y, t; reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Geometry of a dissection.                                               *)
(* ---------------------------------------------------------------------- *)

Section Dissection.

Variable L : R.
Variable l : list Sq.
Hypothesis hd : IsDissection L l.

Let hpos : forall q, In q l -> 0 < qs q :=
  diss_pos L l hd.
Let hdisj : ForallOrdPairs DisjointOpen l :=
  diss_disj L l hd.
Let hcov : forall u v, InBig L u v <-> exists q, In q l /\ InClosed q u v :=
  diss_cover L l hd.

Lemma tile_bounds : forall q, In q l ->
  (0 <= qx q /\ qx q + qs q <= L) /\ (0 <= qy q /\ qy q + qs q <= L).
Proof.
  intros q Hq.
  pose proof (hpos q Hq) as Hs.
  assert (H1 : InBig L (qx q) (qy q)).
  { apply hcov; exists q; split; [exact Hq |].
    unfold InClosed; lra. }
  assert (H2 : InBig L (qx q + qs q) (qy q + qs q)).
  { apply hcov; exists q; split; [exact Hq |].
    unfold InClosed; lra. }
  unfold InBig in H1, H2; lra.
Qed.

Lemma side_pos_of_dissection : l <> [] -> 0 < L.
Proof.
  intros Hne.
  destruct (list_nonempty l Hne) as [q Hq].
  pose proof (tile_bounds q Hq) as Hb.
  pose proof (hpos q Hq).
  lra.
Qed.

(* Two distinct members have disjoint open interiors. *)
Lemma disjoint_of_in_ne : forall p q, In p l -> In q l -> p <> q ->
  DisjointOpen p q.
Proof.
  intros p q Hp Hq Hne.
  destruct (ForallOrdPairs_In hdisj p q Hp Hq)
    as [He | [H | H]].
  - congruence.
  - exact H.
  - intros u v H1 H2; exact (H u v H2 H1).
Qed.

Lemma center_in_open : forall q, 0 < qs q ->
  InOpen q (qx q + qs q / 2) (qy q + qs q / 2).
Proof.
  intros q Hs; unfold InOpen; lra.
Qed.

(* Overlapping open ranges in both coordinates give a common open point. *)
Lemma exists_open_inter : forall p q,
  0 < qs p -> 0 < qs q ->
  qx q < qx p + qs p -> qx p < qx q + qs q ->
  qy q < qy p + qs p -> qy p < qy q + qs q ->
  exists u v, InOpen p u v /\ InOpen q u v.
Proof.
  intros p q Hp Hq Hx1 Hx2 Hy1 Hy2.
  pose proof (Rmax_l (qx p) (qx q)).
  pose proof (Rmax_r (qx p) (qx q)).
  pose proof (Rmin_l (qx p + qs p) (qx q + qs q)).
  pose proof (Rmin_r (qx p + qs p) (qx q + qs q)).
  pose proof (Rmax_l (qy p) (qy q)).
  pose proof (Rmax_r (qy p) (qy q)).
  pose proof (Rmin_l (qy p + qs p) (qy q + qs q)).
  pose proof (Rmin_r (qy p + qs p) (qy q + qs q)).
  assert (Hxm : Rmax (qx p) (qx q) < Rmin (qx p + qs p) (qx q + qs q)).
  { apply Rmax_lub_lt; apply Rmin_glb_lt; lra. }
  assert (Hym : Rmax (qy p) (qy q) < Rmin (qy p + qs p) (qy q + qs q)).
  { apply Rmax_lub_lt; apply Rmin_glb_lt; lra. }
  exists ((Rmax (qx p) (qx q) + Rmin (qx p + qs p) (qx q + qs q)) / 2).
  exists ((Rmax (qy p) (qy q) + Rmin (qy p + qs p) (qy q + qs q)) / 2).
  unfold InOpen; lra.
Qed.

(* No piece of a dissection with at least two pieces has full side. *)
Lemma side_lt_of_two_le : (2 <= length l)%nat ->
  forall q, In q l -> qs q < L.
Proof.
  intros H2 q Hq.
  pose proof (tile_bounds q Hq) as Hb.
  pose proof (hpos q Hq) as Hs.
  destruct (Rle_lt_or_eq_dec (qs q) L) as [Hlt | Heq]; [lra | exact Hlt |].
  exfalso.
  assert (Hx0 : qx q = 0) by lra.
  assert (Hy0 : qy q = 0) by lra.
  (* the interior of any piece is inside the interior of q *)
  assert (Hsub : forall r, In r l -> forall u v,
      InOpen r u v -> InOpen q u v).
  { intros r Hr u v Hins.
    pose proof (tile_bounds r Hr) as Hbr.
    unfold InOpen in *.
    rewrite Hx0, Hy0, Heq.
    lra. }
  destruct (list_two_split l H2) as [x [y [t Hl]]].
  pose proof hdisj as Hd.
  rewrite Hl in Hd.
  destruct (FOP_cons_inv _ _ _ Hd) as [Hxf Ht].
  rewrite Forall_forall in Hxf.
  assert (Hxl : In x l) by (rewrite Hl; left; reflexivity).
  assert (Hyl : In y l) by (rewrite Hl; right; left; reflexivity).
  pose proof Hq as Hq2.
  rewrite Hl in Hq2.
  destruct Hq2 as [Hqx | Hq'].
  - (* q is the head; the second piece's interior meets q's interior *)
    pose proof (center_in_open y (hpos y Hyl)) as Hc.
    apply (Hxf y (in_eq _ _) (qx y + qs y / 2) (qy y + qs y / 2)).
    + subst x.
      apply (Hsub y Hyl (qx y + qs y / 2) (qy y + qs y / 2) Hc).
    + exact Hc.
  - (* q is later; the head's interior meets q's interior *)
    pose proof (center_in_open x (hpos x Hxl)) as Hc.
    apply (Hxf q Hq' (qx x + qs x / 2) (qy x + qs x / 2)).
    + exact Hc.
    + apply (Hsub x Hxl (qx x + qs x / 2) (qy x + qs x / 2) Hc).
Qed.

(* ------------------------------------------------------------------ *)
(* Corner tiles.                                                       *)
(* ------------------------------------------------------------------ *)

Lemma exists_corner_bl : 0 < L ->
  exists q, In q l /\ qx q = 0 /\ qy q = 0.
Proof.
  intros HL.
  assert (Hc : InBig L 0 0) by (unfold InBig; lra).
  apply hcov in Hc.
  destruct Hc as [q [Hq Hqc]].
  pose proof (tile_bounds q Hq) as Hb.
  unfold InClosed in Hqc.
  exists q; split; [exact Hq | lra].
Qed.

Lemma exists_corner_br : 0 < L ->
  exists q, In q l /\ qx q + qs q = L /\ qy q = 0.
Proof.
  intros HL.
  assert (Hc : InBig L L 0) by (unfold InBig; lra).
  apply hcov in Hc.
  destruct Hc as [q [Hq Hqc]].
  pose proof (tile_bounds q Hq) as Hb.
  unfold InClosed in Hqc.
  exists q; split; [exact Hq | lra].
Qed.

Lemma exists_corner_tl : 0 < L ->
  exists q, In q l /\ qx q = 0 /\ qy q + qs q = L.
Proof.
  intros HL.
  assert (Hc : InBig L 0 L) by (unfold InBig; lra).
  apply hcov in Hc.
  destruct Hc as [q [Hq Hqc]].
  pose proof (tile_bounds q Hq) as Hb.
  unfold InClosed in Hqc.
  exists q; split; [exact Hq | lra].
Qed.

Lemma exists_corner_tr : 0 < L ->
  exists q, In q l /\ qx q + qs q = L /\ qy q + qs q = L.
Proof.
  intros HL.
  assert (Hc : InBig L L L) by (unfold InBig; lra).
  apply hcov in Hc.
  destruct Hc as [q [Hq Hqc]].
  pose proof (tile_bounds q Hq) as Hb.
  unfold InClosed in Hqc.
  exists q; split; [exact Hq | lra].
Qed.

(* Two pieces whose open ranges overlap in both coordinates coincide. *)
Lemma eq_of_overlap : forall p q, In p l -> In q l ->
  qx q < qx p + qs p -> qx p < qx q + qs q ->
  qy q < qy p + qs p -> qy p < qy q + qs q -> p = q.
Proof.
  intros p q Hp Hq Hx1 Hx2 Hy1 Hy2.
  destruct (ForallOrdPairs_In hdisj p q Hp Hq)
    as [He | [H | H]]; [exact He | exfalso | exfalso].
  - destruct (exists_open_inter p q (hpos p Hp) (hpos q Hq)
      Hx1 Hx2 Hy1 Hy2) as [u [v [H1 H2]]].
    exact (H u v H1 H2).
  - destruct (exists_open_inter p q (hpos p Hp) (hpos q Hq)
      Hx1 Hx2 Hy1 Hy2) as [u [v [H1 H2]]].
    exact (H u v H2 H1).
Qed.

Lemma corner_bl_unique : forall p q, In p l -> In q l ->
  qx p = 0 -> qy p = 0 -> qx q = 0 -> qy q = 0 -> p = q.
Proof.
  intros p q Hp Hq Hpx Hpy Hqx Hqy.
  pose proof (hpos p Hp); pose proof (hpos q Hq).
  apply eq_of_overlap; auto; lra.
Qed.

Lemma corner_br_unique : forall p q, In p l -> In q l ->
  qx p + qs p = L -> qy p = 0 -> qx q + qs q = L -> qy q = 0 -> p = q.
Proof.
  intros p q Hp Hq Hpx Hpy Hqx Hqy.
  pose proof (hpos p Hp); pose proof (hpos q Hq).
  apply eq_of_overlap; auto; lra.
Qed.

Lemma corner_tl_unique : forall p q, In p l -> In q l ->
  qx p = 0 -> qy p + qs p = L -> qx q = 0 -> qy q + qs q = L -> p = q.
Proof.
  intros p q Hp Hq Hpx Hpy Hqx Hqy.
  pose proof (hpos p Hp); pose proof (hpos q Hq).
  apply eq_of_overlap; auto; lra.
Qed.

Lemma corner_tr_unique : forall p q, In p l -> In q l ->
  qx p + qs p = L -> qy p + qs p = L ->
  qx q + qs q = L -> qy q + qs q = L -> p = q.
Proof.
  intros p q Hp Hq Hpx Hpy Hqx Hqy.
  pose proof (hpos p Hp); pose proof (hpos q Hq).
  apply eq_of_overlap; auto; lra.
Qed.

End Dissection.

(* ---------------------------------------------------------------------- *)
(* Pairwise machinery for edge partitions.                                 *)
(* ---------------------------------------------------------------------- *)

Lemma FOP_imp_mem {A : Type} (R T : A -> A -> Prop) :
  forall l0, ForallOrdPairs R l0 ->
  (forall a b, In a l0 -> In b l0 -> R a b -> T a b) ->
  ForallOrdPairs T l0.
Proof.
  induction l0 as [|x t IH]; intros H Himp.
  - constructor.
  - destruct (FOP_cons_inv _ _ _ H) as [Hf Ht].
    constructor.
    + rewrite Forall_forall in Hf |- *.
      intros b Hb.
      apply Himp; [left; reflexivity | right; exact Hb | apply Hf, Hb].
    + apply IH; [exact Ht |].
      intros a b Ha Hb; apply Himp; [right; exact Ha | right; exact Hb].
Qed.

Lemma sep1x_of_disjoint : forall p q : Sq,
  0 < qs p -> 0 < qs q -> DisjointOpen p q ->
  qy q < qy p + qs p -> qy p < qy q + qs q ->
  sep1 (qx p, qs p) (qx q, qs q).
Proof.
  intros p q Hp Hq Hd Hy1 Hy2.
  unfold sep1; simpl.
  destruct (Rle_dec (qx p + qs p) (qx q)) as [Hle | Hnle]; [left; lra |].
  destruct (Rle_dec (qx q + qs q) (qx p)) as [Hle | Hnle']; [right; lra |].
  exfalso.
  destruct (exists_open_inter p q Hp Hq ltac:(lra) ltac:(lra) Hy1 Hy2)
    as [u [v [H1 H2]]].
  exact (Hd u v H1 H2).
Qed.

Lemma sep1y_of_disjoint : forall p q : Sq,
  0 < qs p -> 0 < qs q -> DisjointOpen p q ->
  qx q < qx p + qs p -> qx p < qx q + qs q ->
  sep1 (qy p, qs p) (qy q, qs q).
Proof.
  intros p q Hp Hq Hd Hx1 Hx2.
  unfold sep1; simpl.
  destruct (Rle_dec (qy p + qs p) (qy q)) as [Hle | Hnle]; [left; lra |].
  destruct (Rle_dec (qy q + qs q) (qy p)) as [Hle | Hnle']; [right; lra |].
  exfalso.
  destruct (exists_open_inter p q Hp Hq Hx1 Hx2 ltac:(lra) ltac:(lra))
    as [u [v [H1 H2]]].
  exact (Hd u v H1 H2).
Qed.

(* ---------------------------------------------------------------------- *)
(* Edge partition sums.                                                    *)
(* ---------------------------------------------------------------------- *)

Lemma bottom_sum : forall (L : R) (l : list Sq), IsDissection L l -> 0 < L ->
  forall B : list Sq,
  (forall q, In q B -> In q l) ->
  (forall q, In q B -> qy q = 0) ->
  (forall q, In q l -> qy q = 0 -> In q B) ->
  ForallOrdPairs (fun p q => p <> q) B ->
  rsum (map qs B) = L.
Proof.
  intros L l hd HL B HBmem HBy HBall HBne.
  assert (Hsum : rsum (map snd (map (fun q => (qx q, qs q)) B)) = L - 0).
  { apply interval_cover_sum'.
    - lra.
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (diss_pos L l hd q (HBmem q Hq2)).
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (proj1 (tile_bounds L l hd q (HBmem q Hq2))).
    - apply ForallOrdPairs_map.
      apply (FOP_imp_mem (fun p q => p <> q)); [exact HBne |].
      intros a b Ha Hb Hne.
      apply sep1x_of_disjoint.
      + exact (diss_pos L l hd a (HBmem a Ha)).
      + exact (diss_pos L l hd b (HBmem b Hb)).
      + exact (disjoint_of_in_ne L l hd a b (HBmem a Ha) (HBmem b Hb) Hne).
      + rewrite (HBy a Ha), (HBy b Hb).
        pose proof (diss_pos L l hd a (HBmem a Ha)); lra.
      + rewrite (HBy a Ha), (HBy b Hb).
        pose proof (diss_pos L l hd b (HBmem b Hb)); lra.
    - intros x Hx1 Hx2.
      assert (Hin : InBig L x 0) by (unfold InBig; lra).
      destruct (proj1 (diss_cover L l hd x 0) Hin) as [r [Hr Hrc]].
      unfold InClosed in Hrc.
      pose proof (tile_bounds L l hd r Hr) as Hbr.
      assert (Hry : qy r = 0) by lra.
      exists (qx r, qs r); simpl.
      split; [| lra].
      apply (in_map (fun q => (qx q, qs q)) B r); apply HBall; assumption. }
  assert (Heq : map (fun a : Sq => snd (qx a, qs a)) B = map qs B).
  { apply map_ext; intros a; reflexivity. }
  rewrite map_map, Heq in Hsum.
  lra.
Qed.

Lemma top_sum : forall (L : R) (l : list Sq), IsDissection L l -> 0 < L ->
  forall B : list Sq,
  (forall q, In q B -> In q l) ->
  (forall q, In q B -> qy q + qs q = L) ->
  (forall q, In q l -> qy q + qs q = L -> In q B) ->
  ForallOrdPairs (fun p q => p <> q) B ->
  rsum (map qs B) = L.
Proof.
  intros L l hd HL B HBmem HBy HBall HBne.
  assert (Hsum : rsum (map snd (map (fun q => (qx q, qs q)) B)) = L - 0).
  { apply interval_cover_sum'.
    - lra.
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (diss_pos L l hd q (HBmem q Hq2)).
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (proj1 (tile_bounds L l hd q (HBmem q Hq2))).
    - apply ForallOrdPairs_map.
      apply (FOP_imp_mem (fun p q => p <> q)); [exact HBne |].
      intros a b Ha Hb Hne.
      pose proof (diss_pos L l hd a (HBmem a Ha)).
      pose proof (diss_pos L l hd b (HBmem b Hb)).
      pose proof (HBy a Ha); pose proof (HBy b Hb).
      apply sep1x_of_disjoint; try assumption; try lra.
      exact (disjoint_of_in_ne L l hd a b (HBmem a Ha) (HBmem b Hb) Hne).
    - intros x Hx1 Hx2.
      assert (Hin : InBig L x L) by (unfold InBig; lra).
      destruct (proj1 (diss_cover L l hd x L) Hin) as [r [Hr Hrc]].
      unfold InClosed in Hrc.
      pose proof (tile_bounds L l hd r Hr) as Hbr.
      assert (Hry : qy r + qs r = L) by lra.
      exists (qx r, qs r); simpl.
      split; [| lra].
      apply (in_map (fun q => (qx q, qs q)) B r); apply HBall; assumption. }
  assert (Heq : map (fun a : Sq => snd (qx a, qs a)) B = map qs B).
  { apply map_ext; intros a; reflexivity. }
  rewrite map_map, Heq in Hsum.
  lra.
Qed.

Lemma left_sum : forall (L : R) (l : list Sq), IsDissection L l -> 0 < L ->
  forall B : list Sq,
  (forall q, In q B -> In q l) ->
  (forall q, In q B -> qx q = 0) ->
  (forall q, In q l -> qx q = 0 -> In q B) ->
  ForallOrdPairs (fun p q => p <> q) B ->
  rsum (map qs B) = L.
Proof.
  intros L l hd HL B HBmem HBx HBall HBne.
  assert (Hsum : rsum (map snd (map (fun q => (qy q, qs q)) B)) = L - 0).
  { apply interval_cover_sum'.
    - lra.
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (diss_pos L l hd q (HBmem q Hq2)).
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (proj2 (tile_bounds L l hd q (HBmem q Hq2))).
    - apply ForallOrdPairs_map.
      apply (FOP_imp_mem (fun p q => p <> q)); [exact HBne |].
      intros a b Ha Hb Hne.
      pose proof (diss_pos L l hd a (HBmem a Ha)).
      pose proof (diss_pos L l hd b (HBmem b Hb)).
      pose proof (HBx a Ha); pose proof (HBx b Hb).
      apply sep1y_of_disjoint; try assumption; try lra.
      exact (disjoint_of_in_ne L l hd a b (HBmem a Ha) (HBmem b Hb) Hne).
    - intros y Hy1 Hy2.
      assert (Hin : InBig L 0 y) by (unfold InBig; lra).
      destruct (proj1 (diss_cover L l hd 0 y) Hin) as [r [Hr Hrc]].
      unfold InClosed in Hrc.
      pose proof (tile_bounds L l hd r Hr) as Hbr.
      assert (Hrx : qx r = 0) by lra.
      exists (qy r, qs r); simpl.
      split; [| lra].
      apply (in_map (fun q => (qy q, qs q)) B r); apply HBall; assumption. }
  assert (Heq : map (fun a : Sq => snd (qy a, qs a)) B = map qs B).
  { apply map_ext; intros a; reflexivity. }
  rewrite map_map, Heq in Hsum.
  lra.
Qed.

Lemma right_sum : forall (L : R) (l : list Sq), IsDissection L l -> 0 < L ->
  forall B : list Sq,
  (forall q, In q B -> In q l) ->
  (forall q, In q B -> qx q + qs q = L) ->
  (forall q, In q l -> qx q + qs q = L -> In q B) ->
  ForallOrdPairs (fun p q => p <> q) B ->
  rsum (map qs B) = L.
Proof.
  intros L l hd HL B HBmem HBx HBall HBne.
  assert (Hsum : rsum (map snd (map (fun q => (qy q, qs q)) B)) = L - 0).
  { apply interval_cover_sum'.
    - lra.
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (diss_pos L l hd q (HBmem q Hq2)).
    - intros p Hp.
      apply in_map_iff in Hp; destruct Hp as [q [Hq1 Hq2]]; subst p; simpl.
      exact (proj2 (tile_bounds L l hd q (HBmem q Hq2))).
    - apply ForallOrdPairs_map.
      apply (FOP_imp_mem (fun p q => p <> q)); [exact HBne |].
      intros a b Ha Hb Hne.
      pose proof (diss_pos L l hd a (HBmem a Ha)).
      pose proof (diss_pos L l hd b (HBmem b Hb)).
      pose proof (HBx a Ha); pose proof (HBx b Hb).
      apply sep1y_of_disjoint; try assumption; try lra.
      exact (disjoint_of_in_ne L l hd a b (HBmem a Ha) (HBmem b Hb) Hne).
    - intros y Hy1 Hy2.
      assert (Hin : InBig L L y) by (unfold InBig; lra).
      destruct (proj1 (diss_cover L l hd L y) Hin) as [r [Hr Hrc]].
      unfold InClosed in Hrc.
      pose proof (tile_bounds L l hd r Hr) as Hbr.
      assert (Hrx : qx r + qs r = L) by lra.
      exists (qy r, qs r); simpl.
      split; [| lra].
      apply (in_map (fun q => (qy q, qs q)) B r); apply HBall; assumption. }
  assert (Heq : map (fun a : Sq => snd (qy a, qs a)) B = map qs B).
  { apply map_ext; intros a; reflexivity. }
  rewrite map_map, Heq in Hsum.
  lra.
Qed.

(* ---------------------------------------------------------------------- *)
(* Corner data.                                                            *)
(* ---------------------------------------------------------------------- *)

Record CornerData (L : R) (l : list Sq) : Type := mkCornerData {
  cBL : Sq; cBR : Sq; cTL : Sq; cTR : Sq;
  cBLin : In cBL l; cBLx : qx cBL = 0; cBLy : qy cBL = 0;
  cBRin : In cBR l; cBRx : qx cBR + qs cBR = L; cBRy : qy cBR = 0;
  cTLin : In cTL l; cTLx : qx cTL = 0; cTLy : qy cTL + qs cTL = L;
  cTRin : In cTR l; cTRx : qx cTR + qs cTR = L; cTRy : qy cTR + qs cTR = L
}.

Arguments cBL {L l} _.
Arguments cBR {L l} _.
Arguments cTL {L l} _.
Arguments cTR {L l} _.
Arguments cBLin {L l} _.
Arguments cBLx {L l} _.
Arguments cBLy {L l} _.
Arguments cBRin {L l} _.
Arguments cBRx {L l} _.
Arguments cBRy {L l} _.
Arguments cTLin {L l} _.
Arguments cTLx {L l} _.
Arguments cTLy {L l} _.
Arguments cTRin {L l} _.
Arguments cTRx {L l} _.
Arguments cTRy {L l} _.

Lemma exists_cornerData : forall (L : R) (l : list Sq),
  IsDissection L l -> 0 < L -> exists cd : CornerData L l, True.
Proof.
  intros L l hd HL.
  destruct (exists_corner_bl L l hd HL) as [BL [HBL [HBLx HBLy]]].
  destruct (exists_corner_br L l hd HL) as [BR [HBR [HBRx HBRy]]].
  destruct (exists_corner_tl L l hd HL) as [TL [HTL [HTLx HTLy]]].
  destruct (exists_corner_tr L l hd HL) as [TR [HTR [HTRx HTRy]]].
  exists (mkCornerData L l BL BR TL TR HBL HBLx HBLy HBR HBRx HBRy
    HTL HTLx HTLy HTR HTRx HTRy).
  exact I.
Qed.

(* The four corner tiles are pairwise distinct. *)

Lemma corner_ne_BL_BR : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l, cBL cd <> cBR cd.
Proof.
  intros L l hd H2 cd He.
  pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)) as Hlt.
  pose proof (cBRx cd) as Hx.
  rewrite <- He in Hx.
  rewrite (cBLx cd) in Hx.
  lra.
Qed.

Lemma corner_ne_BL_TL : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l, cBL cd <> cTL cd.
Proof.
  intros L l hd H2 cd He.
  pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)) as Hlt.
  pose proof (cTLy cd) as Hy.
  rewrite <- He in Hy.
  rewrite (cBLy cd) in Hy.
  lra.
Qed.

Lemma corner_ne_BL_TR : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l, cBL cd <> cTR cd.
Proof.
  intros L l hd H2 cd He.
  pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)) as Hlt.
  pose proof (cTRx cd) as Hx.
  rewrite <- He in Hx.
  rewrite (cBLx cd) in Hx.
  lra.
Qed.

Lemma corner_ne_BR_TL : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l, cBR cd <> cTL cd.
Proof.
  intros L l hd H2 cd He.
  pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)) as Hlt.
  pose proof (cTLy cd) as Hy.
  rewrite <- He in Hy.
  rewrite (cBRy cd) in Hy.
  lra.
Qed.

Lemma corner_ne_BR_TR : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l, cBR cd <> cTR cd.
Proof.
  intros L l hd H2 cd He.
  pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)) as Hlt.
  pose proof (cTRy cd) as Hy.
  rewrite <- He in Hy.
  rewrite (cBRy cd) in Hy.
  lra.
Qed.

Lemma corner_ne_TL_TR : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l, cTL cd <> cTR cd.
Proof.
  intros L l hd H2 cd He.
  pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)) as Hlt.
  pose proof (cTRx cd) as Hx.
  rewrite <- He in Hx.
  rewrite (cTLx cd) in Hx.
  lra.
Qed.

(* Two distinct pieces of equal side contradict pairwise non-congruence. *)
Lemma no_congruent_pair : forall (l : list Sq),
  PairwiseNoncongruent l ->
  forall p q, In p l -> In q l -> p <> q -> qs p = qs q -> False.
Proof.
  intros l Hnc p q Hp Hq Hne Hs.
  destruct (ForallOrdPairs_In Hnc p q Hp Hq) as [He | [H | H]].
  - congruence.
  - exact (H (congruent_of_side_eq p q Hs)).
  - exact (H (congruent_of_side_eq q p (eq_sym Hs))).
Qed.

(* A non-corner piece can touch at most one edge. *)

Lemma flag_excl_BT : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall E, In E l ->
  qy E = 0 -> qy E + qs E = L -> False.
Proof.
  intros L l hd H2 E HE Hy Ht.
  pose proof (side_lt_of_two_le L l hd H2 E HE); lra.
Qed.

Lemma flag_excl_LR : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall E, In E l ->
  qx E = 0 -> qx E + qs E = L -> False.
Proof.
  intros L l hd H2 E HE Hx Hr.
  pose proof (side_lt_of_two_le L l hd H2 E HE); lra.
Qed.

Lemma flag_excl_BL : forall L l (hd : IsDissection L l)
  (cd : CornerData L l) E, In E l -> E <> cBL cd ->
  qy E = 0 -> qx E = 0 -> False.
Proof.
  intros L l hd cd E HE Hne Hy Hx.
  apply Hne.
  exact (corner_bl_unique L l hd E (cBL cd) HE (cBLin cd)
    Hx Hy (cBLx cd) (cBLy cd)).
Qed.

Lemma flag_excl_BR : forall L l (hd : IsDissection L l)
  (cd : CornerData L l) E, In E l -> E <> cBR cd ->
  qy E = 0 -> qx E + qs E = L -> False.
Proof.
  intros L l hd cd E HE Hne Hy Hx.
  apply Hne.
  exact (corner_br_unique L l hd E (cBR cd) HE (cBRin cd)
    Hx Hy (cBRx cd) (cBRy cd)).
Qed.

Lemma flag_excl_TL : forall L l (hd : IsDissection L l)
  (cd : CornerData L l) E, In E l -> E <> cTL cd ->
  qy E + qs E = L -> qx E = 0 -> False.
Proof.
  intros L l hd cd E HE Hne Hy Hx.
  apply Hne.
  exact (corner_tl_unique L l hd E (cTL cd) HE (cTLin cd)
    Hx Hy (cTLx cd) (cTLy cd)).
Qed.

Lemma flag_excl_TR : forall L l (hd : IsDissection L l)
  (cd : CornerData L l) E, In E l -> E <> cTR cd ->
  qy E + qs E = L -> qx E + qs E = L -> False.
Proof.
  intros L l hd cd E HE Hne Hy Hx.
  apply Hne.
  exact (corner_tr_unique L l hd E (cTR cd) HE (cTRin cd)
    Hx Hy (cTRx cd) (cTRy cd)).
Qed.

(* ---------------------------------------------------------------------- *)
(* Two- and three-piece edge partitions.                                   *)
(* ---------------------------------------------------------------------- *)

Lemma bottom_two : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall cd : CornerData L l,
  (forall q, In q l -> qy q = 0 -> q = cBL cd \/ q = cBR cd) ->
  qs (cBL cd) + qs (cBR cd) = L.
Proof.
  intros L l hd H2 HL cd Honly.
  pose proof (corner_ne_BL_BR L l hd H2 cd) as Hne.
  assert (HB : rsum (map qs [cBL cd; cBR cd]) = L).
  { apply (bottom_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cBLin cd) | exact (cBRin cd)].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cBLy cd) | exact (cBRy cd)].
    - intros q Hql Hqy.
      destruct (Honly q Hql Hqy) as [-> | ->]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne | apply Forall_nil].
      + apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma top_two : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall cd : CornerData L l,
  (forall q, In q l -> qy q + qs q = L -> q = cTL cd \/ q = cTR cd) ->
  qs (cTL cd) + qs (cTR cd) = L.
Proof.
  intros L l hd H2 HL cd Honly.
  pose proof (corner_ne_TL_TR L l hd H2 cd) as Hne.
  assert (HB : rsum (map qs [cTL cd; cTR cd]) = L).
  { apply (top_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cTLin cd) | exact (cTRin cd)].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cTLy cd) | exact (cTRy cd)].
    - intros q Hql Hqy.
      destruct (Honly q Hql Hqy) as [-> | ->]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne | apply Forall_nil].
      + apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma left_two : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall cd : CornerData L l,
  (forall q, In q l -> qx q = 0 -> q = cBL cd \/ q = cTL cd) ->
  qs (cBL cd) + qs (cTL cd) = L.
Proof.
  intros L l hd H2 HL cd Honly.
  pose proof (corner_ne_BL_TL L l hd H2 cd) as Hne.
  assert (HB : rsum (map qs [cBL cd; cTL cd]) = L).
  { apply (left_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cBLin cd) | exact (cTLin cd)].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cBLx cd) | exact (cTLx cd)].
    - intros q Hql Hqx.
      destruct (Honly q Hql Hqx) as [-> | ->]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne | apply Forall_nil].
      + apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma right_two : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall cd : CornerData L l,
  (forall q, In q l -> qx q + qs q = L -> q = cBR cd \/ q = cTR cd) ->
  qs (cBR cd) + qs (cTR cd) = L.
Proof.
  intros L l hd H2 HL cd Honly.
  pose proof (corner_ne_BR_TR L l hd H2 cd) as Hne.
  assert (HB : rsum (map qs [cBR cd; cTR cd]) = L).
  { apply (right_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cBRin cd) | exact (cTRin cd)].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | []]]; subst q;
        [exact (cBRx cd) | exact (cTRx cd)].
    - intros q Hql Hqx.
      destruct (Honly q Hql Hqx) as [-> | ->]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne | apply Forall_nil].
      + apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma bottom_three : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall (cd : CornerData L l) (E : Sq),
  In E l -> E <> cBL cd -> E <> cBR cd -> qy E = 0 ->
  (forall q, In q l -> qy q = 0 -> q = cBL cd \/ q = cBR cd \/ q = E) ->
  qs (cBL cd) + qs (cBR cd) + qs E = L.
Proof.
  intros L l hd H2 HL cd E HE HneBL HneBR HEy Honly.
  pose proof (corner_ne_BL_BR L l hd H2 cd) as Hne1.
  assert (HB : rsum (map qs [cBL cd; cBR cd; E]) = L).
  { apply (bottom_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cBLin cd) | exact (cBRin cd) | exact HE].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cBLy cd) | exact (cBRy cd) | exact HEy].
    - intros q Hql Hqy.
      destruct (Honly q Hql Hqy) as [-> | [-> | ->]]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne1 |].
        apply Forall_cons; [exact (not_eq_sym HneBL) | apply Forall_nil].
      + apply FOP_cons.
        * apply Forall_cons; [exact (not_eq_sym HneBR) | apply Forall_nil].
        * apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma top_three : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall (cd : CornerData L l) (E : Sq),
  In E l -> E <> cTL cd -> E <> cTR cd -> qy E + qs E = L ->
  (forall q, In q l -> qy q + qs q = L ->
     q = cTL cd \/ q = cTR cd \/ q = E) ->
  qs (cTL cd) + qs (cTR cd) + qs E = L.
Proof.
  intros L l hd H2 HL cd E HE HneTL HneTR HEy Honly.
  pose proof (corner_ne_TL_TR L l hd H2 cd) as Hne1.
  assert (HB : rsum (map qs [cTL cd; cTR cd; E]) = L).
  { apply (top_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cTLin cd) | exact (cTRin cd) | exact HE].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cTLy cd) | exact (cTRy cd) | exact HEy].
    - intros q Hql Hqy.
      destruct (Honly q Hql Hqy) as [-> | [-> | ->]]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne1 |].
        apply Forall_cons; [exact (not_eq_sym HneTL) | apply Forall_nil].
      + apply FOP_cons.
        * apply Forall_cons; [exact (not_eq_sym HneTR) | apply Forall_nil].
        * apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma left_three : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall (cd : CornerData L l) (E : Sq),
  In E l -> E <> cBL cd -> E <> cTL cd -> qx E = 0 ->
  (forall q, In q l -> qx q = 0 -> q = cBL cd \/ q = cTL cd \/ q = E) ->
  qs (cBL cd) + qs (cTL cd) + qs E = L.
Proof.
  intros L l hd H2 HL cd E HE HneBL HneTL HEx Honly.
  pose proof (corner_ne_BL_TL L l hd H2 cd) as Hne1.
  assert (HB : rsum (map qs [cBL cd; cTL cd; E]) = L).
  { apply (left_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cBLin cd) | exact (cTLin cd) | exact HE].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cBLx cd) | exact (cTLx cd) | exact HEx].
    - intros q Hql Hqx.
      destruct (Honly q Hql Hqx) as [-> | [-> | ->]]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne1 |].
        apply Forall_cons; [exact (not_eq_sym HneBL) | apply Forall_nil].
      + apply FOP_cons.
        * apply Forall_cons; [exact (not_eq_sym HneTL) | apply Forall_nil].
        * apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

Lemma right_three : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall (cd : CornerData L l) (E : Sq),
  In E l -> E <> cBR cd -> E <> cTR cd -> qx E + qs E = L ->
  (forall q, In q l -> qx q + qs q = L ->
     q = cBR cd \/ q = cTR cd \/ q = E) ->
  qs (cBR cd) + qs (cTR cd) + qs E = L.
Proof.
  intros L l hd H2 HL cd E HE HneBR HneTR HEx Honly.
  pose proof (corner_ne_BR_TR L l hd H2 cd) as Hne1.
  assert (HB : rsum (map qs [cBR cd; cTR cd; E]) = L).
  { apply (right_sum L l hd HL).
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cBRin cd) | exact (cTRin cd) | exact HE].
    - intros q Hq; simpl in Hq.
      destruct Hq as [Hq | [Hq | [Hq | []]]]; subst q;
        [exact (cBRx cd) | exact (cTRx cd) | exact HEx].
    - intros q Hql Hqx.
      destruct (Honly q Hql Hqx) as [-> | [-> | ->]]; simpl; auto.
    - apply FOP_cons.
      + apply Forall_cons; [exact Hne1 |].
        apply Forall_cons; [exact (not_eq_sym HneBR) | apply Forall_nil].
      + apply FOP_cons.
        * apply Forall_cons; [exact (not_eq_sym HneTR) | apply Forall_nil].
        * apply FOP_cons; [apply Forall_nil | apply FOP_nil]. }
  simpl in HB; lra.
Qed.

(* ---------------------------------------------------------------------- *)
(* The contradiction lemmas.                                               *)
(* ---------------------------------------------------------------------- *)

Lemma clean_bottom_left : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> PairwiseNoncongruent l ->
  forall cd : CornerData L l,
  (forall q, In q l -> qy q = 0 -> q = cBL cd \/ q = cBR cd) ->
  (forall q, In q l -> qx q = 0 -> q = cBL cd \/ q = cTL cd) ->
  False.
Proof.
  intros L l hd H2 HL Hnc cd Hbot Hleft.
  pose proof (bottom_two L l hd H2 HL cd Hbot).
  pose proof (left_two L l hd H2 HL cd Hleft).
  exact (no_congruent_pair l Hnc (cBR cd) (cTL cd) (cBRin cd) (cTLin cd)
    (corner_ne_BR_TL L l hd H2 cd) ltac:(lra)).
Qed.

Lemma clean_bottom_right : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> PairwiseNoncongruent l ->
  forall cd : CornerData L l,
  (forall q, In q l -> qy q = 0 -> q = cBL cd \/ q = cBR cd) ->
  (forall q, In q l -> qx q + qs q = L -> q = cBR cd \/ q = cTR cd) ->
  False.
Proof.
  intros L l hd H2 HL Hnc cd Hbot Hright.
  pose proof (bottom_two L l hd H2 HL cd Hbot).
  pose proof (right_two L l hd H2 HL cd Hright).
  exact (no_congruent_pair l Hnc (cBL cd) (cTR cd) (cBLin cd) (cTRin cd)
    (corner_ne_BL_TR L l hd H2 cd) ltac:(lra)).
Qed.

Lemma clean_top_left : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> PairwiseNoncongruent l ->
  forall cd : CornerData L l,
  (forall q, In q l -> qy q + qs q = L -> q = cTL cd \/ q = cTR cd) ->
  (forall q, In q l -> qx q = 0 -> q = cBL cd \/ q = cTL cd) ->
  False.
Proof.
  intros L l hd H2 HL Hnc cd Htop Hleft.
  pose proof (top_two L l hd H2 HL cd Htop).
  pose proof (left_two L l hd H2 HL cd Hleft).
  exact (no_congruent_pair l Hnc (cBL cd) (cTR cd) (cBLin cd) (cTRin cd)
    (corner_ne_BL_TR L l hd H2 cd) ltac:(lra)).
Qed.

Lemma clean_top_right : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> PairwiseNoncongruent l ->
  forall cd : CornerData L l,
  (forall q, In q l -> qy q + qs q = L -> q = cTL cd \/ q = cTR cd) ->
  (forall q, In q l -> qx q + qs q = L -> q = cBR cd \/ q = cTR cd) ->
  False.
Proof.
  intros L l hd H2 HL Hnc cd Htop Hright.
  pose proof (top_two L l hd H2 HL cd Htop).
  pose proof (right_two L l hd H2 HL cd Hright).
  exact (no_congruent_pair l Hnc (cBR cd) (cTL cd) (cBRin cd) (cTLin cd)
    (corner_ne_BR_TL L l hd H2 cd) ltac:(lra)).
Qed.

Lemma opposite_bottom_top : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall (cd : CornerData L l) (E1 E2 : Sq),
  In E1 l -> In E2 l ->
  E1 <> cBL cd -> E1 <> cBR cd -> E2 <> cTL cd -> E2 <> cTR cd ->
  qy E1 = 0 -> qy E2 + qs E2 = L ->
  (forall q, In q l -> qy q = 0 -> q = cBL cd \/ q = cBR cd \/ q = E1) ->
  (forall q, In q l -> qy q + qs q = L ->
     q = cTL cd \/ q = cTR cd \/ q = E2) ->
  (forall q, In q l -> qx q = 0 -> q = cBL cd \/ q = cTL cd) ->
  (forall q, In q l -> qx q + qs q = L -> q = cBR cd \/ q = cTR cd) ->
  False.
Proof.
  intros L l hd H2 HL cd E1 E2 HE1 HE2 Hne1BL Hne1BR Hne2TL Hne2TR
    HE1y HE2y Hbot Htop Hleft Hright.
  pose proof (bottom_three L l hd H2 HL cd E1 HE1 Hne1BL Hne1BR HE1y Hbot).
  pose proof (top_three L l hd H2 HL cd E2 HE2 Hne2TL Hne2TR HE2y Htop).
  pose proof (left_two L l hd H2 HL cd Hleft).
  pose proof (right_two L l hd H2 HL cd Hright).
  pose proof (diss_pos L l hd E1 HE1).
  pose proof (diss_pos L l hd E2 HE2).
  lra.
Qed.

Lemma opposite_left_right : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> 0 < L -> forall (cd : CornerData L l) (E1 E2 : Sq),
  In E1 l -> In E2 l ->
  E1 <> cBL cd -> E1 <> cTL cd -> E2 <> cBR cd -> E2 <> cTR cd ->
  qx E1 = 0 -> qx E2 + qs E2 = L ->
  (forall q, In q l -> qy q = 0 -> q = cBL cd \/ q = cBR cd) ->
  (forall q, In q l -> qy q + qs q = L -> q = cTL cd \/ q = cTR cd) ->
  (forall q, In q l -> qx q = 0 -> q = cBL cd \/ q = cTL cd \/ q = E1) ->
  (forall q, In q l -> qx q + qs q = L ->
     q = cBR cd \/ q = cTR cd \/ q = E2) ->
  False.
Proof.
  intros L l hd H2 HL cd E1 E2 HE1 HE2 Hne1BL Hne1TL Hne2BR Hne2TR
    HE1x HE2x Hbot Htop Hleft Hright.
  pose proof (left_three L l hd H2 HL cd E1 HE1 Hne1BL Hne1TL HE1x Hleft).
  pose proof (right_three L l hd H2 HL cd E2 HE2 Hne2BR Hne2TR HE2x Hright).
  pose proof (bottom_two L l hd H2 HL cd Hbot).
  pose proof (top_two L l hd H2 HL cd Htop).
  pose proof (diss_pos L l hd E1 HE1).
  pose proof (diss_pos L l hd E2 HE2).
  lra.
Qed.

(* ---------------------------------------------------------------------- *)
(* Extracting the corner tiles from the list.                              *)
(* ---------------------------------------------------------------------- *)

Lemma corners_nodup : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l,
  NoDup [cBL cd; cBR cd; cTL cd; cTR cd].
Proof.
  intros L l hd H2 cd.
  pose proof (corner_ne_BL_BR L l hd H2 cd) as N1.
  pose proof (corner_ne_BL_TL L l hd H2 cd) as N2.
  pose proof (corner_ne_BL_TR L l hd H2 cd) as N3.
  pose proof (corner_ne_BR_TL L l hd H2 cd) as N4.
  pose proof (corner_ne_BR_TR L l hd H2 cd) as N5.
  pose proof (corner_ne_TL_TR L l hd H2 cd) as N6.
  apply NoDup_cons; [intros [H|[H|[H|[]]]]; congruence |].
  apply NoDup_cons; [intros [H|[H|[]]]; congruence |].
  apply NoDup_cons; [intros [H|[]]; congruence |].
  apply NoDup_cons; [intros [] |].
  apply NoDup_nil.
Qed.

Lemma corners_incl : forall L l (cd : CornerData L l),
  incl [cBL cd; cBR cd; cTL cd; cTR cd] l.
Proof.
  intros L l cd q Hq.
  destruct Hq as [H|[H|[H|[H|[]]]]]; subst q;
    [exact (cBLin cd) | exact (cBRin cd) | exact (cTLin cd)
     | exact (cTRin cd)].
Qed.

Lemma exists_rest : forall L l (hd : IsDissection L l),
  (2 <= length l)%nat -> forall cd : CornerData L l,
  exists rest,
    Permutation l ([cBL cd; cBR cd; cTL cd; cTR cd] ++ rest) /\
    (length rest + 4 = length l)%nat.
Proof.
  intros L l hd H2 cd.
  destruct (nodup_incl_perm_append [cBL cd; cBR cd; cTL cd; cTR cd] l
    (corners_nodup L l hd H2 cd) (corners_incl L l cd)) as [rest Hperm].
  exists rest; split; [exact Hperm |].
  pose proof (Permutation_length Hperm) as Hl.
  rewrite length_app in Hl.
  simpl in Hl; lia.
Qed.

Lemma rest_facts : forall L l (hd : IsDissection L l)
  (cd : CornerData L l) (rest : list Sq),
  Permutation l ([cBL cd; cBR cd; cTL cd; cTR cd] ++ rest) ->
  forall E, In E rest ->
  In E l /\ E <> cBL cd /\ E <> cBR cd /\ E <> cTL cd /\ E <> cTR cd.
Proof.
  intros L l hd cd rest Hperm E HE.
  assert (HEl : In E l).
  { apply (Permutation_in E (Permutation_sym Hperm)).
    apply in_or_app; right; exact HE. }
  assert (Hdisj : ForallOrdPairs DisjointOpen
      ([cBL cd; cBR cd; cTL cd; cTR cd] ++ rest)).
  { exact (FOP_perm DisjointOpen (fun a b H u v H1 H2 => H u v H2 H1)
      l _ Hperm (diss_disj L l hd)). }
  destruct (FOP_app_inv _ _ _ Hdisj) as [_ [_ Hcross]].
  assert (HBLm : In (cBL cd) [cBL cd; cBR cd; cTL cd; cTR cd])
    by (simpl; auto).
  assert (HBRm : In (cBR cd) [cBL cd; cBR cd; cTL cd; cTR cd])
    by (simpl; auto).
  assert (HTLm : In (cTL cd) [cBL cd; cBR cd; cTL cd; cTR cd])
    by (simpl; auto).
  assert (HTRm : In (cTR cd) [cBL cd; cBR cd; cTL cd; cTR cd])
    by (simpl; auto).
  split; [exact HEl |].
  split.
  { intro He.
    pose proof (Hcross (cBL cd) E HBLm HE) as Hd.
    rewrite He in Hd.
    pose proof (center_in_open (cBL cd)
      (diss_pos L l hd (cBL cd) (cBLin cd))) as Hc.
    exact (Hd _ _ Hc Hc). }
  split.
  { intro He.
    pose proof (Hcross (cBR cd) E HBRm HE) as Hd.
    rewrite He in Hd.
    pose proof (center_in_open (cBR cd)
      (diss_pos L l hd (cBR cd) (cBRin cd))) as Hc.
    exact (Hd _ _ Hc Hc). }
  split.
  { intro He.
    pose proof (Hcross (cTL cd) E HTLm HE) as Hd.
    rewrite He in Hd.
    pose proof (center_in_open (cTL cd)
      (diss_pos L l hd (cTL cd) (cTLin cd))) as Hc.
    exact (Hd _ _ Hc Hc). }
  { intro He.
    pose proof (Hcross (cTR cd) E HTRm HE) as Hd.
    rewrite He in Hd.
    pose proof (center_in_open (cTR cd)
      (diss_pos L l hd (cTR cd) (cTRin cd))) as Hc.
    exact (Hd _ _ Hc Hc). }
Qed.

(* ---------------------------------------------------------------------- *)
(* The impossibility theorems.                                             *)
(* ---------------------------------------------------------------------- *)

Theorem four_le_length : forall L l, IsPerfectSquaredSquare L l ->
  (4 <= length l)%nat.
Proof.
  intros L l [hd [H2 Hnc]].
  assert (Hne : l <> []).
  { intro He; subst l; simpl in H2; lia. }
  pose proof (side_pos_of_dissection L l hd Hne) as HL.
  destruct (exists_cornerData L l hd HL) as [cd _].
  pose proof (NoDup_incl_length (corners_nodup L l hd H2 cd)
    (corners_incl L l cd)) as Hlen.
  simpl in Hlen; lia.
Qed.

Theorem length_ne_four : forall L l,
  IsPerfectSquaredSquare L l -> length l <> 4%nat.
Proof.
  intros L l [hd [H2 Hnc]] Hlen.
  assert (Hne : l <> []) by (intro He; subst l; discriminate).
  pose proof (side_pos_of_dissection L l hd Hne) as HL.
  destruct (exists_cornerData L l hd HL) as [cd _].
  destruct (exists_rest L l hd H2 cd) as [rest [Hperm Hrl]].
  assert (Hrest : rest = []).
  { destruct rest; [reflexivity | simpl in Hrl; lia]. }
  subst rest.
  rewrite app_nil_r in Hperm.
  assert (Hmem : forall q, In q l ->
      q = cBL cd \/ q = cBR cd \/ q = cTL cd \/ q = cTR cd).
  { intros q Hq.
    pose proof (Permutation_in q Hperm Hq) as Hq2.
    destruct Hq2 as [H|[H|[H|[H|[]]]]]; subst q; tauto. }
  apply (clean_bottom_right L l hd H2 HL Hnc cd).
  - intros q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | ->]]].
    + left; reflexivity.
    + right; reflexivity.
    + exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLy cd); lra.
    + exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRy cd); lra.
  - intros q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | ->]]].
    + exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLx cd); lra.
    + left; reflexivity.
    + exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLx cd); lra.
    + right; reflexivity.
Qed.

Theorem length_ne_five : forall L l,
  IsPerfectSquaredSquare L l -> length l <> 5%nat.
Proof.
  intros L l [hd [H2 Hnc]] Hlen.
  assert (Hne : l <> []) by (intro He; subst l; discriminate).
  pose proof (side_pos_of_dissection L l hd Hne) as HL.
  destruct (exists_cornerData L l hd HL) as [cd _].
  destruct (exists_rest L l hd H2 cd) as [rest [Hperm Hrl]].
  destruct rest as [|E rest']; [simpl in Hrl; lia |].
  destruct rest' as [|F rest'']; [| simpl in Hrl; lia].
  destruct (rest_facts L l hd cd [E] Hperm E (in_eq _ _))
    as [HEl [HEBL [HEBR [HETL HETR]]]].
  assert (Hmem : forall q, In q l -> q = cBL cd \/ q = cBR cd \/
      q = cTL cd \/ q = cTR cd \/ q = E).
  { intros q Hq.
    pose proof (Permutation_in q Hperm Hq) as Hq2.
    apply in_app_or in Hq2.
    destruct Hq2 as [[H|[H|[H|[H|[]]]]] | [H|[]]]; subst q; tauto. }
  assert (Hbotc : qy E <> 0 -> forall q, In q l -> qy q = 0 ->
      q = cBL cd \/ q = cBR cd).
  { intros HEy q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | ->]]]].
    - left; reflexivity.
    - right; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRy cd); lra.
    - congruence. }
  assert (Htopc : qy E + qs E <> L -> forall q, In q l ->
      qy q + qs q = L -> q = cTL cd \/ q = cTR cd).
  { intros HEy q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | ->]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRy cd); lra.
    - left; reflexivity.
    - right; reflexivity.
    - congruence. }
  assert (Hleftc : qx E <> 0 -> forall q, In q l -> qx q = 0 ->
      q = cBL cd \/ q = cTL cd).
  { intros HEx q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | ->]]]].
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRx cd); lra.
    - right; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRx cd); lra.
    - congruence. }
  assert (Hrightc : qx E + qs E <> L -> forall q, In q l ->
      qx q + qs q = L -> q = cBR cd \/ q = cTR cd).
  { intros HEx q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | ->]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLx cd); lra.
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLx cd); lra.
    - right; reflexivity.
    - congruence. }
  destruct (Req_dec (qy E) 0) as [HpB | HpB].
  - assert (HnT : qy E + qs E <> L)
      by (intro h; exact (flag_excl_BT L l hd H2 E HEl HpB h)).
    assert (HnL : qx E <> 0)
      by (intro h; exact (flag_excl_BL L l hd cd E HEl HEBL HpB h)).
    exact (clean_top_left L l hd H2 HL Hnc cd (Htopc HnT) (Hleftc HnL)).
  - destruct (Req_dec (qy E + qs E) L) as [HpT | HpT].
    + assert (HnL : qx E <> 0)
        by (intro h; exact (flag_excl_TL L l hd cd E HEl HETL HpT h)).
      exact (clean_bottom_left L l hd H2 HL Hnc cd (Hbotc HpB)
        (Hleftc HnL)).
    + destruct (Req_dec (qx E) 0) as [HpL | HpL].
      * assert (HnR : qx E + qs E <> L)
          by (intro h; exact (flag_excl_LR L l hd H2 E HEl HpL h)).
        exact (clean_bottom_right L l hd H2 HL Hnc cd (Hbotc HpB)
          (Hrightc HnR)).
      * exact (clean_bottom_left L l hd H2 HL Hnc cd (Hbotc HpB)
          (Hleftc HpL)).
Qed.

Theorem length_ne_six : forall L l,
  IsPerfectSquaredSquare L l -> length l <> 6%nat.
Proof.
  intros L l [hd [H2 Hnc]] Hlen.
  assert (Hne : l <> []) by (intro He; subst l; discriminate).
  pose proof (side_pos_of_dissection L l hd Hne) as HL.
  destruct (exists_cornerData L l hd HL) as [cd _].
  destruct (exists_rest L l hd H2 cd) as [rest [Hperm Hrl]].
  destruct rest as [|E1 rest']; [simpl in Hrl; lia |].
  destruct rest' as [|E2 rest'']; [simpl in Hrl; lia |].
  destruct rest'' as [|G rest''']; [| simpl in Hrl; lia].
  destruct (rest_facts L l hd cd [E1; E2] Hperm E1 (in_eq _ _))
    as [HE1l [HE1BL [HE1BR [HE1TL HE1TR]]]].
  destruct (rest_facts L l hd cd [E1; E2] Hperm E2
    (in_cons _ _ _ (in_eq _ _)))
    as [HE2l [HE2BL [HE2BR [HE2TL HE2TR]]]].
  assert (Hmem : forall q, In q l -> q = cBL cd \/ q = cBR cd \/
      q = cTL cd \/ q = cTR cd \/ q = E1 \/ q = E2).
  { intros q Hq.
    pose proof (Permutation_in q Hperm Hq) as Hq2.
    apply in_app_or in Hq2.
    destruct Hq2 as [[H|[H|[H|[H|[]]]]] | [H|[H|[]]]]; subst q; tauto. }
  (* clean-edge characterizations, conditional on the extras avoiding it *)
  assert (Hbotc : qy E1 <> 0 -> qy E2 <> 0 -> forall q, In q l ->
      qy q = 0 -> q = cBL cd \/ q = cBR cd).
  { intros Hn1 Hn2 q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - left; reflexivity.
    - right; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRy cd); lra.
    - congruence.
    - congruence. }
  assert (Htopc : qy E1 + qs E1 <> L -> qy E2 + qs E2 <> L ->
      forall q, In q l -> qy q + qs q = L -> q = cTL cd \/ q = cTR cd).
  { intros Hn1 Hn2 q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRy cd); lra.
    - left; reflexivity.
    - right; reflexivity.
    - congruence.
    - congruence. }
  assert (Hleftc : qx E1 <> 0 -> qx E2 <> 0 -> forall q, In q l ->
      qx q = 0 -> q = cBL cd \/ q = cTL cd).
  { intros Hn1 Hn2 q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRx cd); lra.
    - right; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRx cd); lra.
    - congruence.
    - congruence. }
  assert (Hrightc : qx E1 + qs E1 <> L -> qx E2 + qs E2 <> L ->
      forall q, In q l -> qx q + qs q = L -> q = cBR cd \/ q = cTR cd).
  { intros Hn1 Hn2 q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLx cd); lra.
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLx cd); lra.
    - right; reflexivity.
    - congruence.
    - congruence. }
  (* three-piece characterizations *)
  assert (Hbot31 : qy E2 <> 0 -> forall q, In q l -> qy q = 0 ->
      q = cBL cd \/ q = cBR cd \/ q = E1).
  { intros Hn2 q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - left; reflexivity.
    - right; left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRy cd); lra.
    - right; right; reflexivity.
    - congruence. }
  assert (Hbot32 : qy E1 <> 0 -> forall q, In q l -> qy q = 0 ->
      q = cBL cd \/ q = cBR cd \/ q = E2).
  { intros Hn1 q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - left; reflexivity.
    - right; left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRy cd); lra.
    - congruence.
    - right; right; reflexivity. }
  assert (Htop31 : qy E2 + qs E2 <> L -> forall q, In q l ->
      qy q + qs q = L -> q = cTL cd \/ q = cTR cd \/ q = E1).
  { intros Hn2 q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRy cd); lra.
    - left; reflexivity.
    - right; left; reflexivity.
    - right; right; reflexivity.
    - congruence. }
  assert (Htop32 : qy E1 + qs E1 <> L -> forall q, In q l ->
      qy q + qs q = L -> q = cTL cd \/ q = cTR cd \/ q = E2).
  { intros Hn1 q Hql Hqy.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLy cd); lra.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRy cd); lra.
    - left; reflexivity.
    - right; left; reflexivity.
    - congruence.
    - right; right; reflexivity. }
  assert (Hleft31 : qx E2 <> 0 -> forall q, In q l -> qx q = 0 ->
      q = cBL cd \/ q = cTL cd \/ q = E1).
  { intros Hn2 q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRx cd); lra.
    - right; left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRx cd); lra.
    - right; right; reflexivity.
    - congruence. }
  assert (Hleft32 : qx E1 <> 0 -> forall q, In q l -> qx q = 0 ->
      q = cBL cd \/ q = cTL cd \/ q = E2).
  { intros Hn1 q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBR cd) (cBRin cd)).
      pose proof (cBRx cd); lra.
    - right; left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTR cd) (cTRin cd)).
      pose proof (cTRx cd); lra.
    - congruence.
    - right; right; reflexivity. }
  assert (Hright31 : qx E2 + qs E2 <> L -> forall q, In q l ->
      qx q + qs q = L -> q = cBR cd \/ q = cTR cd \/ q = E1).
  { intros Hn2 q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLx cd); lra.
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLx cd); lra.
    - right; left; reflexivity.
    - right; right; reflexivity.
    - congruence. }
  assert (Hright32 : qx E1 + qs E1 <> L -> forall q, In q l ->
      qx q + qs q = L -> q = cBR cd \/ q = cTR cd \/ q = E2).
  { intros Hn1 q Hql Hqx.
    destruct (Hmem q Hql) as [-> | [-> | [-> | [-> | [-> | ->]]]]].
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cBL cd) (cBLin cd)).
      pose proof (cBLx cd); lra.
    - left; reflexivity.
    - exfalso.
      pose proof (side_lt_of_two_le L l hd H2 (cTL cd) (cTLin cd)).
      pose proof (cTLx cd); lra.
    - right; left; reflexivity.
    - congruence.
    - right; right; reflexivity. }
  (* decision tree over the edges occupied by the two extras *)
  destruct (Req_dec (qy E1) 0) as [HpB1 | HpB1].
  - assert (H1nT : qy E1 + qs E1 <> L)
      by (intro h; exact (flag_excl_BT L l hd H2 E1 HE1l HpB1 h)).
    assert (H1nL : qx E1 <> 0)
      by (intro h; exact (flag_excl_BL L l hd cd E1 HE1l HE1BL HpB1 h)).
    assert (H1nR : qx E1 + qs E1 <> L)
      by (intro h; exact (flag_excl_BR L l hd cd E1 HE1l HE1BR HpB1 h)).
    destruct (Req_dec (qy E2 + qs E2) L) as [HpT2 | HpT2].
    + assert (H2nB : qy E2 <> 0)
        by (intro h; exact (flag_excl_BT L l hd H2 E2 HE2l h HpT2)).
      assert (H2nL : qx E2 <> 0)
        by (intro h; exact (flag_excl_TL L l hd cd E2 HE2l HE2TL HpT2 h)).
      assert (H2nR : qx E2 + qs E2 <> L)
        by (intro h; exact (flag_excl_TR L l hd cd E2 HE2l HE2TR HpT2 h)).
      exact (opposite_bottom_top L l hd H2 HL cd E1 E2 HE1l HE2l
        HE1BL HE1BR HE2TL HE2TR HpB1 HpT2 (Hbot31 H2nB) (Htop32 H1nT)
        (Hleftc H1nL H2nL) (Hrightc H1nR H2nR)).
    + destruct (Req_dec (qx E2) 0) as [HpL2 | HpL2].
      * assert (H2nR : qx E2 + qs E2 <> L)
          by (intro h; exact (flag_excl_LR L l hd H2 E2 HE2l HpL2 h)).
        exact (clean_top_right L l hd H2 HL Hnc cd (Htopc H1nT HpT2)
          (Hrightc H1nR H2nR)).
      * exact (clean_top_left L l hd H2 HL Hnc cd (Htopc H1nT HpT2)
          (Hleftc H1nL HpL2)).
  - destruct (Req_dec (qy E1 + qs E1) L) as [HpT1 | HpT1].
    + assert (H1nL : qx E1 <> 0)
        by (intro h; exact (flag_excl_TL L l hd cd E1 HE1l HE1TL HpT1 h)).
      assert (H1nR : qx E1 + qs E1 <> L)
        by (intro h; exact (flag_excl_TR L l hd cd E1 HE1l HE1TR HpT1 h)).
      destruct (Req_dec (qy E2) 0) as [HpB2 | HpB2].
      * assert (H2nT : qy E2 + qs E2 <> L)
          by (intro h; exact (flag_excl_BT L l hd H2 E2 HE2l HpB2 h)).
        assert (H2nL : qx E2 <> 0)
          by (intro h; exact (flag_excl_BL L l hd cd E2 HE2l HE2BL HpB2 h)).
        assert (H2nR : qx E2 + qs E2 <> L)
          by (intro h; exact (flag_excl_BR L l hd cd E2 HE2l HE2BR HpB2 h)).
        exact (opposite_bottom_top L l hd H2 HL cd E2 E1 HE2l HE1l
          HE2BL HE2BR HE1TL HE1TR HpB2 HpT1 (Hbot32 HpB1) (Htop31 H2nT)
          (Hleftc H1nL H2nL) (Hrightc H1nR H2nR)).
      * destruct (Req_dec (qx E2) 0) as [HpL2 | HpL2].
        -- assert (H2nR : qx E2 + qs E2 <> L)
             by (intro h; exact (flag_excl_LR L l hd H2 E2 HE2l HpL2 h)).
           exact (clean_bottom_right L l hd H2 HL Hnc cd
             (Hbotc HpB1 HpB2) (Hrightc H1nR H2nR)).
        -- exact (clean_bottom_left L l hd H2 HL Hnc cd
             (Hbotc HpB1 HpB2) (Hleftc H1nL HpL2)).
    + destruct (Req_dec (qx E1) 0) as [HpL1 | HpL1].
      * assert (H1nR : qx E1 + qs E1 <> L)
          by (intro h; exact (flag_excl_LR L l hd H2 E1 HE1l HpL1 h)).
        destruct (Req_dec (qx E2 + qs E2) L) as [HpR2 | HpR2].
        -- assert (H2nB : qy E2 <> 0)
             by (intro h;
                 exact (flag_excl_BR L l hd cd E2 HE2l HE2BR h HpR2)).
           assert (H2nT : qy E2 + qs E2 <> L)
             by (intro h;
                 exact (flag_excl_TR L l hd cd E2 HE2l HE2TR h HpR2)).
           assert (H2nL : qx E2 <> 0)
             by (intro h; exact (flag_excl_LR L l hd H2 E2 HE2l h HpR2)).
           exact (opposite_left_right L l hd H2 HL cd E1 E2 HE1l HE2l
             HE1BL HE1TL HE2BR HE2TR HpL1 HpR2 (Hbotc HpB1 H2nB)
             (Htopc HpT1 H2nT) (Hleft31 H2nL) (Hright32 H1nR)).
        -- destruct (Req_dec (qy E2) 0) as [HpB2 | HpB2].
           ++ assert (H2nT : qy E2 + qs E2 <> L)
                by (intro h; exact (flag_excl_BT L l hd H2 E2 HE2l HpB2 h)).
              exact (clean_top_right L l hd H2 HL Hnc cd
                (Htopc HpT1 H2nT) (Hrightc H1nR HpR2)).
           ++ exact (clean_bottom_right L l hd H2 HL Hnc cd
                (Hbotc HpB1 HpB2) (Hrightc H1nR HpR2)).
      * destruct (Req_dec (qx E1 + qs E1) L) as [HpR1 | HpR1].
        -- destruct (Req_dec (qx E2) 0) as [HpL2 | HpL2].
           ++ assert (H2nR : qx E2 + qs E2 <> L)
                by (intro h; exact (flag_excl_LR L l hd H2 E2 HE2l HpL2 h)).
              assert (H2nB : qy E2 <> 0)
                by (intro h;
                    exact (flag_excl_BL L l hd cd E2 HE2l HE2BL h HpL2)).
              assert (H2nT : qy E2 + qs E2 <> L)
                by (intro h;
                    exact (flag_excl_TL L l hd cd E2 HE2l HE2TL h HpL2)).
              assert (H1nB : qy E1 <> 0)
                by (intro h;
                    exact (flag_excl_BR L l hd cd E1 HE1l HE1BR h HpR1)).
              assert (H1nT : qy E1 + qs E1 <> L)
                by (intro h;
                    exact (flag_excl_TR L l hd cd E1 HE1l HE1TR h HpR1)).
              exact (opposite_left_right L l hd H2 HL cd E2 E1 HE2l HE1l
                HE2BL HE2TL HE1BR HE1TR HpL2 HpR1 (Hbotc H1nB H2nB)
                (Htopc H1nT H2nT) (Hleft32 HpL1) (Hright31 H2nR)).
           ++ destruct (Req_dec (qy E2) 0) as [HpB2 | HpB2].
              ** assert (H2nT : qy E2 + qs E2 <> L)
                   by (intro h;
                       exact (flag_excl_BT L l hd H2 E2 HE2l HpB2 h)).
                 assert (H2nL : qx E2 <> 0)
                   by (intro h;
                       exact (flag_excl_BL L l hd cd E2 HE2l HE2BL HpB2 h)).
                 exact (clean_top_left L l hd H2 HL Hnc cd
                   (Htopc HpT1 H2nT) (Hleftc HpL1 H2nL)).
              ** destruct (Req_dec (qy E2 + qs E2) L) as [HpT2 | HpT2].
                 --- assert (H2nL : qx E2 <> 0)
                       by (intro h;
                           exact (flag_excl_TL L l hd cd E2 HE2l
                             HE2TL HpT2 h)).
                     exact (clean_bottom_left L l hd H2 HL Hnc cd
                       (Hbotc HpB1 HpB2) (Hleftc HpL1 H2nL)).
                 --- exact (clean_bottom_left L l hd H2 HL Hnc cd
                       (Hbotc HpB1 HpB2) (Hleftc HpL1 HpL2)).
        -- destruct (Req_dec (qy E2) 0) as [HpB2 | HpB2].
           ++ assert (H2nT : qy E2 + qs E2 <> L)
                by (intro h; exact (flag_excl_BT L l hd H2 E2 HE2l HpB2 h)).
              assert (H2nL : qx E2 <> 0)
                by (intro h;
                    exact (flag_excl_BL L l hd cd E2 HE2l HE2BL HpB2 h)).
              exact (clean_top_left L l hd H2 HL Hnc cd
                (Htopc HpT1 H2nT) (Hleftc HpL1 H2nL)).
           ++ destruct (Req_dec (qy E2 + qs E2) L) as [HpT2 | HpT2].
              ** assert (H2nL : qx E2 <> 0)
                   by (intro h;
                       exact (flag_excl_TL L l hd cd E2 HE2l HE2TL HpT2 h)).
                 exact (clean_bottom_left L l hd H2 HL Hnc cd
                   (Hbotc HpB1 HpB2) (Hleftc HpL1 H2nL)).
              ** destruct (Req_dec (qx E2) 0) as [HpL2 | HpL2].
                 --- assert (H2nR : qx E2 + qs E2 <> L)
                       by (intro h;
                           exact (flag_excl_LR L l hd H2 E2 HE2l HpL2 h)).
                     exact (clean_bottom_right L l hd H2 HL Hnc cd
                       (Hbotc HpB1 HpB2) (Hrightc HpR1 H2nR)).
                 --- exact (clean_bottom_left L l hd H2 HL Hnc cd
                       (Hbotc HpB1 HpB2) (Hleftc HpL1 HpL2)).
Qed.

(* A perfect squared square has at least 7 pieces.  Together with
   Duijvestijn's dissection this brackets the minimum order in [7, 21];
   the sharp bound 21 rests on Duijvestijn's exhaustive search of the
   orders 7..20, which is not formalized here. *)
Theorem seven_le_length : forall L l, IsPerfectSquaredSquare L l ->
  (7 <= length l)%nat.
Proof.
  intros L l Hp.
  pose proof (four_le_length L l Hp).
  pose proof (length_ne_four L l Hp).
  pose proof (length_ne_five L l Hp).
  pose proof (length_ne_six L l Hp).
  lia.
Qed.

End SquaredSquare.
End LeanProofs.
