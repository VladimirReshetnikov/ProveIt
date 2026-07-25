(*
  Interval partitions of a segment.

  Coq port of the Lean module SquaredSquare.Intervals: if finitely many
  closed intervals [x, x + s] with positive lengths, pairwise disjoint
  interiors and endpoints inside [lo, hi] cover every point of (lo, hi],
  then their lengths sum to hi - lo.

  Intervals are recorded as pairs (x, s) of position and length; interior
  disjointness enters through the separation predicate sep1.
*)

From Stdlib Require Import Reals.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Psatz.
Import ListNotations.

Open Scope R_scope.

Module LeanProofs.
Module SquaredSquare.

Definition sep1 (p q : R * R) : Prop :=
  fst p + snd p <= fst q \/ fst q + snd q <= fst p.

Definition rsum (L : list R) : R := fold_right Rplus 0 L.

Lemma rsum_app : forall L1 L2, rsum (L1 ++ L2) = rsum L1 + rsum L2.
Proof.
  induction L1 as [|x t IH]; intros L2; simpl.
  - lra.
  - rewrite IH; lra.
Qed.

Lemma fold_min_gt : forall (L : list R) (a c : R),
  c < a -> (forall x, In x L -> c < x) -> c < fold_right Rmin a L.
Proof.
  induction L as [|x t IH]; simpl; intros a c Ha Hx.
  - exact Ha.
  - apply Rmin_glb_lt.
    + apply Hx; auto.
    + apply IH; auto.
Qed.

Lemma fold_min_le_mem : forall (L : list R) (a x : R),
  In x L -> fold_right Rmin a L <= x.
Proof.
  induction L as [|y t IH]; simpl; intros a x Hx.
  - contradiction.
  - destruct Hx as [-> | Hx].
    + apply Rmin_l.
    + eapply Rle_trans; [apply Rmin_r | apply IH, Hx].
Qed.

Lemma fold_min_le_init : forall (L : list R) (a : R),
  fold_right Rmin a L <= a.
Proof.
  induction L as [|y t IH]; simpl; intros a.
  - lra.
  - eapply Rle_trans; [apply Rmin_r | apply IH].
Qed.

(* Decomposition and recomposition of ForallOrdPairs across an append. *)

Lemma FOP_cons_inv {A : Type} (R : A -> A -> Prop) (x : A) (l : list A) :
  ForallOrdPairs R (x :: l) -> Forall (R x) l /\ ForallOrdPairs R l.
Proof.
  intros H; inversion H; subst; auto.
Qed.

Lemma FOP_app_inv {A : Type} (R : A -> A -> Prop) (l1 l2 : list A) :
  ForallOrdPairs R (l1 ++ l2) ->
  ForallOrdPairs R l1 /\ ForallOrdPairs R l2 /\
  (forall a b, In a l1 -> In b l2 -> R a b).
Proof.
  induction l1 as [|x t IH]; simpl; intros H.
  - repeat split; auto.
    + constructor.
    + intros a b [].
  - inversion H as [|? ? Hf Ht]; subst.
    destruct (IH Ht) as [H1 [H2 H3]].
    rewrite Forall_forall in Hf.
    repeat split.
    + constructor; [| exact H1].
      rewrite Forall_forall; intros b Hb.
      apply Hf, in_or_app; auto.
    + exact H2.
    + intros a b Ha Hb.
      destruct Ha as [-> | Ha].
      * apply Hf, in_or_app; auto.
      * apply H3; auto.
Qed.

Lemma FOP_app {A : Type} (R : A -> A -> Prop) (l1 l2 : list A) :
  ForallOrdPairs R l1 -> ForallOrdPairs R l2 ->
  (forall a b, In a l1 -> In b l2 -> R a b) ->
  ForallOrdPairs R (l1 ++ l2).
Proof.
  induction l1 as [|x t IH]; simpl; intros H1 H2 H3.
  - exact H2.
  - inversion H1 as [|? ? Hf Ht]; subst.
    constructor.
    + rewrite Forall_app; split; [assumption |].
      rewrite Forall_forall; intros b Hb.
      apply H3; auto.
    + apply IH; [exact Ht | exact H2 |].
      intros a b Ha Hb; apply H3; auto.
Qed.

(* The interval partition sum lemma. *)

Lemma interval_cover_sum : forall (n : nat) (B : list (R * R)) (lo hi : R),
  length B = n -> lo <= hi ->
  (forall p, In p B -> 0 < snd p) ->
  (forall p, In p B -> lo <= fst p /\ fst p + snd p <= hi) ->
  ForallOrdPairs sep1 B ->
  (forall x, lo < x -> x <= hi ->
     exists p, In p B /\ fst p <= x <= fst p + snd p) ->
  rsum (map snd B) = hi - lo.
Proof.
  induction n as [|n IH]; intros B lo hi Hlen Hle Hpos Hbnd Hsep Hcov.
  - apply length_zero_iff_nil in Hlen; subst B.
    destruct (Rle_lt_or_eq_dec lo hi Hle) as [Hlt | Heq].
    + exfalso.
      destruct (Hcov hi Hlt (Rle_refl hi)) as [p [[] _]].
    + simpl; lra.
  - destruct B as [|p0 B0]; [discriminate |].
    assert (Hlolt : lo < hi).
    { destruct (Hbnd p0 (in_eq _ _)) as [Hb1 Hb2].
      pose proof (Hpos p0 (in_eq _ _)).
      lra. }
    set (keep := fun r : R * R =>
      if Rlt_dec lo (fst r) then true else false).
    set (mu := fold_right Rmin hi (map fst (filter keep (p0 :: B0)))).
    assert (Hmugt : lo < mu).
    { apply fold_min_gt; [exact Hlolt |].
      intros x Hx.
      apply in_map_iff in Hx; destruct Hx as [r [Hr1 Hr2]].
      apply filter_In in Hr2; destruct Hr2 as [_ Hr2].
      unfold keep in Hr2.
      destruct (Rlt_dec lo (fst r)); [subst x; assumption | discriminate]. }
    assert (Hmule : forall r, In r (p0 :: B0) -> lo < fst r -> mu <= fst r).
    { intros r Hr Hlt.
      apply fold_min_le_mem, in_map, filter_In.
      split; [exact Hr |].
      unfold keep; destruct (Rlt_dec lo (fst r)); [reflexivity | lra]. }
    assert (Hmuhi : mu <= hi) by apply fold_min_le_init.
    set (m := (lo + mu) / 2).
    assert (Hm1 : lo < m) by (unfold m; lra).
    assert (Hm2 : m <= hi) by (unfold m; lra).
    destruct (Hcov m Hm1 Hm2) as [q [Hq [Hq1 Hq2]]].
    assert (Hqlo : fst q = lo).
    { destruct (Rlt_dec lo (fst q)) as [Hlt | Hnlt].
      - exfalso.
        pose proof (Hmule q Hq Hlt).
        unfold m in Hq1; lra.
      - destruct (Hbnd q Hq); lra. }
    destruct (in_split q (p0 :: B0) Hq) as [l1 [l2 HB]].
    rewrite HB in *.
    destruct (FOP_app_inv sep1 l1 (q :: l2) Hsep) as [Hs1 [Hs2' Hcross]].
    destruct (FOP_cons_inv sep1 q l2 Hs2') as [HqfF Hs2].
    assert (Hqf : forall r, In r l2 -> sep1 q r).
    { rewrite Forall_forall in HqfF; exact HqfF. }
    assert (Hmem : forall r, In r (l1 ++ l2) -> In r (l1 ++ q :: l2)).
    { intros r Hr.
      apply in_app_or in Hr; apply in_or_app.
      destruct Hr; [auto | right; right; assumption]. }
    assert (Hqpos := Hpos q (in_or_app _ _ _ (or_intror (in_eq _ _)))).
    assert (Hqbnd := Hbnd q (in_or_app _ _ _ (or_intror (in_eq _ _)))).
    assert (Hafter : forall r, In r (l1 ++ l2) -> lo + snd q <= fst r).
    { intros r Hr.
      assert (Hrpos := Hpos r (Hmem r Hr)).
      assert (Hrbnd := Hbnd r (Hmem r Hr)).
      apply in_app_or in Hr; destruct Hr as [Hr | Hr].
      - destruct (Hcross r q Hr (in_eq _ _)) as [Hs | Hs];
          rewrite Hqlo in Hs; lra.
      - destruct (Hqf r Hr) as [Hs | Hs];
          rewrite Hqlo in Hs; lra. }
    assert (Hlen' : length (l1 ++ l2) = n).
    { rewrite length_app in Hlen |- *.
      simpl in Hlen; lia. }
    assert (Hsum' : rsum (map snd (l1 ++ l2)) = hi - (lo + snd q)).
    { apply (IH (l1 ++ l2) (lo + snd q) hi Hlen').
      - lra.
      - intros p Hp; apply Hpos, Hmem, Hp.
      - intros p Hp.
        split; [apply Hafter, Hp | apply (Hbnd p (Hmem p Hp))].
      - apply FOP_app; [exact Hs1 | exact Hs2 |].
        intros a b Ha Hb.
        apply (Hcross a b Ha (in_cons _ _ _ Hb)).
      - intros x Hx1 Hx2.
        destruct (Hcov x ltac:(lra) Hx2) as [r [Hr [Hr1 Hr2]]].
        apply in_app_or in Hr; destruct Hr as [Hr | Hr].
        + exists r; repeat split; auto using in_or_app.
        + destruct Hr as [-> | Hr].
          * exfalso; rewrite Hqlo in Hr2; lra.
          * exists r; repeat split; auto.
            apply in_or_app; auto. }
    rewrite map_app in *.
    rewrite rsum_app in *.
    simpl.
    lra.
Qed.

Lemma interval_cover_sum' : forall (B : list (R * R)) (lo hi : R),
  lo <= hi ->
  (forall p, In p B -> 0 < snd p) ->
  (forall p, In p B -> lo <= fst p /\ fst p + snd p <= hi) ->
  ForallOrdPairs sep1 B ->
  (forall x, lo < x -> x <= hi ->
     exists p, In p B /\ fst p <= x <= fst p + snd p) ->
  rsum (map snd B) = hi - lo.
Proof.
  intros B lo hi; apply (interval_cover_sum (length B)); reflexivity.
Qed.

End SquaredSquare.
End LeanProofs.
