(**
  Finitary monotone fixed points through executable HFS approximations.

  The source constructs a least fixed point of a monotone operator by finite
  HFS stages.  We retain that representation exactly in the standard model:
  every stage is an [N] bitset.  The operator itself is proposition-valued,
  so it can also be applied to the generally infinite union of all stages;
  only its action on a finite HFS input must come with a Boolean decision
  procedure.  This cleanly separates mathematical monotonicity from the
  executable comprehension used to build one stage.

  Parameters are bundled in an arbitrary type rather than a fixed finite
  vector.  Finiteness is expressed by an explicit finite support, the weakest
  data needed by the fixed-point proof and a constructive strengthening of
  the source's classically Skolemized bounded support.
*)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat Bool.Bool Lia
  Lists.List Logic.ClassicalDescription NArith.NArith.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.

Record hfs_fp_construction (P : Type) : Type := {
  hfs_fp_holds : P -> (hfs_code -> Prop) -> hfs_code -> Prop;
  hfs_fp_decide : P -> hfs_code -> hfs_code -> bool;
  hfs_fp_decide_spec : forall p finite_set x,
    hfs_fp_decide p finite_set x = true <->
    hfs_fp_holds p (fun z => hfs_mem z finite_set) x;
  hfs_fp_monotone : forall p C D,
    (forall z, C z -> D z) ->
    forall x, hfs_fp_holds p C x -> hfs_fp_holds p D x
}.

Arguments hfs_fp_holds {P} _ _ _ _.
Arguments hfs_fp_decide {P} _ _ _ _.

Definition hfs_fp_finite {P} (c : hfs_fp_construction P) : Prop :=
  forall p C x,
    hfs_fp_holds c p C x ->
    exists support : list hfs_code,
      (forall z, In z support -> C z) /\
      hfs_fp_holds c p (fun z => In z support) x.

Definition hfs_fp_strong_finite {P} (c : hfs_fp_construction P) : Prop :=
  forall p C x,
    hfs_fp_holds c p C x ->
    hfs_fp_holds c p
      (fun z => C z /\ N.to_nat z < N.to_nat x) x.

(** * Finite HFS comprehension *)

Fixpoint hfs_collect_below (count : nat) (test : hfs_code -> bool)
    : hfs_code :=
  match count with
  | 0 => hfs_empty
  | S k =>
      if test (N.of_nat k)
      then hfs_insert (N.of_nat k) (hfs_collect_below k test)
      else hfs_collect_below k test
  end.

Theorem hfs_mem_collect_below_iff : forall count test x,
  hfs_mem x (hfs_collect_below count test) <->
  N.to_nat x < count /\ test x = true.
Proof.
  induction count as [|count IH]; intros test x; simpl.
  - rewrite hfs_mem_empty_iff. lia.
  - destruct (test (N.of_nat count)) eqn:Hlast.
    + rewrite hfs_mem_insert_iff, IH. split.
      * intros [Hx | [Hlt Htest]].
        -- subst x. rewrite Nat2N.id. split; [lia|exact Hlast].
        -- now split; [lia|].
      * intros [Hlt Htest].
        destruct (Nat.eq_dec (N.to_nat x) count) as [Heq | Hneq].
        -- left. apply N2Nat.inj. now rewrite Nat2N.id.
        -- right. split; [lia|exact Htest].
    + rewrite IH. split.
      * intros [Hlt Htest]. now split; [lia|].
      * intros [Hlt Htest]. split; [|exact Htest].
        assert (Hneq : N.to_nat x <> count).
        { intro Heq. assert (Hx : x = N.of_nat count).
          { apply N2Nat.inj. now rewrite Nat2N.id. }
          subst x. rewrite Hlast in Htest. discriminate. }
        lia.
Qed.

Definition hfs_restrict_below (bound : nat) (s : hfs_code) : hfs_code :=
  N.land s (N.ones (N.of_nat bound)).

Lemma hfs_mem_restrict_below_iff : forall bound s x,
  hfs_mem x (hfs_restrict_below bound s) <->
  hfs_mem x s /\ N.to_nat x < bound.
Proof.
  intros bound s x. unfold hfs_mem, hfs_restrict_below.
  rewrite N.land_spec, Bool.andb_true_iff, N.ones_spec_iff.
  unfold N.lt. rewrite N2Nat.inj_compare, Nat2N.id,
    Nat.compare_lt_iff. reflexivity.
Qed.

Definition hfs_prefix_codes (bound : nat) : list hfs_code :=
  map N.of_nat (seq 0 bound).

Lemma hfs_in_prefix_codes_iff : forall bound x,
  In x (hfs_prefix_codes bound) <-> N.to_nat x < bound.
Proof.
  intros bound x. unfold hfs_prefix_codes. rewrite in_map_iff. split.
  - intros [k [<- Hk]]. apply in_seq in Hk. rewrite Nat2N.id. lia.
  - intro Hx. exists (N.to_nat x). split.
    + apply N2Nat.id.
    + apply in_seq. lia.
Qed.

Lemma hfs_fp_strong_finite_implies_finite : forall P
    (c : hfs_fp_construction P),
  hfs_fp_strong_finite c -> hfs_fp_finite c.
Proof.
  intros P c Hstrong p C x Hx.
  pose (decide_C := fun z : hfs_code =>
    if excluded_middle_informative (C z) then true else false).
  exists (filter decide_C (hfs_prefix_codes (N.to_nat x))). split.
  - intros z Hz. apply filter_In in Hz. destruct Hz as [_ HzC].
    unfold decide_C in HzC.
    destruct (excluded_middle_informative (C z)) as [HC | HNC];
      [exact HC|discriminate].
  - eapply (@hfs_fp_monotone P c p
      (fun z => C z /\ N.to_nat z < N.to_nat x)
      (fun z => In z
        (filter decide_C (hfs_prefix_codes (N.to_nat x))))).
    + intros z [HzC Hzlt]. apply filter_In. split.
      * now apply hfs_in_prefix_codes_iff.
      * unfold decide_C.
        destruct (excluded_middle_informative (C z)) as [HC | HNC];
          [reflexivity|contradiction].
    + now apply Hstrong.
Qed.

(** * Executable approximation stages *)

Definition hfs_fp_successor {P} (c : hfs_fp_construction P) (p : P)
    (bound : nat) (previous : hfs_code) : hfs_code :=
  hfs_collect_below (S bound) (hfs_fp_decide c p previous).

Fixpoint hfs_fp_stage {P} (c : hfs_fp_construction P) (p : P)
    (n : nat) : hfs_code :=
  match n with
  | 0 => hfs_empty
  | S k => hfs_fp_successor c p k (hfs_fp_stage c p k)
  end.

Lemma hfs_fp_stage_zero : forall P (c : hfs_fp_construction P) p,
  hfs_fp_stage c p 0 = hfs_empty.
Proof. reflexivity. Qed.

Lemma hfs_fp_stage_succ : forall P (c : hfs_fp_construction P) p n,
  hfs_fp_stage c p (S n) =
  hfs_fp_successor c p n (hfs_fp_stage c p n).
Proof. reflexivity. Qed.

Theorem hfs_fp_mem_successor_iff : forall P
    (c : hfs_fp_construction P) p bound previous x,
  hfs_mem x (hfs_fp_successor c p bound previous) <->
  N.to_nat x <= bound /\
  hfs_fp_holds c p (fun z => hfs_mem z previous) x.
Proof.
  intros P c p bound previous x. unfold hfs_fp_successor.
  rewrite hfs_mem_collect_below_iff, hfs_fp_decide_spec. split.
  - intros [Hlt Hphi]. split; [lia|exact Hphi].
  - intros [Hle Hphi]. split; [lia|exact Hphi].
Qed.

Corollary hfs_fp_mem_stage_succ_iff : forall P
    (c : hfs_fp_construction P) p n x,
  hfs_mem x (hfs_fp_stage c p (S n)) <->
  N.to_nat x <= n /\
  hfs_fp_holds c p (fun z => hfs_mem z (hfs_fp_stage c p n)) x.
Proof. intros. apply hfs_fp_mem_successor_iff. Qed.

Theorem hfs_fp_stage_cumulative : forall P
    (c : hfs_fp_construction P) p n m,
  n <= m -> hfs_subset (hfs_fp_stage c p n) (hfs_fp_stage c p m).
Proof.
  intros P c p n m. revert n.
  induction m as [|m IH]; intros [|n] Hnm x Hx.
  - exact Hx.
  - lia.
  - exfalso. exact (hfs_not_mem_empty Hx).
  - apply hfs_fp_mem_stage_succ_iff in Hx.
    destruct Hx as [Hxbound Hxphi].
    apply hfs_fp_mem_stage_succ_iff. split; [lia|].
    eapply hfs_fp_monotone.
    + intros z Hz. apply (IH n); [lia|exact Hz].
    + exact Hxphi.
Qed.

Definition hfs_fp_fixedpoint {P} (c : hfs_fp_construction P)
    (p : P) (x : hfs_code) : Prop :=
  exists n, hfs_mem x (hfs_fp_stage c p n).

Lemma hfs_fp_fixedpoint_of_stage : forall P
    (c : hfs_fp_construction P) p n x,
  hfs_mem x (hfs_fp_stage c p n) -> hfs_fp_fixedpoint c p x.
Proof. intros. now exists n. Qed.

Lemma hfs_fp_unfold : forall P (c : hfs_fp_construction P) p x,
  hfs_fp_fixedpoint c p x ->
  hfs_fp_holds c p (hfs_fp_fixedpoint c p) x.
Proof.
  intros P c p x [n Hn]. destruct n as [|n].
  { now apply hfs_not_mem_empty in Hn. }
  apply hfs_fp_mem_stage_succ_iff in Hn. destruct Hn as [_ Hphi].
  eapply (@hfs_fp_monotone P c p
    (fun z => hfs_mem z (hfs_fp_stage c p n))
    (hfs_fp_fixedpoint c p)).
  - intros z Hz. now exists n.
  - exact Hphi.
Qed.

Lemma hfs_fp_stage_subset_fixedpoint : forall P
    (c : hfs_fp_construction P) p n x,
  hfs_mem x (hfs_fp_stage c p n) -> hfs_fp_fixedpoint c p x.
Proof. intros. now exists n. Qed.

(** Strong finiteness makes an element appear by its own successor stage. *)
Theorem hfs_fp_mem_stage_self : forall P
    (c : hfs_fp_construction P),
  hfs_fp_strong_finite c ->
  forall p x n,
    hfs_mem x (hfs_fp_stage c p n) ->
    hfs_mem x (hfs_fp_stage c p (S (N.to_nat x))).
Proof.
  intros P c Hstrong p x.
  remember (N.to_nat x) as rank eqn:Hrank.
  revert x Hrank.
  induction rank using lt_wf_ind; intros x Hrank n Hmem.
  destruct n as [|n].
  { now apply hfs_not_mem_empty in Hmem. }
  apply hfs_fp_mem_stage_succ_iff in Hmem.
  destruct Hmem as [_ Hphi].
  apply hfs_fp_mem_stage_succ_iff. rewrite Hrank. split; [lia|].
  apply Hstrong in Hphi.
  eapply (@hfs_fp_monotone P c p
    (fun z => hfs_mem z (hfs_fp_stage c p n) /\
      N.to_nat z < N.to_nat x)
    (fun z => hfs_mem z (hfs_fp_stage c p (N.to_nat x)))).
  - intros z [Hzstage Hzrank].
    assert (Hzself : hfs_mem z
        (hfs_fp_stage c p (S (N.to_nat z)))).
    { assert (Hzrank' : N.to_nat z < rank) by now rewrite Hrank.
      exact (H (N.to_nat z) Hzrank' z eq_refl n Hzstage). }
    eapply hfs_fp_stage_cumulative; [|exact Hzself]. lia.
  - exact Hphi.
Qed.

Corollary hfs_fp_fixedpoint_iff_self_stage : forall P
    (c : hfs_fp_construction P),
  hfs_fp_strong_finite c ->
  forall p x,
    hfs_fp_fixedpoint c p x <->
    hfs_mem x (hfs_fp_stage c p (S (N.to_nat x))).
Proof.
  intros P c Hstrong p x. split.
  - intros [n Hn]. now apply (hfs_fp_mem_stage_self Hstrong Hn).
  - intro H. now exists (S (N.to_nat x)).
Qed.

(** A finite family of fixed-point elements is contained in one common
    stage.  This is the standard-model replacement for the source's
    Sigma-one Skolem map and its arithmetized maximum bound. *)
Lemma hfs_fp_finite_upper_stage : forall P
    (c : hfs_fp_construction P) p support,
  (forall z, In z support -> hfs_fp_fixedpoint c p z) ->
  exists n, forall z, In z support -> hfs_mem z (hfs_fp_stage c p n).
Proof.
  intros P c p support. induction support as [|x xs IH]; intro Hsupport.
  - exists 0. intros z Hz. inversion Hz.
  - destruct (Hsupport x (or_introl eq_refl)) as [nx Hx].
    destruct IH as [nxs Hxs].
    { intros z Hz. apply Hsupport. now right. }
    exists (Nat.max nx nxs). intros z [Hz | Hz].
    + subst z. eapply hfs_fp_stage_cumulative; [apply Nat.le_max_l|exact Hx].
    + eapply hfs_fp_stage_cumulative; [apply Nat.le_max_r|now apply Hxs].
Qed.

(** The union of all stages is exactly a fixed point for every finitary
    monotone operator. *)
Theorem hfs_fp_case : forall P (c : hfs_fp_construction P),
  hfs_fp_finite c ->
  forall p x,
    hfs_fp_fixedpoint c p x <->
    hfs_fp_holds c p (hfs_fp_fixedpoint c p) x.
Proof.
  intros P c Hfinite p x. split.
  - apply hfs_fp_unfold.
  - intro Hphi.
    destruct (Hfinite p _ x Hphi) as [support [Hmembers Hsupport]].
    destruct (@hfs_fp_finite_upper_stage P c p support Hmembers)
      as [stage Hstage].
    assert (Hstage_phi : hfs_fp_holds c p
        (fun z => hfs_mem z (hfs_fp_stage c p stage)) x).
    { eapply (@hfs_fp_monotone P c p
        (fun z => In z support)
        (fun z => hfs_mem z (hfs_fp_stage c p stage))).
      - intros z Hzsupport. now apply Hstage.
      - exact Hsupport. }
    exists (S (Nat.max stage (N.to_nat x))).
    apply hfs_fp_mem_stage_succ_iff. split; [apply Nat.le_max_r|].
    eapply (@hfs_fp_monotone P c p
      (fun z => hfs_mem z (hfs_fp_stage c p stage))
      (fun z => hfs_mem z
        (hfs_fp_stage c p (Nat.max stage (N.to_nat x))))).
    + intros z Hz. eapply hfs_fp_stage_cumulative;
        [apply Nat.le_max_l|exact Hz].
    + exact Hstage_phi.
Qed.

(** Least-fixed-point induction.  The closure hypothesis is stated for an
    arbitrary dependency predicate, matching the source while avoiding any
    need for predicate extensionality. *)
Theorem hfs_fp_induction : forall P (c : hfs_fp_construction P),
  hfs_fp_strong_finite c ->
  forall p (Q : hfs_code -> Prop),
  (forall C,
    (forall z, C z -> hfs_fp_fixedpoint c p z /\ Q z) ->
    forall x, hfs_fp_holds c p C x -> Q x) ->
  forall x, hfs_fp_fixedpoint c p x -> Q x.
Proof.
  intros P c Hstrong p Q Hclosure x Hfixed.
  remember (N.to_nat x) as rank eqn:Hrank.
  revert x Hrank Hfixed.
  induction rank using lt_wf_ind; intros x Hrank Hfixed.
  pose proof (@hfs_fp_unfold P c p x Hfixed) as Hphi.
  apply Hstrong in Hphi.
  eapply (Hclosure
    (fun z => hfs_fp_fixedpoint c p z /\ N.to_nat z < N.to_nat x)).
  - intros z [Hzfixed Hzlt]. split; [exact Hzfixed|].
    apply (H (N.to_nat z)); [lia|reflexivity|exact Hzfixed].
  - exact Hphi.
Qed.
