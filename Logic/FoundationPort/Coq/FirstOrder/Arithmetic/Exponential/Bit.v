(** Executable finite-bitset arithmetic in the standard natural model.

    Foundation defines membership by the binary digit selected by [2^i]
    inside arbitrary models of arithmetic.  On standard naturals this is
    exactly [N.testbit], already used by the audited hereditary-finite-set
    layer.  Reusing that representation exposes the mathematical bitset
    algebra directly and keeps every operation executable.

    Internal Delta-zero formulas, their nonstandard-model absoluteness, and
    bounded-comprehension principles remain outside this module.  No formula
    graph or model-theoretic adapter is assumed here. *)

From Stdlib Require Import Bool.Bool Lia NArith.NArith
  Numbers.Natural.Abstract.NBits.
From Foundation.FirstOrder.Arithmetic.HFS Require Import Basic.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.

Definition nat_bit (i a : N) : Prop := hfs_mem i a.
Definition nat_bit_empty : N := hfs_empty.
Definition nat_bit_singleton (i : N) : N := hfs_singleton i.
Definition nat_bit_insert (i a : N) : N := hfs_insert i a.
Definition nat_bit_remove (i a : N) : N := hfs_remove i a.
Definition nat_bit_subset (a b : N) : Prop := hfs_subset a b.

Lemma nat_bit_mem_iff : forall i a,
  nat_bit i a <-> N.testbit a i = true.
Proof. reflexivity. Qed.

(** The source [LenBit.iff_rem] normal form, specialized to binary N codes. *)
Lemma nat_bit_mem_iff_div_pow2_mod_two : forall i a,
  nat_bit i a <-> (a / 2 ^ i) mod 2 = 1.
Proof.
  intros i a. rewrite nat_bit_mem_iff. apply N.testbit_true.
Qed.

Lemma nat_bit_not_mem_iff_div_pow2_mod_two : forall i a,
  ~ nat_bit i a <-> (a / 2 ^ i) mod 2 = 0.
Proof.
  intros i a. unfold nat_bit, hfs_mem.
  destruct (N.testbit a i) eqn:Ht.
  - split.
    + intro H. exfalso. apply H. reflexivity.
    + intro H. pose proof (proj1 (N.testbit_true a i) Ht) as Hone. nia.
  - split.
    + intro Hdummy. apply (proj1 (N.testbit_false a i)); exact Ht.
    + intro Hzero. discriminate.
Qed.

(** A present bit contributes its full power of two to the code. *)
Lemma nat_bit_exp_le_of_mem : forall i a,
  nat_bit i a -> 2 ^ i <= a.
Proof.
  intros i a H. unfold nat_bit, hfs_mem in H.
  assert (Ha : a <> 0).
  { intro E. subst a. rewrite N.bits_0 in H. discriminate. }
  assert (Hi : i <= N.log2 a).
  { apply N.nlt_ge. intro Hlt.
    rewrite (N.bits_above_log2 a i Hlt) in H. discriminate. }
  eapply N.le_trans.
  - apply N.pow_le_mono_r; [discriminate | exact Hi].
  - exact (proj1 (N.log2_spec a
      (proj1 (N.neq_0_lt_0 a) Ha))).
Qed.

Lemma nat_bit_lt_of_mem : forall i a,
  nat_bit i a -> i < a.
Proof.
  intros i a H.
  eapply N.lt_le_trans with (m := 2 ^ i).
  - exact (N.pow_gt_lin_r 2 i eq_refl).
  - exact (@nat_bit_exp_le_of_mem i a H).
Qed.

Lemma nat_bit_not_mem_of_lt_exp : forall i a,
  a < 2 ^ i -> ~ nat_bit i a.
Proof.
  intros i a Hlt Hmem.
  exact (N.lt_irrefl (2 ^ i)
    (N.le_lt_trans _ _ _ (@nat_bit_exp_le_of_mem i a Hmem) Hlt)).
Qed.

(** The selected bit is exactly the middle bit in a low/high binary
    decomposition.  These are the standard-model counterparts of the two
    source [LenBit] decomposition lemmas. *)
Lemma nat_bit_mem_iff_mul_pow2_add : forall i a,
  nat_bit i a <->
  exists k r, r < 2 ^ i /\
    a = k * 2 ^ (i + 1) + 2 ^ i + r.
Proof.
  intros i a. split.
  - intro H.
    unfold nat_bit, hfs_mem in H.
    destruct (N.testbit_spec a i) as [l [h [Hl Heq]]].
    rewrite H in Heq.
    change (a = l + (1 + 2 * h) * 2 ^ i) in Heq.
    exists h, l. split; [exact (proj2 Hl)|].
    rewrite N.add_1_r, N.pow_succ_r'. nia.
  - intros [k [r [Hr Heq]]].
    unfold nat_bit, hfs_mem.
    apply (N.testbit_unique a i true r k).
    + exact Hr.
    + rewrite N.add_1_r in Heq.
      rewrite N.pow_succ_r' in Heq.
      change (a = r + (1 + 2 * k) * 2 ^ i).
      nia.
Qed.

Lemma nat_bit_not_mem_iff_mul_pow2_add : forall i a,
  ~ nat_bit i a <->
  exists k r, r < 2 ^ i /\
    a = k * 2 ^ (i + 1) + r.
Proof.
  intros i a. split.
  - intro H.
    unfold nat_bit, hfs_mem in H.
    destruct (N.testbit_spec a i) as [l [h [Hl Heq]]].
    assert (Hb : N.testbit a i = false).
    { destruct (N.testbit a i);
      [exfalso; apply H; reflexivity | reflexivity]. }
    rewrite Hb in Heq.
    change (a = l + (0 + 2 * h) * 2 ^ i) in Heq.
    exists h, l. split; [exact (proj2 Hl)|].
    rewrite N.add_1_r, N.pow_succ_r'. nia.
  - intros [k [r [Hr Heq]]] Hbit.
    unfold nat_bit, hfs_mem in Hbit.
    assert (Hfalse : N.testbit a i = false).
    { apply (N.testbit_unique a i false r k).
      - exact Hr.
      - rewrite N.add_1_r in Heq.
        rewrite N.pow_succ_r' in Heq.
        change (a = r + (0 + 2 * k) * 2 ^ i).
        nia. }
    rewrite Hfalse in Hbit. discriminate.
Qed.

Lemma nat_bit_empty_eq_zero : nat_bit_empty = 0.
Proof. reflexivity. Qed.

Lemma nat_bit_not_mem_empty : forall i,
  ~ nat_bit i nat_bit_empty.
Proof. exact hfs_not_mem_empty. Qed.

Lemma nat_bit_not_mem_zero : forall i,
  ~ nat_bit i 0.
Proof. exact hfs_not_mem_empty. Qed.

(** A singleton code is the corresponding power of two. *)
Lemma nat_bit_singleton_eq_pow : forall i,
  nat_bit_singleton i = 2 ^ i.
Proof.
  intro i. unfold nat_bit_singleton, hfs_singleton,
    hfs_insert, hfs_empty.
  rewrite N.setbit_spec', N.lor_0_l. reflexivity.
Qed.

Lemma nat_bit_singleton_injective : forall i j,
  nat_bit_singleton i = nat_bit_singleton j <-> i = j.
Proof.
  intros i j. rewrite !nat_bit_singleton_eq_pow. split.
  - apply N.pow_inj_r. exact eq_refl.
  - now intros ->.
Qed.

Lemma nat_bit_insert_eq : forall i a,
  nat_bit_insert i a = hfs_insert i a.
Proof. reflexivity. Qed.

Lemma nat_bit_remove_eq : forall i a,
  nat_bit_remove i a = hfs_remove i a.
Proof. reflexivity. Qed.

Lemma nat_bit_singleton_eq_insert_empty : forall i,
  nat_bit_singleton i = nat_bit_insert i nat_bit_empty.
Proof. reflexivity. Qed.

Lemma nat_bit_mem_insert_iff : forall i j a,
  nat_bit i (nat_bit_insert j a) <-> i = j \/ nat_bit i a.
Proof. exact hfs_mem_insert_iff. Qed.

Lemma nat_bit_mem_remove_iff : forall i j a,
  nat_bit i (nat_bit_remove j a) <-> i <> j /\ nat_bit i a.
Proof.
  intros i j a. rewrite hfs_mem_remove_iff. tauto.
Qed.

Lemma nat_bit_not_mem_remove_self : forall i a,
  ~ nat_bit i (nat_bit_remove i a).
Proof. exact hfs_not_mem_remove_self. Qed.

Lemma nat_bit_one_eq_singleton_empty :
  1 = nat_bit_singleton nat_bit_empty.
Proof. rewrite nat_bit_singleton_eq_pow. reflexivity. Qed.

Lemma nat_bit_mem_singleton_iff : forall i j,
  nat_bit i (nat_bit_singleton j) <-> i = j.
Proof. exact hfs_mem_singleton_iff. Qed.

Lemma nat_bit_remove_lt_of_mem : forall i a,
  nat_bit i a -> nat_bit_remove i a < a.
Proof.
  intros i a H. unfold nat_bit in H. unfold nat_bit_remove, hfs_remove.
  apply (proj2 (N.le_neq (N.clearbit a i) a)). split.
  - rewrite N.clearbit_spec'. apply N.ldiff_le_l.
  - intro E. pose proof (N.clearbit_eq a i) as Hclear.
    unfold hfs_mem in H. rewrite E, H in Hclear. discriminate.
Qed.

Lemma nat_bit_pos_of_nonempty : forall i a,
  nat_bit i a -> 0 < a.
Proof.
  intros i a H.
  exact (N.lt_le_trans _ _ _
    (proj1 (N.neq_0_lt_0 (2 ^ i))
      (N.pow_nonzero 2 i ltac:(discriminate)))
    (@nat_bit_exp_le_of_mem i a H)).
Qed.

Lemma nat_bit_mem_insert : forall i a,
  nat_bit i (nat_bit_insert i a).
Proof. exact hfs_mem_insert_self. Qed.

Lemma nat_bit_insert_eq_self_of_mem : forall i a,
  nat_bit i a -> nat_bit_insert i a = a.
Proof.
  intros i a Hi. apply hfs_extensionality. intro j.
  rewrite hfs_mem_insert_iff. split.
  - intros [-> | Hj]; assumption.
  - intro Hj. now right.
Qed.

(** An absent bit is disjoint from its corresponding singleton power. *)
Lemma nat_bit_absent_land_pow : forall i a,
  ~ nat_bit i a -> N.land a (2 ^ i) = 0.
Proof.
  intros i a H.
  assert (Ha : N.testbit a i = false).
  { destruct (N.testbit a i) eqn:Ht.
    - exfalso. apply H. apply (proj2 (nat_bit_mem_iff i a)). exact Ht.
    - reflexivity. }
  apply N.bits_inj_0. intro j.
  rewrite N.land_spec.
  destruct (N.eq_dec j i) as [-> | Hji].
  - rewrite Ha, N.pow2_bits_true. reflexivity.
  - assert (Hji' : i <> j).
    { intro E. apply Hji. symmetry. exact E. }
    rewrite (N.pow2_bits_false i j Hji').
    destruct (N.testbit a j); reflexivity.
Qed.

(** Inserting an absent bit is ordinary addition by its power of two. *)
Lemma nat_bit_insert_add_of_not_mem : forall i a,
  ~ nat_bit i a -> nat_bit_insert i a = a + 2 ^ i.
Proof.
  intros i a H.
  unfold nat_bit_insert, hfs_insert.
  rewrite N.setbit_spec'.
  pose proof (@nat_bit_absent_land_pow i a H) as Hland.
  pose proof (N.lxor_lor a (2 ^ i) Hland) as Hxor.
  pose proof (N.add_nocarry_lxor a (2 ^ i) Hland) as Hadd.
  rewrite <- Hxor. symmetry. exact Hadd.
Qed.

(** Foundation's insertion estimate, specialized to executable N codes. *)
Lemma nat_bit_insert_le_of_le_of_le : forall i j a b,
  i <= j -> a <= b -> nat_bit_insert i a <= b + 2 ^ j.
Proof.
  intros i j a b Hij Hab.
  destruct (N.testbit a i) eqn:Ht.
  - assert (Hmem : nat_bit i a).
    { apply (proj2 (nat_bit_mem_iff i a)); exact Ht. }
    rewrite nat_bit_insert_eq_self_of_mem by exact Hmem.
    eapply N.le_trans; [exact Hab|].
    apply N.le_add_r.
  - assert (Hnot : ~ nat_bit i a).
    { intro Hmem.
      rewrite (proj1 (nat_bit_mem_iff i a) Hmem) in Ht.
      discriminate. }
    rewrite (@nat_bit_insert_add_of_not_mem i a Hnot).
    apply N.add_le_mono.
    + exact Hab.
    + apply N.pow_le_mono_r; [discriminate | exact Hij].
Qed.

(** Adding a multiple of the full period [2^(i+1)] does not change bit [i]. *)
Lemma nat_bit_mem_add_period_iff : forall i a k,
  nat_bit i (a + k * 2 ^ (i + 1)) <-> nat_bit i a.
Proof.
  intros i a k.
  rewrite !nat_bit_mem_iff_div_pow2_mod_two.
  rewrite N.add_1_r, N.pow_succ_r'.
  replace (k * (2 * 2 ^ i)) with ((k * 2) * 2 ^ i) by nia.
  rewrite N.div_add by (apply N.pow_nonzero; discriminate).
  rewrite N.mod_add by discriminate.
  reflexivity.
Qed.

Lemma nat_bit_subset_iff : forall a b,
  nat_bit_subset a b <-> forall i, nat_bit i a -> nat_bit i b.
Proof. reflexivity. Qed.

Lemma nat_bit_subset_refl : forall a,
  nat_bit_subset a a.
Proof. exact hfs_subset_refl. Qed.

Lemma nat_bit_subset_trans : forall a b c,
  nat_bit_subset a b -> nat_bit_subset b c -> nat_bit_subset a c.
Proof. exact hfs_subset_trans. Qed.

Lemma nat_bit_eq_zero_of_subset_zero : forall a,
  nat_bit_subset a 0 -> a = 0.
Proof.
  intros a H. apply hfs_subset_antisym.
  - exact H.
  - exact (hfs_empty_subset a).
Qed.

(** Bit inclusion implies the ordinary numerical order. *)
Lemma nat_bit_le_of_subset : forall a b,
  nat_bit_subset a b -> a <= b.
Proof.
  intros a b H. apply N.ldiff_le. apply N.bits_inj_0. intro i.
  rewrite N.ldiff_spec. destruct (N.testbit a i) eqn:Ha; simpl.
  - unfold nat_bit_subset, hfs_subset, hfs_mem in H.
    now rewrite (H i Ha).
  - reflexivity.
Qed.

Lemma nat_bit_ext : forall a b,
  (forall i, nat_bit i a <-> nat_bit i b) -> a = b.
Proof. exact hfs_extensionality. Qed.

Lemma nat_bit_ext_iff : forall a b,
  a = b <-> forall i, nat_bit i a <-> nat_bit i b.
Proof.
  intros a b. split; [now intros -> i | apply nat_bit_ext].
Qed.

Lemma nat_bit_pos_iff_nonempty : forall a,
  0 < a <-> a <> nat_bit_empty.
Proof.
  intro a. unfold nat_bit_empty, hfs_empty.
  symmetry. apply N.neq_0_lt_0.
Qed.

Lemma nat_bit_nonempty_of_pos : forall a,
  0 < a -> exists i, nat_bit i a.
Proof.
  intros a Ha. exists (N.log2 a). unfold nat_bit, hfs_mem.
  exact (N.bit_log2 a (proj2 (N.neq_0_lt_0 a) Ha)).
Qed.

Lemma nat_bit_eq_empty_or_nonempty : forall a,
  a = nat_bit_empty \/ exists i, nat_bit i a.
Proof.
  intro a. destruct (N.eq_dec a 0) as [-> | Ha].
  - now left.
  - right. apply nat_bit_nonempty_of_pos.
    exact (proj1 (N.neq_0_lt_0 a) Ha).
Qed.

Lemma nat_bit_nonempty_iff : forall a,
  a <> nat_bit_empty <-> exists i, nat_bit i a.
Proof.
  intro a. split.
  - intro Ha. apply nat_bit_nonempty_of_pos.
    exact (proj2 (@nat_bit_pos_iff_nonempty a) Ha).
  - intros [i Hi] ->. exact (@nat_bit_not_mem_empty i Hi).
Qed.

Lemma nat_bit_isempty_iff : forall a,
  a = nat_bit_empty <-> forall i, ~ nat_bit i a.
Proof.
  intro a. split.
  - intros ->. exact nat_bit_not_mem_empty.
  - intro H. apply nat_bit_ext. intro i. split.
    + intro Hi. exact (False_rect _ (H i Hi)).
    + intro Hi. exact (False_rect _ (@nat_bit_not_mem_empty i Hi)).
Qed.

Lemma nat_bit_empty_subset : forall a,
  nat_bit_subset nat_bit_empty a.
Proof. exact hfs_empty_subset. Qed.

Lemma nat_bit_log2_mem_of_pos : forall a,
  0 < a -> nat_bit (N.log2 a) a.
Proof.
  intros a Ha. unfold nat_bit, hfs_mem.
  exact (N.bit_log2 a (proj2 (N.neq_0_lt_0 a) Ha)).
Qed.

Lemma nat_bit_le_log2_of_mem : forall i a,
  nat_bit i a -> i <= N.log2 a.
Proof.
  intros i a H. apply N.nlt_ge. intro Hlt.
  unfold nat_bit, hfs_mem in H.
  rewrite (N.bits_above_log2 a i Hlt) in H. discriminate.
Qed.

Lemma nat_bit_lt_size_of_mem : forall i a,
  nat_bit i a -> i < N.size a.
Proof.
  intros i a H.
  rewrite N.size_log2.
  - apply (proj2 (N.lt_succ_r i (N.log2 a))).
    exact (@nat_bit_le_log2_of_mem i a H).
  - exact (proj2 (N.neq_0_lt_0 a) (@nat_bit_pos_of_nonempty i a H)).
Qed.

(** A code whose members all lie strictly below [log2 b] is itself below
    every positive [b].  This is Foundation's [lt_of_lt_log] in the standard
    binary model. *)
Lemma nat_bit_lt_of_lt_log2 : forall a b,
  0 < b ->
  (forall i, nat_bit i a -> i < N.log2 b) ->
  a < b.
Proof.
  intros a b Hb Hmembers.
  destruct (N.eq_dec a 0) as [-> | Ha]; [exact Hb |].
  apply N.log2_lt_cancel. apply Hmembers.
  apply nat_bit_log2_mem_of_pos.
  exact (proj1 (N.neq_0_lt_0 a) Ha).
Qed.

Lemma nat_bit_succ_mem_iff_div2 : forall i a,
  nat_bit (N.succ i) a <-> nat_bit i (N.div2 a).
Proof.
  intros i a. unfold nat_bit, hfs_mem.
  rewrite N.testbit_succ_r_div2 by apply N.le_0_l. reflexivity.
Qed.

Lemma nat_bit_subset_div2 : forall a b,
  nat_bit_subset a b -> nat_bit_subset (N.div2 a) (N.div2 b).
Proof.
  intros a b H i Hi. unfold nat_bit, hfs_mem in Hi |- *.
  rewrite <- (N.testbit_succ_r_div2 a i (N.le_0_l i)) in Hi.
  rewrite <- (N.testbit_succ_r_div2 b i (N.le_0_l i)).
  exact (H (N.succ i) Hi).
Qed.

Lemma nat_bit_zero_not_mem_iff_even : forall a,
  ~ nat_bit 0 a <-> N.Even a.
Proof.
  intro a. split.
  - intro H. apply N.even_spec.
    destruct (N.even a) eqn:He; [reflexivity |].
    exfalso. apply H. unfold nat_bit, hfs_mem.
    rewrite N.bit0_odd. unfold N.odd. now rewrite He.
  - intros [m ->] H. unfold nat_bit, hfs_mem in H.
    rewrite N.testbit_even_0 in H. discriminate.
Qed.

Lemma nat_bit_zero_not_mem_double : forall a,
  ~ nat_bit 0 (2 * a).
Proof.
  intros a H. unfold nat_bit, hfs_mem in H.
  rewrite N.testbit_even_0 in H. discriminate.
Qed.

Lemma nat_bit_zero_mem_double_add_one : forall a,
  nat_bit 0 (2 * a + 1).
Proof.
  intro a. unfold nat_bit, hfs_mem. apply N.testbit_odd_0.
Qed.

Lemma nat_bit_succ_mem_double_iff : forall i a,
  nat_bit (N.succ i) (2 * a) <-> nat_bit i a.
Proof.
  intros i a. unfold nat_bit, hfs_mem.
  rewrite N.testbit_even_succ by apply N.le_0_l. reflexivity.
Qed.

Lemma nat_bit_succ_mem_double_add_one_iff : forall i a,
  nat_bit (N.succ i) (2 * a + 1) <-> nat_bit i a.
Proof.
  intros i a. unfold nat_bit, hfs_mem.
  rewrite N.testbit_odd_succ by apply N.le_0_l. reflexivity.
Qed.

(** [nat_bit_under n] codes exactly the initial segment below [n]. *)
Definition nat_bit_under (n : N) : N := N.ones n.

Lemma nat_bit_le_under : forall n,
  n <= nat_bit_under n.
Proof.
  intro n. unfold nat_bit_under. rewrite N.ones_equiv.
  apply N.lt_le_pred. exact (N.pow_gt_lin_r 2 n eq_refl).
Qed.

Lemma nat_bit_under_lt_pow : forall n,
  nat_bit_under n < 2 ^ n.
Proof.
  intro n. unfold nat_bit_under. rewrite N.ones_equiv.
  apply N.lt_pred_l. apply N.pow_nonzero. discriminate.
Qed.

Lemma nat_bit_mem_under_iff : forall i j,
  nat_bit i (nat_bit_under j) <-> i < j.
Proof.
  intros i j. unfold nat_bit, nat_bit_under, hfs_mem.
  apply N.ones_spec_iff.
Qed.

Lemma nat_bit_mem_exp_add_succ_sub_one : forall i j,
  nat_bit i (2 ^ (i + j + 1) - 1).
Proof.
  intros i j.
  assert (E : 2 ^ (i + j + 1) - 1 = nat_bit_under (i + j + 1)).
  { unfold nat_bit_under. rewrite N.ones_equiv. apply N.sub_1_r. }
  rewrite E.
  apply (proj2 (nat_bit_mem_under_iff i (i + j + 1))).
  lia.
Qed.

Lemma nat_bit_not_mem_under_self : forall i,
  ~ nat_bit i (nat_bit_under i).
Proof.
  intro i. rewrite nat_bit_mem_under_iff. apply N.lt_irrefl.
Qed.

Lemma nat_bit_under_injective : forall i j,
  nat_bit_under i = nat_bit_under j <-> i = j.
Proof.
  intros i j. split; [|now intros ->].
  intro H. unfold nat_bit_under in H. rewrite !N.ones_equiv in H.
  apply (N.pow_inj_r 2 i j eq_refl). apply N.pred_inj.
  - apply N.pow_nonzero. discriminate.
  - apply N.pow_nonzero. discriminate.
  - exact H.
Qed.

Lemma nat_bit_under_zero : nat_bit_under 0 = nat_bit_empty.
Proof. unfold nat_bit_under, nat_bit_empty, hfs_empty. apply N.ones_0. Qed.

Lemma nat_bit_under_succ : forall i,
  nat_bit_under (N.succ i) = nat_bit_insert i (nat_bit_under i).
Proof.
  intro i. apply N.bits_inj. intro x. apply Bool.eq_true_iff_eq.
  unfold nat_bit_under, nat_bit_insert, hfs_insert.
  rewrite N.ones_spec_iff, N.setbit_iff, N.ones_spec_iff,
    N.lt_succ_r, N.le_lteq.
  intuition congruence.
Qed.

Lemma nat_bit_under_succ_arithmetic : forall i,
  nat_bit_under (N.succ i) = 2 * nat_bit_under i + 1.
Proof. exact N.ones_succ. Qed.

Lemma nat_bit_lt_pow_iff : forall a i,
  a < 2 ^ i <-> forall j, nat_bit j a -> j < i.
Proof.
  intros a i. split.
  - intros H j Hj.
    apply (proj2 (N.pow_lt_mono_r_iff 2 j i eq_refl)).
    exact (N.le_lt_trans _ _ _ (@nat_bit_exp_le_of_mem j a Hj) H).
  - intro H. eapply N.le_lt_trans.
    + apply nat_bit_le_of_subset. intros j Hj.
      apply (proj2 (@nat_bit_mem_under_iff j i)). exact (H j Hj).
    + apply nat_bit_under_lt_pow.
Qed.

Lemma nat_bit_insert_remove : forall i a,
  nat_bit i a ->
  nat_bit_insert i (nat_bit_remove i a) = a.
Proof. exact hfs_insert_remove. Qed.
