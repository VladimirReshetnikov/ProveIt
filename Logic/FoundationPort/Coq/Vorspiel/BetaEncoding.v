(** Concrete finite-sequence encoding for the Gödel beta function. *)

From Stdlib Require Import Arith.Arith Lia.

(** This identity is stated before importing MathComp so [nia] sees the
    Stdlib arithmetic operations directly.  It is the Bezout certificate
    used for the pairwise-coprime beta moduli below. *)
Lemma beta_bezout_identity : forall i j k stride : nat,
  0 < k -> stride = (j - i) * k -> i < j ->
  (S i * S i * k) * S (S j * stride) -
    (S i * k * S j - 1) * S (S i * stride) = 1.
Proof. intros i j k stride Hk Hstride Hij. nia. Qed.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From Foundation.Vorspiel Require Import Matrix Arithmetic.

Set Implicit Arguments.
Unset Strict Implicit.

(** Restore Stdlib's propositional order notation locally; MathComp's
    boolean order remains available through [ltP] and [leP]. *)
Local Infix "<" := Nat.lt : nat_scope.
Local Infix "<=" := Nat.le : nat_scope.

(** MathComp and Stdlib implement the same Euclidean remainder through
    different transparent functions. *)
Lemma mathcomp_modn_eq_nat_modulo : forall m d,
  m %% d = Nat.modulo m d.
Proof.
  intros m d. destruct d as [|d].
  - rewrite modn0. rewrite Nat.mod_0_r. reflexivity.
  - apply Nat.mod_unique with (q := m %/ S d).
    + apply/ltP. rewrite ltn_mod. exact (ltn0Sn d).
    + pose proof (divn_eq m (S d)) as Hdiv.
      rewrite Nat.mul_comm. exact Hdiv.
Qed.

Fixpoint beta_factorial (n : nat) : nat :=
  match n with 0 => 1 | S k => S k * beta_factorial k end.

Lemma beta_factorial_positive : forall n, 0 < beta_factorial n.
Proof.
  induction n; simpl; [lia |].
  apply Nat.mul_pos_pos; [lia | exact IHn].
Qed.

Lemma beta_factorial_divides : forall d n,
  0 < d -> d <= n -> Nat.divide d (beta_factorial n).
Proof.
  intros d n Hd Hdn. induction n as [|n IH]; [lia |].
  simpl. destruct (Nat.eq_dec d (S n)) as [-> | Hne].
  - exists (beta_factorial n). apply Nat.mul_comm.
  - assert (Hdle : d <= n) by lia.
    destruct (IH Hdle) as [k Hk].
    exists (S n * k). rewrite Hk. rewrite <- Nat.mul_assoc. reflexivity.
Qed.

Fixpoint beta_prefix_bound (len : nat) (a : nat -> nat) : nat :=
  match len with
  | 0 => 1
  | S k => Nat.max (S (a k)) (beta_prefix_bound k a)
  end.

Lemma beta_prefix_bound_positive : forall len a,
  0 < beta_prefix_bound len a.
Proof.
  induction len; intro a.
  - cbn. lia.
  - change (0 < Nat.max (S (a len)) (beta_prefix_bound len a)).
    eapply Nat.lt_le_trans with (m := S (a len)).
    + lia.
    + apply Nat.le_max_l.
Qed.

Lemma beta_prefix_bound_gt : forall len a i,
  i < len -> a i < beta_prefix_bound len a.
Proof.
  induction len as [|len IH]; intros a i Hi; [lia |].
  change (a i < Nat.max (S (a len)) (beta_prefix_bound len a)).
  destruct (Nat.eq_dec i len) as [-> | Hne].
  - apply Nat.lt_le_trans with (S (a len)); [lia | apply Nat.le_max_l].
  - apply Nat.lt_le_trans with (beta_prefix_bound len a).
    + apply IH. lia.
    + apply Nat.le_max_r.
Qed.

Definition beta_stride (len : nat) (a : nat -> nat) : nat :=
  beta_factorial len * beta_prefix_bound len a.

Lemma beta_stride_positive : forall len a, 0 < beta_stride len a.
Proof.
  intros len a. unfold beta_stride.
  apply Nat.mul_pos_pos.
  - apply beta_factorial_positive.
  - apply beta_prefix_bound_positive.
Qed.

Lemma beta_stride_gt : forall len a i,
  i < len -> a i < beta_stride len a.
Proof.
  intros len a i Hi. unfold beta_stride.
  eapply Nat.lt_le_trans.
  - apply beta_prefix_bound_gt; exact Hi.
  - apply Nat.le_mul_l.
    apply Nat.neq_0_lt_0, beta_factorial_positive.
Qed.

Lemma beta_stride_divides_difference : forall len a d,
  0 < d -> d <= len -> Nat.divide d (beta_stride len a).
Proof.
  intros len a d Hd Hdle. unfold beta_stride.
  destruct (@beta_factorial_divides d len Hd Hdle) as [k Hk].
  exists (k * beta_prefix_bound len a).
  rewrite Hk. apply Nat.mul_shuffle0.
Qed.

Definition beta_modulus (stride i : nat) : nat := S (S i * stride).

Lemma beta_modulus_positive : forall stride i,
  0 < beta_modulus stride i.
Proof. intros; unfold beta_modulus; lia. Qed.

(** Factorial spacing yields an explicit Bezout certificate. *)
Lemma beta_moduli_coprime : forall len a i j,
  i < j -> j < len ->
  coprime (beta_modulus (beta_stride len a) i)
          (beta_modulus (beta_stride len a) j).
Proof.
  intros len a i j Hij Hjlen.
  set (stride := beta_stride len a).
  set (d := j - i).
  assert (Hd : 0 < d).
  { unfold d. apply Nat.neq_0_lt_0, Nat.sub_gt. exact Hij. }
  assert (Hdle : d <= len).
  { unfold d. eapply Nat.le_trans; [apply Nat.le_sub_l | lia]. }
  destruct (beta_stride_divides_difference
    (len := len) a (d := d) Hd Hdle)
    as [k Hk].
  assert (Hstride : stride = d * k).
  { unfold stride. rewrite Hk. apply Nat.mul_comm. }
  assert (Hkpos : 0 < k).
  { apply Nat.neq_0_lt_0. intro Hzero. subst k.
    simpl in Hk. pose proof (beta_stride_positive len a). lia. }
  rewrite coprime_sym.
  apply/coprimeP.
  - apply/ltP. apply beta_modulus_positive.
  - exists ((S i * S i * k), (S i * k * S j - 1)).
    unfold beta_modulus, d in *.
    rewrite !mulnE !subnE in Hstride |-.
    apply beta_bezout_identity; assumption.
Qed.

Fixpoint beta_modulus_product (count stride : nat) : nat :=
  match count with
  | 0 => 1
  | S k => beta_modulus_product k stride * beta_modulus stride k
  end.

Lemma beta_modulus_divides_product : forall stride count i,
  i < count ->
  beta_modulus stride i %| beta_modulus_product count stride.
Proof.
  intros stride count; induction count as [|count IH]; intros i Hi; [lia |].
  simpl. destruct (Nat.eq_dec i count) as [-> | Hne].
  - apply dvdn_mull, dvdnn.
  - apply dvdn_mulr, IH. lia.
Qed.

Lemma beta_modulus_product_coprime_later : forall len a count j,
  count <= j -> j < len ->
  coprime (beta_modulus_product count (beta_stride len a))
          (beta_modulus (beta_stride len a) j).
Proof.
  intros len a count; induction count as [|count IH]; intros j Hcount Hj.
  - simpl. apply coprime1n.
  - simpl. rewrite coprimeMl. apply/andP; split.
    + apply IH; lia.
    + apply beta_moduli_coprime; lia.
Qed.

Fixpoint beta_crt_prefix (count : nat) (a : nat -> nat)
    (stride : nat) : nat :=
  match count with
  | 0 => 0
  | S k => chinese
      (beta_modulus_product k stride) (beta_modulus stride k)
      (beta_crt_prefix k a stride) (a k)
  end.

Lemma beta_crt_prefix_correct : forall len a count i,
  count <= len -> i < count ->
  beta_crt_prefix count a (beta_stride len a) %%
      beta_modulus (beta_stride len a) i =
    a i %% beta_modulus (beta_stride len a) i.
Proof.
  intros len a count; induction count as [|count IH];
    intros i Hcount Hi; [lia |].
  simpl.
  assert (Hcop :
    coprime (beta_modulus_product count (beta_stride len a))
      (beta_modulus (beta_stride len a) count)).
  { apply beta_modulus_product_coprime_later; lia. }
  destruct (Nat.eq_dec i count) as [-> | Hne].
  - apply chinese_modr. exact Hcop.
  - assert (Hdvd :
      beta_modulus (beta_stride len a) i %|
        beta_modulus_product count (beta_stride len a)).
    { apply beta_modulus_divides_product. lia. }
    etransitivity.
    + symmetry. apply modn_dvdm. exact Hdvd.
    + etransitivity.
      * apply (f_equal (fun x =>
          x %% beta_modulus (beta_stride len a) i)).
        apply chinese_modl. exact Hcop.
      * etransitivity.
        -- apply modn_dvdm. exact Hdvd.
        -- apply IH; lia.
Qed.

Definition concrete_beta_encode (len : nat) (a : nat -> nat) : nat :=
  nat_pair (beta_crt_prefix len a (beta_stride len a))
    (beta_stride len a).

Lemma concrete_beta_encode_correct : forall len a i,
  i < len -> nat_beta (concrete_beta_encode len a) i = a i.
Proof.
  intros len a i Hi. unfold concrete_beta_encode.
  rewrite nat_beta_pair.
  change
    (beta_crt_prefix len a (beta_stride len a) mod
       beta_modulus (beta_stride len a) i = a i).
  rewrite <- !mathcomp_modn_eq_nat_modulo.
  pose proof (@beta_crt_prefix_correct len a len i
    (Nat.le_refl len) Hi) as Hcrt.
  rewrite Hcrt.
  rewrite modn_small; [reflexivity |].
  apply/ltP.
  pose proof (@beta_stride_gt len a i Hi) as Hstride.
  unfold beta_modulus. rewrite mulnE.
  eapply Nat.lt_le_trans; [exact Hstride |].
  eapply Nat.le_trans.
  - apply Nat.le_mul_l. apply Nat.neq_succ_0.
  - apply Nat.le_succ_diag_r.
Qed.

Definition concrete_beta_sequence_encoder : beta_sequence_encoder :=
  {| beta_encode := concrete_beta_encode;
     beta_encode_correct := concrete_beta_encode_correct |}.

Corollary arithmetic1_primitive_recursion_concrete : forall n
    (f : (Fin.t n -> nat) -> nat)
    (g : (Fin.t (S (S n)) -> nat) -> nat),
  arithmetic1 f -> arithmetic1 g ->
  arithmetic1 (fun v : Fin.t (S n) -> nat =>
    arithmetic_primitive_recursion f g
      (matrix_vec_head v) (matrix_vec_tail v)).
Proof. apply arithmetic1_primitive_recursion, concrete_beta_sequence_encoder. Qed.

Corollary arithmetic1_of_primitive_recursive1_concrete : forall n
    (f : (Fin.t n -> nat) -> nat),
  primitive_recursive1 n f -> arithmetic1 f.
Proof.
  apply arithmetic1_of_primitive_recursive1,
    concrete_beta_sequence_encoder.
Qed.

Corollary arith_part1_iff_partial_recursive1_concrete : forall n
    (f : arith_partial_function n),
  arith_part1 n f <-> partial_recursive1 n f.
Proof.
  apply arith_part1_iff_partial_recursive1,
    concrete_beta_sequence_encoder.
Qed.
