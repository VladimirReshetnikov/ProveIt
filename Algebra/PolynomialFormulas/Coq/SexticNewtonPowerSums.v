From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From Stdlib Require Import Ring Lia.
From PolynomialFormulas Require Import SexticSparsePolynomials
  SexticPowerSumSymmetric.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Newton reconstruction of power sums in six variables.  All programs in
    this file are transparent sparse-list computations; the ring-valued
    interpretation is used only for their correctness proofs. *)
Module PolynomialFormulasSexticNewtonPowerSums.

Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticPowerSumSymmetric.

Section RingEvaluation.

Variable R : comPzRingType.

Definition exponent_value_ring (values : 6.-tuple R)
    (d : sparse_exponent) : R :=
  \prod_(i : 'I_6) tnth values i ^+ tnth d i.

Definition sparse_eval_ring (values : 6.-tuple R)
    (p : sparse_polynomial) : R :=
  \sum_(t <- p) (t.1)%:~R * exponent_value_ring values t.2.

Lemma exponent_value_ring_zero values :
  exponent_value_ring values exponent_zero = 1.
Proof.
rewrite /exponent_value_ring; apply: big1=> i _.
by rewrite tnth_exponent_zeroE expr0.
Qed.

Lemma exponent_value_ring_single values (j : 'I_6) :
  exponent_value_ring values (exponent_single j) = tnth values j.
Proof.
rewrite /exponent_value_ring (bigD1 j) //=.
rewrite tnth_exponent_singleE eqxx expr1.
suff -> : \prod_(i < 6 | i != j)
    tnth values i ^+ tnth (exponent_single j) i = 1 by rewrite mulr1.
apply: big1=> i hij.
by rewrite tnth_exponent_singleE (negbTE hij) expr0.
Qed.

Lemma exponent_value_ring_add values a b :
  exponent_value_ring values (exponent_add a b) =
    exponent_value_ring values a * exponent_value_ring values b.
Proof.
rewrite /exponent_value_ring.
under eq_bigr do rewrite tnth_exponent_addE exprD.
exact: big_split.
Qed.

Lemma sparse_eval_ring_zero values :
  sparse_eval_ring values sparse_zero = 0.
Proof. by rewrite /sparse_eval_ring /sparse_zero big_nil. Qed.

Lemma sparse_eval_ring_const values z :
  sparse_eval_ring values (sparse_const z) = z%:~R.
Proof.
by rewrite /sparse_eval_ring /sparse_const big_seq1
  exponent_value_ring_zero mulr1.
Qed.

Lemma sparse_eval_ring_var values i :
  sparse_eval_ring values (sparse_var i) = tnth values i.
Proof.
by rewrite /sparse_eval_ring /sparse_var big_seq1
  exponent_value_ring_single rmorph1 mul1r.
Qed.

Lemma sparse_eval_ring_add values p q :
  sparse_eval_ring values (sparse_add p q) =
    sparse_eval_ring values p + sparse_eval_ring values q.
Proof. by rewrite /sparse_eval_ring /sparse_add big_cat. Qed.

Lemma sparse_eval_ring_neg values p :
  sparse_eval_ring values (sparse_neg p) = - sparse_eval_ring values p.
Proof.
rewrite /sparse_eval_ring /sparse_neg big_map /=.
under eq_bigr do rewrite /term_neg /= rmorphN mulNr.
exact: sumrN.
Qed.

Lemma sparse_eval_ring_sub values p q :
  sparse_eval_ring values (sparse_sub p q) =
    sparse_eval_ring values p - sparse_eval_ring values q.
Proof. by rewrite /sparse_sub sparse_eval_ring_add sparse_eval_ring_neg. Qed.

Lemma sparse_eval_ring_mul values p q :
  sparse_eval_ring values (sparse_mul p q) =
    sparse_eval_ring values p * sparse_eval_ring values q.
Proof.
rewrite /sparse_eval_ring /sparse_mul big_flatten big_map /=.
under eq_bigr=> t ht do rewrite big_map /=.
under eq_bigr=> t ht do
  under eq_bigr=> u hu do
    rewrite /term_mul /= rmorphM exponent_value_ring_add mulrACA.
rewrite big_distrl.
apply: eq_bigr=> t ht.
by rewrite big_distrr.
Qed.

Lemma sparse_eval_ring_pow values p n :
  sparse_eval_ring values (sparse_pow p n) =
    sparse_eval_ring values p ^+ n.
Proof.
elim: n=> [|n ih] /=.
- exact: sparse_eval_ring_const.
- by rewrite sparse_eval_ring_mul ih exprS.
Qed.

Lemma sparse_eval_ring_product values ps :
  sparse_eval_ring values (sparse_product ps) =
    \prod_(p <- ps) sparse_eval_ring values p.
Proof.
elim: ps=> [|p ps ih] /=.
- by rewrite big_nil; exact: sparse_eval_ring_const.
- by rewrite sparse_eval_ring_mul ih big_cons.
Qed.

Fixpoint root_esymm_list
    (values : 6.-tuple R) (indices : seq 'I_6) (k : nat) : R :=
  match k, indices with
  | 0%N, _ => 1
  | _.+1, [::] => 0
  | k'.+1, i :: is' =>
      tnth values i * root_esymm_list values is' k' +
        root_esymm_list values is' k'.+1
  end.

Definition root_esymm (values : 6.-tuple R) (i : 'I_6) : R :=
  root_esymm_list values six_indices i.+1.

Lemma sparse_eval_ring_esymm_list values indices k :
  sparse_eval_ring values (esymm_list indices k) =
    root_esymm_list values indices k.
Proof.
elim: indices k=> [|i indices ih] [|k] /=.
- exact: sparse_eval_ring_const.
- exact: sparse_eval_ring_zero.
- exact: sparse_eval_ring_const.
- by rewrite sparse_eval_ring_add sparse_eval_ring_mul
    sparse_eval_ring_var ih ih addrC.
Qed.

Lemma sparse_eval_ring_esymm values i :
  sparse_eval_ring values (esymm_sparse i) = root_esymm values i.
Proof. exact: sparse_eval_ring_esymm_list. Qed.

Lemma six_indicesE :
  six_indices =
    [:: inord 0; inord 1; inord 2; inord 3; inord 4; inord 5].
Proof.
apply: (inj_map val_inj).
rewrite /six_indices val_enum_ord /=.
by rewrite (@inordK 5 0 isT) (@inordK 5 1 isT)
  (@inordK 5 2 isT) (@inordK 5 3 isT)
  (@inordK 5 4 isT) (@inordK 5 5 isT).
Qed.

(** The standard [ring] tactic keys its structures by a syntactic carrier.
    MathComp's packed projections are definitionally equal but syntactically
    different, so these small opaque wrappers expose one uniform carrier to
    the tactic. *)
Let ring_carrier := GRing.PzSemiRing.sort R.
Local Definition ring_zero : ring_carrier := 0.
Local Definition ring_one : ring_carrier := 1.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add R.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul R.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp R.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma ring_addE x y : x + y = ring_add x y.
Proof. reflexivity. Qed.
Lemma ring_mulE x y : x * y = ring_mul x y.
Proof. reflexivity. Qed.
Lemma ring_subE x y : x - y = ring_sub x y.
Proof. reflexivity. Qed.
Lemma ring_oppE x : - x = ring_opp x.
Proof. reflexivity. Qed.
Lemma ring_zeroE : (0 : R) = ring_zero.
Proof. reflexivity. Qed.
Lemma ring_oneE : (1 : R) = ring_one.
Proof. reflexivity. Qed.

Lemma mathcomp_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring mathcomp_ring : mathcomp_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_mathcomp_ring :=
  repeat first
    [ rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma two_natrE : (2%:R : R) = 1 + 1.
Proof. exact: (@natrD R 1 1). Qed.

Lemma three_natrE : (3%:R : R) = 1 + 1 + 1.
Proof.
rewrite -two_natrE.
exact: (@natrD R 2 1).
Qed.

Lemma four_natrE : (4%:R : R) = 1 + 1 + 1 + 1.
Proof.
rewrite -three_natrE.
exact: (@natrD R 3 1).
Qed.

Lemma five_natrE : (5%:R : R) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -four_natrE.
exact: (@natrD R 4 1).
Qed.

Lemma six_natrE : (6%:R : R) = 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -five_natrE.
exact: (@natrD R 5 1).
Qed.

Lemma alternating_six_zero (a b c d e f g : R) :
  a - b + c - d + e - f + g = 0 ->
  a = b - c + d - e + f - g.
Proof.
move=> h; apply: subr0_eq.
have heq :
    a - (b - c + d - e + f - g) = a - b + c - d + e - f + g.
  finish_mathcomp_ring.
by rewrite heq.
Qed.

Lemma root_esymm_list_zero values indices :
  root_esymm_list values indices 0 = 1.
Proof. by case: indices. Qed.

Lemma root_esymm_list_one values indices :
  root_esymm_list values indices 1 =
    \sum_(i <- indices) tnth values i.
Proof.
elim: indices=> [|i indices ih] /=.
- by rewrite big_nil.
- by rewrite root_esymm_list_zero mulr1 ih big_cons.
Qed.

Lemma root_power_sum_one values :
  root_power_sum values 1 = root_esymm values ord0.
Proof.
rewrite /root_power_sum /root_esymm root_esymm_list_one /six_indices.
rewrite big_enum; apply: eq_bigr=> i _.
by rewrite expr1.
Qed.

Definition root_power_sum_list
    (values : 6.-tuple R) (indices : seq 'I_6) (n : nat) : R :=
  \sum_(i <- indices) tnth values i ^+ n.

Lemma root_power_sum_list_enum values n :
  root_power_sum_list values six_indices n = root_power_sum values n.
Proof. by rewrite /root_power_sum_list /root_power_sum /six_indices big_enum. Qed.

Lemma root_power_sum_list_oneE values indices :
  root_power_sum_list values indices 1 =
    root_esymm_list values indices 1.
Proof.
rewrite root_esymm_list_one /root_power_sum_list.
apply: eq_bigr=> i _.
by rewrite expr1.
Qed.

Lemma sum_expr_one (values : 6.-tuple R) (indices : seq 'I_6) :
  \sum_(i <- indices) tnth values i ^+ 1 =
    \sum_(i <- indices) tnth values i.
Proof. by apply: eq_bigr=> i _; rewrite expr1. Qed.

Lemma root_power_sum_list_two values indices :
  root_power_sum_list values indices 2 =
    root_esymm_list values indices 1 *
      root_power_sum_list values indices 1 -
    2%:R * root_esymm_list values indices 2.
Proof.
elim: indices=> [|i indices ih].
- rewrite /root_power_sum_list !big_nil /=.
  finish_mathcomp_ring.
- rewrite [root_power_sum_list values (i :: indices) 2]
    /root_power_sum_list big_cons.
  rewrite [root_power_sum_list values (i :: indices) 1]
    /root_power_sum_list big_cons /= root_esymm_list_zero.
  rewrite /root_power_sum_list in ih.
  rewrite ih two_natrE.
  repeat rewrite exprS.
  rewrite !expr0 !mulr1.
  rewrite !sum_expr_one root_esymm_list_one.
  finish_mathcomp_ring.
Qed.

Lemma root_power_sum_two values :
  root_power_sum values 2 =
    root_esymm values ord0 * root_power_sum values 1 -
      2%:R * root_esymm values (inord 1).
Proof.
rewrite -!root_power_sum_list_enum /root_esymm.
rewrite (@inordK 5 1 isT).
exact: root_power_sum_list_two.
Qed.

Lemma root_power_sum_list_three values indices :
  root_power_sum_list values indices 3 =
    root_esymm_list values indices 1 *
      root_power_sum_list values indices 2 -
    root_esymm_list values indices 2 *
      root_power_sum_list values indices 1 +
    3%:R * root_esymm_list values indices 3.
Proof.
elim: indices=> [|i indices ih].
- rewrite /root_power_sum_list !big_nil /=.
  finish_mathcomp_ring.
- have p2 := root_power_sum_list_two values indices.
  rewrite /root_power_sum_list in ih p2 *.
  rewrite !big_cons /= root_esymm_list_zero ih p2.
  rewrite two_natrE three_natrE !sum_expr_one.
  repeat rewrite exprS.
  rewrite !expr0 !mulr1.
  finish_mathcomp_ring.
Qed.

Lemma root_power_sum_three values :
  root_power_sum values 3 =
    root_esymm values ord0 * root_power_sum values 2 -
    root_esymm values (inord 1) * root_power_sum values 1 +
    3%:R * root_esymm values (inord 2).
Proof.
rewrite -!root_power_sum_list_enum /root_esymm.
rewrite (@inordK 5 1 isT) (@inordK 5 2 isT).
exact: root_power_sum_list_three.
Qed.

Lemma root_power_sum_list_four values indices :
  root_power_sum_list values indices 4 =
    root_esymm_list values indices 1 *
      root_power_sum_list values indices 3 -
    root_esymm_list values indices 2 *
      root_power_sum_list values indices 2 +
    root_esymm_list values indices 3 *
      root_power_sum_list values indices 1 -
    4%:R * root_esymm_list values indices 4.
Proof.
elim: indices=> [|i indices ih].
- rewrite /root_power_sum_list !big_nil /=.
  finish_mathcomp_ring.
- have p2 := root_power_sum_list_two values indices.
  have p3 := root_power_sum_list_three values indices.
  rewrite /root_power_sum_list in ih p2 p3 *.
  rewrite !big_cons /= root_esymm_list_zero ih p3 p2.
  rewrite two_natrE three_natrE four_natrE !sum_expr_one.
  repeat rewrite exprS.
  rewrite !expr0 !mulr1.
  finish_mathcomp_ring.
Qed.

Lemma root_power_sum_four values :
  root_power_sum values 4 =
    root_esymm values ord0 * root_power_sum values 3 -
    root_esymm values (inord 1) * root_power_sum values 2 +
    root_esymm values (inord 2) * root_power_sum values 1 -
    4%:R * root_esymm values (inord 3).
Proof.
rewrite -!root_power_sum_list_enum /root_esymm.
rewrite (@inordK 5 1 isT) (@inordK 5 2 isT) (@inordK 5 3 isT).
exact: root_power_sum_list_four.
Qed.

Lemma root_power_sum_list_five values indices :
  root_power_sum_list values indices 5 =
    root_esymm_list values indices 1 *
      root_power_sum_list values indices 4 -
    root_esymm_list values indices 2 *
      root_power_sum_list values indices 3 +
    root_esymm_list values indices 3 *
      root_power_sum_list values indices 2 -
    root_esymm_list values indices 4 *
      root_power_sum_list values indices 1 +
    5%:R * root_esymm_list values indices 5.
Proof.
elim: indices=> [|i indices ih].
- rewrite /root_power_sum_list !big_nil /=.
  finish_mathcomp_ring.
- have p2 := root_power_sum_list_two values indices.
  have p3 := root_power_sum_list_three values indices.
  have p4 := root_power_sum_list_four values indices.
  rewrite /root_power_sum_list in ih p2 p3 p4 *.
  rewrite !big_cons /= root_esymm_list_zero ih p4 p3 p2.
  rewrite two_natrE three_natrE four_natrE five_natrE !sum_expr_one.
  repeat rewrite exprS.
  rewrite !expr0 !mulr1.
  finish_mathcomp_ring.
Qed.

Lemma root_power_sum_five values :
  root_power_sum values 5 =
    root_esymm values ord0 * root_power_sum values 4 -
    root_esymm values (inord 1) * root_power_sum values 3 +
    root_esymm values (inord 2) * root_power_sum values 2 -
    root_esymm values (inord 3) * root_power_sum values 1 +
    5%:R * root_esymm values (inord 4).
Proof.
rewrite -!root_power_sum_list_enum /root_esymm.
rewrite (@inordK 5 1 isT) (@inordK 5 2 isT) (@inordK 5 3 isT)
  (@inordK 5 4 isT).
exact: root_power_sum_list_five.
Qed.

Lemma root_power_sum_list_six values indices :
  root_power_sum_list values indices 6 =
    root_esymm_list values indices 1 *
      root_power_sum_list values indices 5 -
    root_esymm_list values indices 2 *
      root_power_sum_list values indices 4 +
    root_esymm_list values indices 3 *
      root_power_sum_list values indices 3 -
    root_esymm_list values indices 4 *
      root_power_sum_list values indices 2 +
    root_esymm_list values indices 5 *
      root_power_sum_list values indices 1 -
    6%:R * root_esymm_list values indices 6.
Proof.
elim: indices=> [|i indices ih].
- rewrite /root_power_sum_list !big_nil /=.
  finish_mathcomp_ring.
- have p2 := root_power_sum_list_two values indices.
  have p3 := root_power_sum_list_three values indices.
  have p4 := root_power_sum_list_four values indices.
  have p5 := root_power_sum_list_five values indices.
  rewrite /root_power_sum_list in ih p2 p3 p4 p5 *.
  rewrite !big_cons /= root_esymm_list_zero ih p5 p4 p3 p2.
  rewrite two_natrE three_natrE four_natrE five_natrE six_natrE
    !sum_expr_one.
  repeat rewrite exprS.
  rewrite !expr0 !mulr1.
  finish_mathcomp_ring.
Qed.

Lemma root_power_sum_six values :
  root_power_sum values 6 =
    root_esymm values ord0 * root_power_sum values 5 -
    root_esymm values (inord 1) * root_power_sum values 4 +
    root_esymm values (inord 2) * root_power_sum values 3 -
    root_esymm values (inord 3) * root_power_sum values 2 +
    root_esymm values (inord 4) * root_power_sum values 1 -
    6%:R * root_esymm values (inord 5).
Proof.
rewrite -!root_power_sum_list_enum /root_esymm.
rewrite (@inordK 5 1 isT) (@inordK 5 2 isT) (@inordK 5 3 isT)
  (@inordK 5 4 isT) (@inordK 5 5 isT).
exact: root_power_sum_list_six.
Qed.

(** The recurrence beyond degree six comes from the monic polynomial whose
    roots are the six entries.  Defining it first as a product makes the root
    property constructive and independent of ordinal proof terms. *)
Fixpoint characteristic_product
    (values : 6.-tuple R) (indices : seq 'I_6) (x : R) : R :=
  if indices is i :: indices' then
    (x - tnth values i) * characteristic_product values indices' x
  else 1.

Lemma characteristic_product_mem values indices (i : 'I_6) :
  i \in indices ->
  characteristic_product values indices (tnth values i) = 0.
Proof.
elim: indices=> [|j indices ih] //=.
rewrite in_cons; move/orP=> [/eqP ->|hi].
- by rewrite subrr mul0r.
- by rewrite ih // mulr0.
Qed.

Lemma characteristic_product_six values x :
  characteristic_product values six_indices x =
    x ^+ 6 - root_esymm values ord0 * x ^+ 5 +
    root_esymm values (inord 1) * x ^+ 4 -
    root_esymm values (inord 2) * x ^+ 3 +
    root_esymm values (inord 3) * x ^+ 2 -
    root_esymm values (inord 4) * x +
    root_esymm values (inord 5).
Proof.
rewrite /root_esymm six_indicesE /=.
rewrite (@inordK 5 1 isT) (@inordK 5 2 isT) (@inordK 5 3 isT)
  (@inordK 5 4 isT) (@inordK 5 5 isT).
repeat rewrite exprS.
rewrite !expr0 !mulr1.
finish_mathcomp_ring.
Qed.

Lemma root_characteristic values (i : 'I_6) :
  tnth values i ^+ 6 =
    root_esymm values ord0 * tnth values i ^+ 5 -
    root_esymm values (inord 1) * tnth values i ^+ 4 +
    root_esymm values (inord 2) * tnth values i ^+ 3 -
    root_esymm values (inord 3) * tnth values i ^+ 2 +
    root_esymm values (inord 4) * tnth values i -
    root_esymm values (inord 5).
Proof.
have hmem : i \in six_indices by rewrite /six_indices mem_enum.
have hroot := characteristic_product_mem values hmem.
rewrite characteristic_product_six in hroot.
exact: alternating_six_zero hroot.
Qed.

Lemma root_power_recurrence_point values (i : 'I_6) n :
  tnth values i ^+ (n + 6) =
    root_esymm values ord0 * tnth values i ^+ (n + 5) -
    root_esymm values (inord 1) * tnth values i ^+ (n + 4) +
    root_esymm values (inord 2) * tnth values i ^+ (n + 3) -
    root_esymm values (inord 3) * tnth values i ^+ (n + 2) +
    root_esymm values (inord 4) * tnth values i ^+ (n + 1) -
    root_esymm values (inord 5) * tnth values i ^+ n.
Proof.
rewrite !exprD root_characteristic.
rewrite expr1.
finish_mathcomp_ring.
Qed.

Lemma root_power_sum_recurrence values n :
  root_power_sum values (n + 6) =
    root_esymm values ord0 * root_power_sum values (n + 5) -
    root_esymm values (inord 1) * root_power_sum values (n + 4) +
    root_esymm values (inord 2) * root_power_sum values (n + 3) -
    root_esymm values (inord 3) * root_power_sum values (n + 2) +
    root_esymm values (inord 4) * root_power_sum values (n + 1) -
    root_esymm values (inord 5) * root_power_sum values n.
Proof.
rewrite /root_power_sum.
under eq_bigr do rewrite root_power_recurrence_point.
rewrite !sumrB !big_split !sumrN -!big_distrr.
reflexivity.
Qed.

(** Executable Newton reconstruction.  A state stores six consecutive power
    sums as sparse polynomials in the elementary variables [e1], ..., [e6]. *)
Fixpoint sparse_nsmul (n : nat) (p : sparse_polynomial) :
    sparse_polynomial :=
  if n is n'.+1 then sparse_add p (sparse_nsmul n' p)
  else sparse_zero.

Lemma sparse_eval_ring_nsmul values n p :
  sparse_eval_ring values (sparse_nsmul n p) =
    n%:R * sparse_eval_ring values p.
Proof.
elim: n=> [|n ih] /=.
- by rewrite sparse_eval_ring_zero mul0r.
- by rewrite sparse_eval_ring_add ih -nat1r mulrDl mul1r.
Qed.

Definition newton_e1 : sparse_polynomial := sparse_var ord0.
Definition newton_e2 : sparse_polynomial := sparse_var (inord 1).
Definition newton_e3 : sparse_polynomial := sparse_var (inord 2).
Definition newton_e4 : sparse_polynomial := sparse_var (inord 3).
Definition newton_e5 : sparse_polynomial := sparse_var (inord 4).
Definition newton_e6 : sparse_polynomial := sparse_var (inord 5).

Definition newton_p1 : sparse_polynomial := newton_e1.
Definition newton_p2 : sparse_polynomial :=
  sparse_sub (sparse_mul newton_e1 newton_p1)
    (sparse_nsmul 2 newton_e2).
Definition newton_p3 : sparse_polynomial :=
  sparse_add
    (sparse_sub (sparse_mul newton_e1 newton_p2)
      (sparse_mul newton_e2 newton_p1))
    (sparse_nsmul 3 newton_e3).
Definition newton_p4 : sparse_polynomial :=
  sparse_sub
    (sparse_add
      (sparse_sub (sparse_mul newton_e1 newton_p3)
        (sparse_mul newton_e2 newton_p2))
      (sparse_mul newton_e3 newton_p1))
    (sparse_nsmul 4 newton_e4).
Definition newton_p5 : sparse_polynomial :=
  sparse_add
    (sparse_sub
      (sparse_add
        (sparse_sub (sparse_mul newton_e1 newton_p4)
          (sparse_mul newton_e2 newton_p3))
        (sparse_mul newton_e3 newton_p2))
      (sparse_mul newton_e4 newton_p1))
    (sparse_nsmul 5 newton_e5).
Definition newton_p6 : sparse_polynomial :=
  sparse_sub
    (sparse_add
      (sparse_sub
        (sparse_add
          (sparse_sub (sparse_mul newton_e1 newton_p5)
            (sparse_mul newton_e2 newton_p4))
          (sparse_mul newton_e3 newton_p3))
        (sparse_mul newton_e4 newton_p2))
      (sparse_mul newton_e5 newton_p1))
    (sparse_nsmul 6 newton_e6).

Record newton_state := NewtonState {
  newton_s1 : sparse_polynomial;
  newton_s2 : sparse_polynomial;
  newton_s3 : sparse_polynomial;
  newton_s4 : sparse_polynomial;
  newton_s5 : sparse_polynomial;
  newton_s6 : sparse_polynomial
}.

Definition newton_initial_state : newton_state :=
  NewtonState newton_p1 newton_p2 newton_p3
    newton_p4 newton_p5 newton_p6.

Definition newton_next (s : newton_state) : sparse_polynomial :=
  sparse_sub
    (sparse_add
      (sparse_sub
        (sparse_add
          (sparse_sub (sparse_mul newton_e1 (newton_s6 s))
            (sparse_mul newton_e2 (newton_s5 s)))
          (sparse_mul newton_e3 (newton_s4 s)))
        (sparse_mul newton_e4 (newton_s3 s)))
      (sparse_mul newton_e5 (newton_s2 s)))
    (sparse_mul newton_e6 (newton_s1 s)).

Definition newton_step (s : newton_state) : newton_state :=
  NewtonState (newton_s2 s) (newton_s3 s) (newton_s4 s)
    (newton_s5 s) (newton_s6 s) (newton_next s).

Fixpoint newton_iterate (n : nat) (s : newton_state) : newton_state :=
  if n is n'.+1 then newton_iterate n' (newton_step s) else s.

Definition newton_sparse_power (n : nat) : sparse_polynomial :=
  if n is n'.+1 then newton_s1 (newton_iterate n' newton_initial_state)
  else sparse_nsmul 6 (sparse_const 1).

Definition elementary_values (roots : 6.-tuple R) : 6.-tuple R :=
  [tuple root_esymm roots i | i < 6].

Lemma tnth_elementary_values roots i :
  tnth (elementary_values roots) i = root_esymm roots i.
Proof. by rewrite /elementary_values tnth_mktuple. Qed.

Definition newton_state_correct
    (roots : 6.-tuple R) (n : nat) (s : newton_state) : Prop :=
  sparse_eval_ring (elementary_values roots) (newton_s1 s) =
      root_power_sum roots (n + 1) /\
  sparse_eval_ring (elementary_values roots) (newton_s2 s) =
      root_power_sum roots (n + 2) /\
  sparse_eval_ring (elementary_values roots) (newton_s3 s) =
      root_power_sum roots (n + 3) /\
  sparse_eval_ring (elementary_values roots) (newton_s4 s) =
      root_power_sum roots (n + 4) /\
  sparse_eval_ring (elementary_values roots) (newton_s5 s) =
      root_power_sum roots (n + 5) /\
  sparse_eval_ring (elementary_values roots) (newton_s6 s) =
      root_power_sum roots (n + 6).

Lemma newton_e1_eval roots :
  sparse_eval_ring (elementary_values roots) newton_e1 =
    root_esymm roots ord0.
Proof. by rewrite /newton_e1 sparse_eval_ring_var tnth_elementary_values. Qed.

Lemma newton_e2_eval roots :
  sparse_eval_ring (elementary_values roots) newton_e2 =
    root_esymm roots (inord 1).
Proof. by rewrite /newton_e2 sparse_eval_ring_var tnth_elementary_values. Qed.

Lemma newton_e3_eval roots :
  sparse_eval_ring (elementary_values roots) newton_e3 =
    root_esymm roots (inord 2).
Proof. by rewrite /newton_e3 sparse_eval_ring_var tnth_elementary_values. Qed.

Lemma newton_e4_eval roots :
  sparse_eval_ring (elementary_values roots) newton_e4 =
    root_esymm roots (inord 3).
Proof. by rewrite /newton_e4 sparse_eval_ring_var tnth_elementary_values. Qed.

Lemma newton_e5_eval roots :
  sparse_eval_ring (elementary_values roots) newton_e5 =
    root_esymm roots (inord 4).
Proof. by rewrite /newton_e5 sparse_eval_ring_var tnth_elementary_values. Qed.

Lemma newton_e6_eval roots :
  sparse_eval_ring (elementary_values roots) newton_e6 =
    root_esymm roots (inord 5).
Proof. by rewrite /newton_e6 sparse_eval_ring_var tnth_elementary_values. Qed.

Lemma newton_p1_eval roots :
  sparse_eval_ring (elementary_values roots) newton_p1 =
    root_power_sum roots 1.
Proof. by rewrite /newton_p1 newton_e1_eval root_power_sum_one. Qed.

Lemma newton_p2_eval roots :
  sparse_eval_ring (elementary_values roots) newton_p2 =
    root_power_sum roots 2.
Proof.
rewrite /newton_p2 sparse_eval_ring_sub sparse_eval_ring_mul
  sparse_eval_ring_nsmul newton_e1_eval newton_e2_eval.
by rewrite root_power_sum_two root_power_sum_one.
Qed.

Lemma newton_p3_eval roots :
  sparse_eval_ring (elementary_values roots) newton_p3 =
    root_power_sum roots 3.
Proof.
rewrite /newton_p3 sparse_eval_ring_add sparse_eval_ring_sub
  !sparse_eval_ring_mul sparse_eval_ring_nsmul
  newton_e1_eval newton_e2_eval newton_e3_eval
  newton_p2_eval.
by rewrite root_power_sum_three root_power_sum_one.
Qed.

Lemma newton_p4_eval roots :
  sparse_eval_ring (elementary_values roots) newton_p4 =
    root_power_sum roots 4.
Proof.
rewrite /newton_p4.
repeat first
  [ rewrite newton_p3_eval | rewrite newton_p2_eval
  | rewrite newton_e1_eval | rewrite newton_e2_eval
  | rewrite newton_e3_eval | rewrite newton_e4_eval
  | rewrite sparse_eval_ring_sub | rewrite sparse_eval_ring_nsmul
  | rewrite sparse_eval_ring_mul | rewrite sparse_eval_ring_add ].
by rewrite root_power_sum_four root_power_sum_one.
Qed.

Lemma newton_p5_eval roots :
  sparse_eval_ring (elementary_values roots) newton_p5 =
    root_power_sum roots 5.
Proof.
rewrite /newton_p5.
repeat first
  [ rewrite newton_p4_eval | rewrite newton_p3_eval
  | rewrite newton_p2_eval
  | rewrite newton_e1_eval | rewrite newton_e2_eval
  | rewrite newton_e3_eval | rewrite newton_e4_eval
  | rewrite newton_e5_eval | rewrite sparse_eval_ring_sub
  | rewrite sparse_eval_ring_nsmul | rewrite sparse_eval_ring_mul
  | rewrite sparse_eval_ring_add ].
by rewrite root_power_sum_five root_power_sum_one.
Qed.

Lemma newton_p6_eval roots :
  sparse_eval_ring (elementary_values roots) newton_p6 =
    root_power_sum roots 6.
Proof.
rewrite /newton_p6.
repeat first
  [ rewrite newton_p5_eval | rewrite newton_p4_eval
  | rewrite newton_p3_eval | rewrite newton_p2_eval
  | rewrite newton_e1_eval | rewrite newton_e2_eval
  | rewrite newton_e3_eval | rewrite newton_e4_eval
  | rewrite newton_e5_eval | rewrite newton_e6_eval
  | rewrite sparse_eval_ring_sub | rewrite sparse_eval_ring_nsmul
  | rewrite sparse_eval_ring_mul | rewrite sparse_eval_ring_add ].
by rewrite root_power_sum_six root_power_sum_one.
Qed.

Lemma newton_initial_state_correct roots :
  newton_state_correct roots 0 newton_initial_state.
Proof.
rewrite /newton_state_correct /newton_initial_state /=.
by rewrite newton_p1_eval newton_p2_eval newton_p3_eval
  newton_p4_eval newton_p5_eval newton_p6_eval.
Qed.

Lemma newton_next_eval roots n s :
  newton_state_correct roots n s ->
  sparse_eval_ring (elementary_values roots) (newton_next s) =
    root_power_sum roots (n + 7).
Proof.
move=> [h1 [h2 [h3 [h4 [h5 h6]]]]].
rewrite /newton_next.
repeat first
  [ rewrite sparse_eval_ring_sub | rewrite sparse_eval_ring_mul
  | rewrite sparse_eval_ring_add | rewrite newton_e1_eval
  | rewrite newton_e2_eval | rewrite newton_e3_eval
  | rewrite newton_e4_eval | rewrite newton_e5_eval
  | rewrite newton_e6_eval ].
rewrite h1 h2 h3 h4 h5 h6.
symmetry.
have hr := root_power_sum_recurrence roots (n + 1).
replace (n + 7)%N with (n + 1 + 6)%N
  by exact: esym (addnA n 1 6).
replace (n + 6)%N with (n + 1 + 5)%N
  by exact: esym (addnA n 1 5).
replace (n + 5)%N with (n + 1 + 4)%N
  by exact: esym (addnA n 1 4).
replace (n + 4)%N with (n + 1 + 3)%N
  by exact: esym (addnA n 1 3).
replace (n + 3)%N with (n + 1 + 2)%N
  by exact: esym (addnA n 1 2).
replace (n + 2)%N with (n + 1 + 1)%N
  by exact: esym (addnA n 1 1).
exact hr.
Qed.

Lemma newton_step_correct roots n s :
  newton_state_correct roots n s ->
  newton_state_correct roots n.+1 (newton_step s).
Proof.
move=> hs; have hnext := newton_next_eval hs.
move: hs=> [h1 [h2 [h3 [h4 [h5 h6]]]]].
rewrite /newton_state_correct /newton_step /=.
repeat split.
- rewrite h2; f_equal; by rewrite addSn addnS.
- rewrite h3; f_equal; by rewrite addSn addnS.
- rewrite h4; f_equal; by rewrite addSn addnS.
- rewrite h5; f_equal; by rewrite addSn addnS.
- rewrite h6; f_equal; by rewrite addSn addnS.
- rewrite hnext; f_equal; by rewrite addSn addnS.
Qed.

Lemma newton_iterate_correct roots k n s :
  newton_state_correct roots n s ->
  newton_state_correct roots (n + k) (newton_iterate k s).
Proof.
elim: k n s=> [|k ih] n s hs /=.
- have heq : (n + 0)%N = n by rewrite addn0.
  by rewrite heq.
- have hstep := newton_step_correct hs.
  have hrec := ih n.+1 (newton_step s) hstep.
  have heq : (n + k.+1)%N = (n.+1 + k)%N
    by rewrite addnS addSn.
  by rewrite heq.
Qed.

Lemma root_power_sum_zero (roots : 6.-tuple R) :
  root_power_sum roots 0 = 6%:R.
Proof.
rewrite /root_power_sum.
under eq_bigr do rewrite expr0.
by rewrite !big_ord_recl big_ord0 /= !addr0.
Qed.

Theorem newton_sparse_power_correct roots n :
  sparse_eval_ring (elementary_values roots) (newton_sparse_power n) =
    root_power_sum roots n.
Proof.
case: n=> [|n].
- rewrite /newton_sparse_power sparse_eval_ring_nsmul
    sparse_eval_ring_const rmorph1 mulr1.
  by rewrite root_power_sum_zero.
- rewrite /newton_sparse_power /=.
  have hi := newton_initial_state_correct roots.
  have hit := newton_iterate_correct n hi.
  move: hit=> [h1 _].
  rewrite h1; f_equal; by rewrite add0n addn1.
Qed.

(** Substituting the executable Newton powers into the Möbius formula gives a
    direct sparse polynomial for every injective monomial orbit. *)
Fixpoint sparse_sum (ps : seq sparse_polynomial) : sparse_polynomial :=
  if ps is p :: ps' then sparse_add p (sparse_sum ps') else sparse_zero.

Lemma sparse_eval_ring_sum values ps :
  sparse_eval_ring values (sparse_sum ps) =
    \sum_(p <- ps) sparse_eval_ring values p.
Proof.
elim: ps=> [|p ps ih] /=.
- by rewrite sparse_eval_ring_zero big_nil.
- by rewrite sparse_eval_ring_add ih big_cons.
Qed.

Definition newton_partition_product
    (e : sparse_exponent) (s : seq nat) : sparse_polynomial :=
  sparse_product
    [seq newton_sparse_power (block_exponent e j) |
      j <- Finite.enum (active_block s)].

Lemma newton_partition_product_correct roots e s :
  sparse_eval_ring (elementary_values roots) (newton_partition_product e s) =
    partition_power_product roots e s.
Proof.
rewrite /newton_partition_product sparse_eval_ring_product
  /partition_power_product big_map [index_enum _]unlock.
apply: eq_bigr=> j _.
exact: newton_sparse_power_correct.
Qed.

Definition newton_weighted_partition
    (e : sparse_exponent) (s : seq nat) : sparse_polynomial :=
  sparse_sub
    (sparse_nsmul (partition_mobius_positive s)
      (newton_partition_product e s))
    (sparse_nsmul (partition_mobius_negative s)
      (newton_partition_product e s)).

Lemma newton_weighted_partition_correct roots e s :
  sparse_eval_ring (elementary_values roots)
      (newton_weighted_partition e s) =
    @partition_ring_weight R s * partition_power_product roots e s.
Proof.
rewrite /newton_weighted_partition sparse_eval_ring_sub
  !sparse_eval_ring_nsmul newton_partition_product_correct
  /partition_ring_weight mulrBl.
reflexivity.
Qed.

Definition newton_mobius_orbit (e : sparse_exponent) : sparse_polynomial :=
  sparse_sum
    [seq newton_weighted_partition e s | s <- partition_codes].

Lemma newton_mobius_orbit_formula roots e :
  sparse_eval_ring (elementary_values roots) (newton_mobius_orbit e) =
    mobius_power_sum_formula roots e.
Proof.
rewrite /newton_mobius_orbit sparse_eval_ring_sum
  /mobius_power_sum_formula big_map.
apply: eq_bigr=> s _.
exact: newton_weighted_partition_correct.
Qed.

Theorem newton_mobius_orbit_correct roots e :
  sparse_eval_ring (elementary_values roots) (newton_mobius_orbit e) =
    injective_assignment_sum roots e.
Proof.
rewrite newton_mobius_orbit_formula.
exact: esym (injective_assignment_sum_power_formula roots e).
Qed.

(** The preceding construction acts on one monomial.  Applying it to every
    term gives an executable Reynolds sum for an arbitrary sparse polynomial.
    This is deliberately the *sum* over the 720 permutations, rather than an
    average, so the construction remains integral and needs no division. *)
Definition assignment_values
    (roots : 6.-tuple R) (a : root_assignment) : 6.-tuple R :=
  [tuple tnth roots (a i) | i < 6].

Lemma exponent_value_ring_assignment roots a e :
  exponent_value_ring (assignment_values roots a) e =
    assignment_monomial roots e a.
Proof.
rewrite /exponent_value_ring /assignment_values /assignment_monomial.
apply: eq_bigr=> i _.
by rewrite tnth_mktuple.
Qed.

Definition injective_assignment_polynomial_sum
    (roots : 6.-tuple R) (p : sparse_polynomial) : R :=
  \sum_(a : root_assignment | code_injectiveb (assignment_code a))
    sparse_eval_ring (assignment_values roots a) p.

Definition newton_symmetrize_term (t : sparse_term) : sparse_polynomial :=
  sparse_mul (sparse_const t.1) (newton_mobius_orbit t.2).

Definition newton_symmetrize (p : sparse_polynomial) : sparse_polynomial :=
  sparse_sum (map newton_symmetrize_term p).

Lemma newton_symmetrize_term_correct roots t :
  sparse_eval_ring (elementary_values roots) (newton_symmetrize_term t) =
    (t.1)%:~R * injective_assignment_sum roots t.2.
Proof.
by rewrite /newton_symmetrize_term sparse_eval_ring_mul
  sparse_eval_ring_const newton_mobius_orbit_correct.
Qed.

Theorem newton_symmetrize_correct roots p :
  sparse_eval_ring (elementary_values roots) (newton_symmetrize p) =
    injective_assignment_polynomial_sum roots p.
Proof.
rewrite /newton_symmetrize sparse_eval_ring_sum big_map
  /injective_assignment_polynomial_sum /injective_assignment_sum.
under [LHS]eq_bigr=> t ht do rewrite newton_symmetrize_term_correct.
under [LHS]eq_bigr=> t ht do rewrite big_distrr.
rewrite exchange_big.
apply: eq_bigr=> a ha.
rewrite /sparse_eval_ring.
apply: eq_bigr=> t ht.
by rewrite exponent_value_ring_assignment.
Qed.

Definition permutation_invariant_at
    (roots : 6.-tuple R) (p : sparse_polynomial) : Prop :=
  forall a : root_assignment,
    code_injectiveb (assignment_code a) ->
    sparse_eval_ring (assignment_values roots a) p =
      sparse_eval_ring roots p.

Lemma assignment_code_enum a :
  assignment_code a =
    [seq val (a i) | i <- Finite.enum root_index].
Proof.
rewrite /assignment_code /six_naturals -val_enum_ord -map_comp enumT.
apply: eq_map=> i.
by rewrite /comp inord_val.
Qed.

Lemma assignment_code_injectiveb a :
  code_injectiveb (assignment_code a) = injectiveb a.
Proof.
rewrite /code_injectiveb assignment_code_enum
  /injectiveb /dinjectiveb enumT.
have hmap : [seq val (a i) | i <- Finite.enum root_index] =
    map val (map a (Finite.enum root_index)).
  rewrite -map_comp.
  by apply: eq_map=> i.
rewrite hmap.
exact: (@map_inj_uniq root_index nat val val_inj
  (map a (Finite.enum root_index))).
Qed.

Theorem newton_symmetrize_invariant_correct roots p :
  permutation_invariant_at roots p ->
  sparse_eval_ring (elementary_values roots) (newton_symmetrize p) =
    720%:R * sparse_eval_ring roots p.
Proof.
move=> hinv; rewrite newton_symmetrize_correct
  /injective_assignment_polynomial_sum.
transitivity
  (\sum_(a in [set a : root_assignment | injectiveb a])
    sparse_eval_ring roots p).
- apply: eq_big.
  + move=> a; by rewrite inE assignment_code_injectiveb.
  + move=> a ha.
    apply: hinv.
    exact ha.
- rewrite sumr_const card_inj_ffuns !card_ord.
  change (sparse_eval_ring roots p *+ 720 =
    720%:R * sparse_eval_ring roots p).
  by rewrite mulr_natl.
Qed.

End RingEvaluation.

End PolynomialFormulasSexticNewtonPowerSums.
