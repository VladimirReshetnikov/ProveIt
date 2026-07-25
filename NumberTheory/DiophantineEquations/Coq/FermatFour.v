(*
  Coq counterpart of DiophantineEquations.FermatFour.

  The Lean file imports mathlib's full descent proof of Fermat's Last Theorem
  for exponent 4 (`not_fermat_42` / `fermatLastTheoremFour`) and exposes two
  small project-local theorem names.  Coq's installed standard/contrib
  libraries do not ship an equivalent theorem, so this module constructs the
  classical Fermat double descent from scratch: a number-theory toolkit
  (prime divisors, coprime factors of squares), the parametrization of
  primitive Pythagorean triples, and the odd-even descent core.

  The development is layered.  Reduction theorems relate three descent-step
  granularities (general, mixed-parity, odd-even) and derive the no-solution
  statement from any of them; `Fermat42_odd_even_descent_step_holds` then
  proves the strongest granularity outright, and the final theorems export
  Fermat's Last Theorem for exponent 4 with no hypotheses:
  `fermat_four_no_positive_nat_solutions` (natural-number form, matching the
  Lean theorem name) and `fermat_four_no_square_right_int_solutions` (the
  stronger integer form with a square right-hand side).
*)

From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import ZArith Znumtheory.
From Stdlib Require Import Wellfounded.
From Stdlib Require Import Lia Ring.

Open Scope Z_scope.

Module LeanProofs.
Module FermatFour.

Definition Fermat42 (a b c : Z) : Prop :=
  a <> 0 /\ b <> 0 /\ (a ^ 4 + b ^ 4 = c ^ 2)%Z.

Definition PythagoreanTriple (x y z : Z) : Prop :=
  (x ^ 2 + y ^ 2 = z ^ 2)%Z.

Definition cMeasure (c : Z) : nat :=
  Z.to_nat (Z.abs c).

Definition Fermat42_descent_step : Prop :=
  forall a b c : Z,
    Fermat42 a b c ->
    exists a' b' c' : Z,
      Fermat42 a' b' c' /\ (cMeasure c' < cMeasure c)%nat.

Definition Fermat42_mixed_parity_descent_step : Prop :=
  forall a b c : Z,
    Fermat42 a b c ->
    (Z.Odd a /\ Z.Even b \/ Z.Even a /\ Z.Odd b) ->
    exists a' b' c' : Z,
      Fermat42 a' b' c' /\ (cMeasure c' < cMeasure c)%nat.

Definition Fermat42_odd_even_descent_step : Prop :=
  forall a b c : Z,
    Fermat42 a b c ->
    Z.Odd a ->
    Z.Even b ->
    exists a' b' c' : Z,
      Fermat42 a' b' c' /\ (cMeasure c' < cMeasure c)%nat.

Definition Fermat42_descent_statement : Prop :=
  forall a b c : Z, a <> 0 -> b <> 0 -> ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).

Theorem Fermat42_comm {a b c : Z} :
    Fermat42 a b c <-> Fermat42 b a c.
Proof.
  unfold Fermat42.
  split.
  - intros (ha & hb & h).
    repeat split; try assumption.
    rewrite Z.add_comm.
    exact h.
  - intros (hb & ha & h).
    repeat split; try assumption.
    rewrite Z.add_comm.
    exact h.
Qed.

Theorem Fermat42_scale {a b c k : Z} (hk : k <> 0) :
    Fermat42 a b c <-> Fermat42 (k * a) (k * b) (k ^ 2 * c).
Proof.
  unfold Fermat42.
  split.
  - intros (ha & hb & h).
    repeat split.
    + intros hka. apply Z.mul_eq_0 in hka as [hk0 | ha0]; tauto.
    + intros hkb. apply Z.mul_eq_0 in hkb as [hk0 | hb0]; tauto.
    + replace ((k * a) ^ 4 + (k * b) ^ 4) with
        (k ^ 4 * (a ^ 4 + b ^ 4)) by ring.
      replace ((k ^ 2 * c) ^ 2) with (k ^ 4 * c ^ 2) by ring.
      now rewrite h.
  - intros (hka & hkb & h).
    repeat split.
    + intros ha. subst a. rewrite Z.mul_0_r in hka. contradiction.
    + intros hb. subst b. rewrite Z.mul_0_r in hkb. contradiction.
    + apply (Z.mul_cancel_l _ _ (k ^ 4)).
      { apply Z.pow_nonzero; lia. }
      replace (k ^ 4 * (a ^ 4 + b ^ 4)) with
        ((k * a) ^ 4 + (k * b) ^ 4) by ring.
      replace (k ^ 4 * c ^ 2) with ((k ^ 2 * c) ^ 2) by ring.
      exact h.
Qed.

Theorem Fermat42_pythagorean_squares {a b c : Z} (h : Fermat42 a b c) :
    PythagoreanTriple (a ^ 2) (b ^ 2) c.
Proof.
  destruct h as (_ & _ & h).
  unfold PythagoreanTriple.
  rewrite <- h.
  ring.
Qed.

Lemma odd_square_mod4 (z : Z) :
    Z.odd z = true -> (z ^ 2) mod 4 = 1.
Proof.
  intro hz.
  pose proof (Z.div2_odd z) as hdecomp.
  rewrite hz in hdecomp.
  change (Z.b2z true) with 1 in hdecomp.
  rewrite hdecomp.
  replace ((2 * Z.div2 z + 1) ^ 2) with
    (1 + (Z.div2 z * Z.div2 z + Z.div2 z) * 4) by ring.
  rewrite Z.mod_add by discriminate.
  apply Z.mod_small.
  lia.
Qed.

Lemma odd_pow4_mod4 (z : Z) :
    Z.odd z = true -> (z ^ 4) mod 4 = 1.
Proof.
  intro hz.
  replace (z ^ 4) with ((z ^ 2) * (z ^ 2)) by ring.
  rewrite Zmult_mod.
  rewrite odd_square_mod4 by exact hz.
  reflexivity.
Qed.

Lemma square_mod4_ne_two (z : Z) :
    (z ^ 2) mod 4 <> 2.
Proof.
  replace (z ^ 2) with (z * z) by ring.
  rewrite Zmult_mod.
  pose proof (Z.mod_pos_bound z 4 ltac:(lia)) as hz.
  remember (z mod 4) as r.
  assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3) by lia.
  destruct H as [-> | [-> | [-> | ->]]]; compute; discriminate.
Qed.

Theorem Fermat42_not_both_odd {a b c : Z} (h : Fermat42 a b c) :
    ~ (Z.odd a = true /\ Z.odd b = true).
Proof.
  intros (haodd & hbodd).
  destruct h as (_ & _ & heq).
  assert (hmod : (c ^ 2) mod 4 = 2).
  { rewrite <- heq.
    rewrite (Zplus_mod (a ^ 4) (b ^ 4) 4).
    rewrite odd_pow4_mod4 by exact haodd.
    rewrite odd_pow4_mod4 by exact hbodd.
    reflexivity. }
  exact (square_mod4_ne_two c hmod).
Qed.

Lemma pow4_pos (a : Z) (ha : a <> 0) : 0 < a ^ 4.
Proof.
  assert (hnonneg : 0 <= a ^ 4).
  { apply Z.pow_even_nonneg. exists 2. reflexivity. }
  assert (hnz : a ^ 4 <> 0).
  { apply Z.pow_nonzero; lia. }
  lia.
Qed.

Theorem Fermat42_c_ne_zero {a b c : Z} (h : Fermat42 a b c) :
    c <> 0.
Proof.
  intros hc.
  destruct h as (ha & hb & heq).
  subst c.
  assert (ha4 : 0 < a ^ 4) by now apply pow4_pos.
  assert (hb4 : 0 < b ^ 4) by now apply pow4_pos.
  nia.
Qed.

Lemma square_mod16_zero_mod4_zero (z : Z) :
    (z ^ 2) mod 16 = 0 -> z mod 4 = 0.
Proof.
  intro h.
  replace (z ^ 2) with (z * z) in h by ring.
  rewrite Zmult_mod in h.
  remember (z mod 16) as r eqn:Hr.
  assert (hz4 : z mod 4 = r mod 4).
  { symmetry.
    rewrite Hr.
    apply Z.mod_mod_divide.
    exists 4. ring. }
  pose proof (Z.mod_pos_bound z 16 ltac:(lia)) as hz.
  rewrite <- Hr in hz.
  assert (hrange : r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/
          r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/
          r = 8 \/ r = 9 \/ r = 10 \/ r = 11 \/
          r = 12 \/ r = 13 \/ r = 14 \/ r = 15) by lia.
  destruct hrange as [-> | [-> | [-> | [-> |
    [-> | [-> | [-> | [-> |
    [-> | [-> | [-> | [-> |
    [-> | [-> | [-> | ->]]]]]]]]]]]]]]];
    try (compute in h; discriminate);
    rewrite hz4; reflexivity.
Qed.

Lemma square_mod16_zero_div4 (z : Z) :
    (z ^ 2) mod 16 = 0 -> exists q : Z, z = 4 * q.
Proof.
  intro h.
  pose proof (square_mod16_zero_mod4_zero z h) as hz4.
  pose proof (proj1 (Z.mod_divide z 4 ltac:(lia)) hz4) as hdiv.
  destruct hdiv as [q hq].
  exists q.
  rewrite hq.
  ring.
Qed.

Lemma cMeasure_quarter_lt {c c' : Z} :
    c = 4 * c' -> c <> 0 -> (cMeasure c' < cMeasure c)%nat.
Proof.
  intros hc hc0.
  unfold cMeasure.
  apply Z2Nat.inj_lt; try apply Z.abs_nonneg.
  rewrite hc, Z.abs_mul.
  change (Z.abs 4) with 4.
  assert (hc' : c' <> 0).
  { intro hzero. apply hc0. rewrite hc, hzero. ring. }
  pose proof (proj2 (Z.abs_pos c') hc') as hcpos.
  lia.
Qed.

Theorem Fermat42_both_even_descent {a b c : Z} (h : Fermat42 a b c)
    (haeven : Z.Even a) (hbeven : Z.Even b) :
    exists a' b' c' : Z,
      Fermat42 a' b' c' /\ (cMeasure c' < cMeasure c)%nat.
Proof.
  pose proof (Fermat42_c_ne_zero h) as hcne.
  destruct h as (ha & hb & heq).
  destruct haeven as [a' haeq].
  destruct hbeven as [b' hbeq].
  assert (hcmod : (c ^ 2) mod 16 = 0).
  { rewrite <- heq.
    rewrite haeq, hbeq.
    replace ((2 * a') ^ 4 + (2 * b') ^ 4) with
      ((a' ^ 4 + b' ^ 4) * 16) by ring.
    rewrite Z.mod_mul by discriminate.
    reflexivity. }
  destruct (square_mod16_zero_div4 c hcmod) as [c' hceq].
  exists a', b', c'.
  split.
  - apply (proj2 (Fermat42_scale (a:=a') (b:=b') (c:=c') (k:=2) ltac:(lia))).
    unfold Fermat42.
    repeat split.
    + intro hzero. apply ha. rewrite haeq, hzero. ring.
    + intro hzero. apply hb. rewrite hbeq, hzero. ring.
    + change (2 ^ 2) with 4.
      rewrite <- haeq, <- hbeq, <- hceq.
      exact heq.
  - exact (cMeasure_quarter_lt hceq hcne).
Qed.

Theorem Fermat42_both_even_descent_bool {a b c : Z} (h : Fermat42 a b c)
    (haeven : Z.even a = true) (hbeven : Z.even b = true) :
    exists a' b' c' : Z,
      Fermat42 a' b' c' /\ (cMeasure c' < cMeasure c)%nat.
Proof.
  exact (Fermat42_both_even_descent h
    (proj1 (Z.even_spec a) haeven)
    (proj1 (Z.even_spec b) hbeven)).
Qed.

Lemma odd_true_of_even_false (z : Z) :
    Z.even z = false -> Z.odd z = true.
Proof.
  intro hz.
  rewrite <- Z.negb_even.
  now rewrite hz.
Qed.

Theorem Fermat42_descent_step_of_mixed_parity
    (mixed_descent : Fermat42_mixed_parity_descent_step) :
    Fermat42_descent_step.
Proof.
  intros a b c h.
  destruct (Z.even a) eqn:haeven;
    destruct (Z.even b) eqn:hbeven.
  - exact (Fermat42_both_even_descent_bool h haeven hbeven).
  - exact (mixed_descent a b c h (or_intror
      (conj
        (proj1 (Z.even_spec a) haeven)
        (proj1 (Z.odd_spec b) (odd_true_of_even_false b hbeven))))).
  - exact (mixed_descent a b c h (or_introl
      (conj
        (proj1 (Z.odd_spec a) (odd_true_of_even_false a haeven))
        (proj1 (Z.even_spec b) hbeven)))).
  - exfalso.
    apply (Fermat42_not_both_odd h).
    split; now apply odd_true_of_even_false.
Qed.

Theorem Fermat42_mixed_parity_descent_step_of_odd_even
    (odd_even_descent : Fermat42_odd_even_descent_step) :
    Fermat42_mixed_parity_descent_step.
Proof.
  intros a b c h hparity.
  destruct hparity as [(haodd & hbeven) | (haeven & hbodd)].
  - exact (odd_even_descent a b c h haodd hbeven).
  - exact (odd_even_descent b a c
      (proj1 Fermat42_comm h) hbodd haeven).
Qed.

Theorem Fermat42_descent_step_of_odd_even
    (odd_even_descent : Fermat42_odd_even_descent_step) :
    Fermat42_descent_step.
Proof.
  exact (Fermat42_descent_step_of_mixed_parity
    (Fermat42_mixed_parity_descent_step_of_odd_even odd_even_descent)).
Qed.

Theorem no_Fermat42_of_descent (descent : Fermat42_descent_step) :
    forall a b c : Z, ~ Fermat42 a b c.
Proof.
  pose (P := fun n : nat => forall a b c : Z,
    cMeasure c = n -> ~ Fermat42 a b c).
  enough (H : forall n : nat, P n).
  { intros a b c h. exact (H (cMeasure c) a b c eq_refl h). }
  apply (well_founded_induction lt_wf P).
  unfold P.
  intros n ih a b c hc h.
  destruct (descent a b c h) as (a' & b' & c' & h' & hlt).
  assert (hlt_n : (cMeasure c' < n)%nat) by lia.
  exact (ih (cMeasure c') hlt_n a' b' c' eq_refl h').
Qed.

Theorem Fermat42_descent_statement_of_step
    (descent : Fermat42_descent_step) :
    Fermat42_descent_statement.
Proof.
  intros a b c ha hb heq.
  exact (no_Fermat42_of_descent descent a b c (conj ha (conj hb heq))).
Qed.

Theorem Fermat42_descent_statement_of_mixed_parity_step
    (mixed_descent : Fermat42_mixed_parity_descent_step) :
    Fermat42_descent_statement.
Proof.
  exact (Fermat42_descent_statement_of_step
    (Fermat42_descent_step_of_mixed_parity mixed_descent)).
Qed.

Theorem Fermat42_descent_statement_of_odd_even_step
    (odd_even_descent : Fermat42_odd_even_descent_step) :
    Fermat42_descent_statement.
Proof.
  exact (Fermat42_descent_statement_of_step
    (Fermat42_descent_step_of_odd_even odd_even_descent)).
Qed.

(* Generic public wrappers over any proof of the descent statement.  The
   three assumption granularities below instantiate these, so the nat-to-Z
   transport is written once. *)

Theorem fermat_four_no_square_right_int_solutions_of_statement
    (hstmt : Fermat42_descent_statement)
    {a b c : Z} (ha : a <> 0) (hb : b <> 0) :
    ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).
Proof.
  exact (hstmt a b c ha hb).
Qed.

Theorem fermat_four_no_positive_nat_solutions_of_statement
    (hstmt : Fermat42_descent_statement)
    {a b c : nat}
    (ha : (0 < a)%nat) (hb : (0 < b)%nat) (_hc : (0 < c)%nat) :
    (a ^ 4 + b ^ 4 <> c ^ 4)%nat.
Proof.
  intro hnat.
  pose proof (f_equal Z.of_nat hnat) as hz.
  rewrite Nat2Z.inj_add in hz.
  repeat rewrite Nat2Z.inj_pow in hz.
  change (Z.of_nat 4) with 4 in hz.
  apply (hstmt (Z.of_nat a) (Z.of_nat b) ((Z.of_nat c) ^ 2)).
  - lia.
  - lia.
  - rewrite hz.
    ring.
Qed.

(* ==================== number-theory toolkit ====================

   Everything needed for the classical descent: existence of prime divisors,
   the fact that coprime factors of a perfect square are squares, and the
   descent of divisibility along squares. *)

Lemma exists_prime_divisor (n : Z) (hn : 1 < n) :
    exists p : Z, prime p /\ (p | n).
Proof.
  revert hn.
  assert (hgen : forall m : Z, 0 <= m ->
    1 < m -> exists p : Z, prime p /\ (p | m)).
  { apply (Z_lt_induction
      (fun m => 1 < m -> exists p : Z, prime p /\ (p | m))).
    intros x IH hx.
    destruct (prime_dec x) as [hp | hnp].
    - exists x. split; [exact hp | apply Z.divide_refl].
    - destruct (not_prime_divide x hx hnp) as (d & hd & hdiv).
      destruct (IH d ltac:(lia) ltac:(lia)) as (p & hp & hpd).
      exists p. split; [exact hp | exact (Z.divide_trans _ _ _ hpd hdiv)]. }
  intro hn. apply hgen; lia.
Qed.

Lemma common_prime_of_gcd_not_one (u v : Z)
    (hne : Z.gcd u v <> 1) (hu : u <> 0) :
    exists p : Z, prime p /\ (p | u) /\ (p | v).
Proof.
  assert (hg : 1 < Z.gcd u v).
  { pose proof (Z.gcd_nonneg u v).
    assert (Z.gcd u v <> 0)
      by (intro h0; apply hu; exact (Z.gcd_eq_0_l _ _ h0)).
    lia. }
  destruct (exists_prime_divisor _ hg) as (p & hp & hpd).
  exists p.
  split; [exact hp |].
  split; eapply Z.divide_trans;
    eauto using Z.gcd_divide_l, Z.gcd_divide_r.
Qed.

(* The key multiplicative fact behind the parametrization of Pythagorean
   triples: a nonnegative factor of a perfect square that is coprime to its
   cofactor is itself a perfect square.  Proved by strong induction on the
   square root, peeling off one prime at a time. *)

Lemma coprime_factor_of_square_aux :
  forall w : Z, 0 <= w ->
  forall u v : Z, 0 <= u -> u * v = w ^ 2 -> Z.gcd u v = 1 ->
  exists s : Z, u = s ^ 2.
Proof.
  assert (main : forall w : Z, 0 <= w ->
    (0 <= w -> forall u v : Z, 0 <= u -> u * v = w ^ 2 -> Z.gcd u v = 1 ->
     exists s : Z, u = s ^ 2)).
  { apply (Z_lt_induction (fun w => 0 <= w ->
      forall u v : Z, 0 <= u -> u * v = w ^ 2 -> Z.gcd u v = 1 ->
      exists s : Z, u = s ^ 2)).
    intros w IH hw u v hu heq hgcd.
    destruct (Z.eq_dec u 0) as [-> | hu0].
    { exists 0. ring. }
    destruct (Z.eq_dec u 1) as [-> | hu1].
    { exists 1. ring. }
    assert (hu2 : 1 < u) by lia.
    destruct (exists_prime_divisor u hu2) as (p & hp & hpu).
    pose proof (prime_ge_2 p hp) as hp2.
    assert (hpww : (p | w * w)).
    { destruct hpu as (qu & hqu). exists (qu * v). nia. }
    assert (hpw : (p | w))
      by (destruct (prime_mult p hp w w hpww) as [h | h]; exact h).
    assert (hwpos : 0 < w).
    { destruct (Z.eq_dec w 0) as [-> | hw0]; [| lia].
      exfalso.
      assert (hv0 : v = 0) by nia.
      rewrite hv0, Z.gcd_0_r in hgcd.
      rewrite Z.abs_eq in hgcd by lia.
      lia. }
    destruct hpw as (w' & hw').
    assert (hw'pos : 0 < w') by nia.
    assert (hw'lt : w' < w) by nia.
    assert (hpv : ~ (p | v)).
    { intro hpv.
      assert (hpg : (p | Z.gcd u v)) by (apply Z.gcd_greatest; assumption).
      rewrite hgcd in hpg. apply Z.divide_1_r in hpg. lia. }
    destruct hpu as (u1 & hu1eq).
    assert (hpu1v : (p | u1 * v)).
    { exists (w' * w').
      apply (Z.mul_cancel_r _ _ p); [lia |]. nia. }
    destruct (prime_mult p hp u1 v hpu1v) as [hpu1 | habs]; [| contradiction].
    destruct hpu1 as (u2 & hu2eq).
    assert (heq2 : u2 * v = w' ^ 2).
    { apply (Z.mul_cancel_r _ _ p); [lia |]. nia. }
    assert (hu2nonneg : 0 <= u2) by nia.
    assert (hgcd2 : Z.gcd u2 v = 1).
    { assert (hd1 : (Z.gcd u2 v | u)).
      { apply Z.divide_trans with u2; [apply Z.gcd_divide_l |].
        exists (p * p). nia. }
      assert (hd : (Z.gcd u2 v | Z.gcd u v))
        by (apply Z.gcd_greatest; [exact hd1 | apply Z.gcd_divide_r]).
      rewrite hgcd in hd. apply Z.divide_1_r in hd.
      pose proof (Z.gcd_nonneg u2 v). lia. }
    destruct (IH w' ltac:(lia) ltac:(lia) u2 v hu2nonneg heq2 hgcd2)
      as (s & hs).
    exists (s * p).
    rewrite hu1eq, hu2eq, hs. ring. }
  intros w hw. exact (main w hw hw).
Qed.

Lemma coprime_square_factor (u v w : Z)
    (hu : 0 <= u) (heq : u * v = w ^ 2) (hgcd : Z.gcd u v = 1) :
    exists s : Z, 0 <= s /\ u = s ^ 2.
Proof.
  assert (heq' : u * v = (Z.abs w) ^ 2).
  { rewrite heq.
    destruct (Z.abs_spec w) as [(_ & h) | (_ & h)]; rewrite h; ring. }
  destruct (coprime_factor_of_square_aux
    (Z.abs w) (Z.abs_nonneg w) u v hu heq' hgcd) as (s & hs).
  exists (Z.abs s).
  split; [apply Z.abs_nonneg |].
  rewrite hs.
  destruct (Z.abs_spec s) as [(_ & h) | (_ & h)]; rewrite h; ring.
Qed.

Lemma divide_of_divide_square (d c : Z) (h : (d ^ 2 | c ^ 2)) : (d | c).
Proof.
  destruct (Z.eq_dec c 0) as [-> | hc].
  { apply Z.divide_0_r. }
  destruct (Z.eq_dec d 0) as [-> | hd].
  { exfalso. destruct h as (k & hk). nia. }
  set (e := Z.gcd c d).
  assert (he : e <> 0)
    by (intro h0; apply hc; exact (Z.gcd_eq_0_l _ _ h0)).
  pose proof (Z.gcd_divide_l c d) as hec.
  pose proof (Z.gcd_divide_r c d) as hed.
  fold e in hec, hed.
  destruct hec as (c' & hc').
  destruct hed as (d' & hd').
  assert (hgcd' : Z.gcd c' d' = 1).
  { pose proof (Z.gcd_div_gcd c d e he eq_refl) as hg.
    rewrite hc', hd' in hg.
    rewrite Z.div_mul in hg by exact he.
    rewrite Z.div_mul in hg by exact he.
    exact hg. }
  assert (hdd : (d' * d' | c' * c')).
  { destruct h as (k & hk).
    exists k.
    apply (Z.mul_cancel_r _ _ (e * e)); [nia |]. nia. }
  assert (hrp : rel_prime (c' * c') (d' * d')).
  { apply Zgcd_1_rel_prime in hgcd'.
    assert (h2 : rel_prime d' (c' * c'))
      by (apply rel_prime_mult; apply rel_prime_sym; assumption).
    apply rel_prime_sym in h2.
    apply rel_prime_mult; exact h2. }
  assert (hone : (d' * d' | 1)).
  { apply rel_prime_sym in hrp.
    destruct hrp as [h1 h2 hgr].
    apply (hgr (d' * d')); [apply Z.divide_refl | exact hdd]. }
  apply Z.divide_1_r in hone.
  assert (hd1 : d' = 1 \/ d' = -1) by nia.
  destruct hd1 as [hd1 | hd1]; rewrite hd'.
  - exists c'. rewrite hd1. nia.
  - exists (- c'). rewrite hd1. nia.
Qed.

Lemma gcd_sq_sq_one (a b : Z) (h : Z.gcd a b = 1) :
    Z.gcd (a ^ 2) (b ^ 2) = 1.
Proof.
  apply Zgcd_1_rel_prime.
  apply Zgcd_1_rel_prime in h.
  replace (a ^ 2) with (a * a) by ring.
  replace (b ^ 2) with (b * b) by ring.
  assert (hab2 : rel_prime a (b * b)) by (apply rel_prime_mult; assumption).
  assert (h2 : rel_prime (b * b) a) by (apply rel_prime_sym; assumption).
  apply rel_prime_sym.
  apply rel_prime_mult; assumption.
Qed.

(* ==================== parity and absolute-value helpers ==================== *)

Lemma odd_sq_form (a : Z) (h : Z.Odd a) : exists k : Z, a ^ 2 = 4 * k + 1.
Proof. destruct h as (i & hi). exists (i * i + i). nia. Qed.

Lemma even_sq_form (a : Z) (h : Z.Even a) : exists k : Z, a ^ 2 = 4 * k.
Proof. destruct h as (j & hj). exists (j * j). nia. Qed.

Lemma Odd_abs (a : Z) (h : Z.Odd a) : Z.Odd (Z.abs a).
Proof.
  destruct h as (i & hi).
  destruct (Z.abs_spec a) as [(_ & h) | (_ & h)]; rewrite h.
  - exists i. exact hi.
  - exists (- i - 1). lia.
Qed.

Lemma abs_pow4 (a : Z) : (Z.abs a) ^ 4 = a ^ 4.
Proof.
  destruct (Z.abs_spec a) as [(_ & h) | (_ & h)]; rewrite h; ring.
Qed.

Lemma abs_sq (a : Z) : (Z.abs a) ^ 2 = a ^ 2.
Proof.
  destruct (Z.abs_spec a) as [(_ & h) | (_ & h)]; rewrite h; ring.
Qed.

(* ==================== Pythagorean parametrization ====================

   The classical parametrization of primitive Pythagorean triples: if
   x^2 + y^2 = z^2 with x, y, z > 0, x odd, y even, and gcd(x, y) = 1, then
   x = m^2 - n^2, y = 2mn, z = m^2 + n^2 for coprime 0 <= n < m. *)

Lemma pythagorean_coprime_xz (x y z : Z)
    (hx : x <> 0) (heq : x ^ 2 + y ^ 2 = z ^ 2) (hgcd : Z.gcd x y = 1) :
    Z.gcd x z = 1.
Proof.
  destruct (Z.eq_dec (Z.gcd x z) 1) as [| hne]; [assumption |].
  exfalso.
  destruct (common_prime_of_gcd_not_one x z hne hx) as (p & hp & hpx & hpz).
  assert (hpyy : (p | y * y)).
  { destruct hpx as (qx & hqx).
    destruct hpz as (qz & hqz).
    exists (qz * qz * p - qx * qx * p).
    nia. }
  destruct (prime_mult p hp y y hpyy) as [hpy | hpy];
    (assert (hdg : (p | Z.gcd x y)) by (apply Z.gcd_greatest; assumption));
    rewrite hgcd in hdg; apply Z.divide_1_r in hdg;
    pose proof (prime_ge_2 p hp); lia.
Qed.

Lemma pythagorean_param (x y z : Z)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (heq : x ^ 2 + y ^ 2 = z ^ 2)
    (hxodd : Z.Odd x) (hyeven : Z.Even y) (hgcd : Z.gcd x y = 1) :
    exists m n : Z,
      0 <= n /\ n < m /\
      x = m ^ 2 - n ^ 2 /\ y = 2 * m * n /\ z = m ^ 2 + n ^ 2 /\
      Z.gcd m n = 1.
Proof.
  assert (hgxz : Z.gcd x z = 1)
    by (apply (pythagorean_coprime_xz x y z); [lia | exact heq | exact hgcd]).
  destruct hxodd as (i & hi).
  destruct hyeven as (j & hj).
  assert (hzodd : Z.Odd z).
  { destruct (Z.Even_or_Odd z) as [(k & hk) | ho]; [exfalso; nia | exact ho]. }
  destruct hzodd as (k & hk).
  set (u := k + i + 1).
  set (v := k - i).
  assert (huvz : u + v = z) by (unfold u, v; lia).
  assert (huvx : u - v = x) by (unfold u, v; lia).
  assert (hupos : 0 < u) by (unfold u; lia).
  (* x < z from x^2 + y^2 = z^2 with y > 0; the nonlinear call is
     clear-scoped: in the full context (set-bound u, v and the parity
     equations) nia diverges. *)
  assert (hxltz : x < z) by (clear -hx hy hz heq; nia).
  assert (hvpos : 0 < v) by (unfold v; lia).
  assert (hjpos : 0 < j) by lia.
  assert (huv : u * v = j ^ 2) by (unfold u, v; nia).
  assert (hgcduv : Z.gcd u v = 1).
  { assert (hdx : (Z.gcd u v | x)).
    { rewrite <- huvx.
      apply Z.divide_sub_r; [apply Z.gcd_divide_l | apply Z.gcd_divide_r]. }
    assert (hdz : (Z.gcd u v | z)).
    { rewrite <- huvz.
      apply Z.divide_add_r; [apply Z.gcd_divide_l | apply Z.gcd_divide_r]. }
    assert (hd : (Z.gcd u v | Z.gcd x z)) by (apply Z.gcd_greatest; assumption).
    rewrite hgxz in hd. apply Z.divide_1_r in hd.
    pose proof (Z.gcd_nonneg u v). lia. }
  destruct (coprime_square_factor u v j ltac:(lia) huv hgcduv)
    as (m & hm0 & hum).
  assert (hvu : v * u = j ^ 2) by lia.
  assert (hgcdvu : Z.gcd v u = 1) by (rewrite Z.gcd_comm; exact hgcduv).
  destruct (coprime_square_factor v u j ltac:(lia) hvu hgcdvu)
    as (n & hn0 & hvn).
  assert (hj_mn : j = m * n).
  { assert (hzero : (j - m * n) * (j + m * n) = 0) by nia.
    apply Z.mul_eq_0 in hzero.
    assert (0 <= m * n) by (apply Z.mul_nonneg_nonneg; assumption).
    lia. }
  exists m, n.
  repeat split.
  - exact hn0.
  - (* n < m from m^2 - n^2 = x > 0; clear-scoped, nia diverges in the
       full context. *)
    clear -hn0 hm0 hum hvn huvx hx
    ; nia.
  - lia.
  - lia.
  - lia.
  - assert (hdm : (Z.gcd m n | u)).
    { apply Z.divide_trans with m; [apply Z.gcd_divide_l |].
      exists m. lia. }
    assert (hdn : (Z.gcd m n | v)).
    { apply Z.divide_trans with n; [apply Z.gcd_divide_r |].
      exists n. lia. }
    assert (hd : (Z.gcd m n | Z.gcd u v)) by (apply Z.gcd_greatest; assumption).
    rewrite hgcduv in hd. apply Z.divide_1_r in hd.
    pose proof (Z.gcd_nonneg m n). lia.
Qed.

(* ==================== the descent core ====================

   The classical double descent: from a coprime solution a^4 + b^4 = c^2 with
   a > 0 odd, b even, c > 0, two applications of the Pythagorean
   parametrization and three applications of the coprime-square-factor lemma
   produce a solution u^4 + v^4 = t^2 with |t| <= m < m^2 + n^2 = c. *)

Lemma Fermat42_coprime_odd_even_core (a b c : Z)
    (ha : 0 < a) (haodd : Z.Odd a) (hb : b <> 0) (hbeven : Z.Even b)
    (hc : 0 < c) (hgcd : Z.gcd a b = 1) (heq : a ^ 4 + b ^ 4 = c ^ 2) :
    exists a' b' c' : Z, Fermat42 a' b' c' /\ Z.abs c' < c.
Proof.
  assert (hx2 : (a ^ 2) ^ 2 + (b ^ 2) ^ 2 = c ^ 2) by nia.
  assert (hxpos : 0 < a ^ 2) by nia.
  assert (hypos : 0 < b ^ 2) by nia.
  assert (hxodd : Z.Odd (a ^ 2)).
  { destruct haodd as (i & hi). exists (2 * i * i + 2 * i). nia. }
  assert (hyeven : Z.Even (b ^ 2)).
  { destruct hbeven as (j & hj). exists (2 * j * j). nia. }
  assert (hgcd2 : Z.gcd (a ^ 2) (b ^ 2) = 1) by (apply gcd_sq_sq_one, hgcd).
  destruct (pythagorean_param (a ^ 2) (b ^ 2) c
    hxpos hypos hc hx2 hxodd hyeven hgcd2)
    as (m & n & hn0 & hnm & hxeq & hyeq & hzeq & hgcdmn).
  assert (hnpos : 0 < n).
  { destruct (Z.eq_dec n 0) as [hn | hn]; [| lia].
    exfalso. rewrite hn in hyeq. nia. }
  assert (hmpos : 0 < m) by lia.
  destruct (odd_sq_form a haodd) as (ka & hka).
  assert (hparity : Z.Odd m /\ Z.Even n).
  { destruct (Z.Even_or_Odd m) as [hm | hm];
      destruct (Z.Even_or_Odd n) as [(hn & hnn) | (hn & hnn)];
      [exfalso | exfalso | | exfalso].
    - destruct (even_sq_form m hm) as (km & hkm).
      destruct (even_sq_form n (ex_intro _ hn hnn)) as (kn & hkn).
      lia.
    - destruct (even_sq_form m hm) as (km & hkm).
      destruct (odd_sq_form n (ex_intro _ hn hnn)) as (kn & hkn).
      lia.
    - split; [exact hm | exact (ex_intro _ hn hnn)].
    - destruct (odd_sq_form m hm) as (km & hkm).
      destruct (odd_sq_form n (ex_intro _ hn hnn)) as (kn & hkn).
      lia. }
  destruct hparity as (hmodd & hneven).
  assert (hgcdan : Z.gcd a n = 1).
  { destruct (Z.eq_dec (Z.gcd a n) 1) as [| hne]; [assumption |].
    exfalso.
    destruct (common_prime_of_gcd_not_one a n hne ltac:(lia))
      as (p & hp & hpa & hpn).
    assert (hpmm : (p | m * m)).
    { destruct hpa as (qa & hqa).
      destruct hpn as (qn & hqn).
      exists (qa * qa * p + qn * qn * p).
      nia. }
    destruct (prime_mult p hp m m hpmm) as [hpm | hpm];
      (assert (hdg : (p | Z.gcd m n)) by (apply Z.gcd_greatest; assumption));
      rewrite hgcdmn in hdg; apply Z.divide_1_r in hdg;
      pose proof (prime_ge_2 p hp); lia. }
  assert (hx2' : a ^ 2 + n ^ 2 = m ^ 2) by lia.
  destruct (pythagorean_param a n m ha hnpos hmpos hx2' haodd hneven hgcdan)
    as (r & s & hs0 & hsr & haeq & hneq & hmeq & hgcdrs).
  destruct hbeven as (b1 & hb1).
  (* Both nonlinear goals are immediate from three facts each; nia diverges
     in the full context, so both calls are clear-scoped. *)
  assert (hprod1 : m * (r * s) = b1 ^ 2) by (clear -hyeq hb1 hneq; nia).
  assert (hrs_nonneg : 0 <= r * s) by (clear -hs0 hsr; nia).
  assert (hgcd_m_rs : Z.gcd m (r * s) = 1).
  { assert (h2 : (Z.gcd m (r * s) | n)).
    { rewrite hneq.
      replace (2 * r * s) with (2 * (r * s)) by ring.
      apply Z.divide_mul_r. apply Z.gcd_divide_r. }
    assert (hd : (Z.gcd m (r * s) | Z.gcd m n))
      by (apply Z.gcd_greatest; [apply Z.gcd_divide_l | exact h2]).
    rewrite hgcdmn in hd. apply Z.divide_1_r in hd.
    pose proof (Z.gcd_nonneg m (r * s)) as hnn.
    clear -hd hnn. lia. }
  destruct (coprime_square_factor m (r * s) b1 ltac:(clear -hmpos; lia)
    hprod1 hgcd_m_rs)
    as (t & ht0 & htm).
  assert (hprod2 : (r * s) * m = b1 ^ 2) by (clear -hprod1; lia).
  assert (hgcd_rs_m : Z.gcd (r * s) m = 1)
    by (rewrite Z.gcd_comm; exact hgcd_m_rs).
  destruct (coprime_square_factor (r * s) m b1 hrs_nonneg hprod2 hgcd_rs_m)
    as (w & hw0 & hwrs).
  destruct (coprime_square_factor r s w ltac:(clear -hs0 hsr; lia) hwrs hgcdrs)
    as (u & hu0 & hur).
  assert (hprod4 : s * r = w ^ 2) by (clear -hwrs; lia).
  assert (hgcdsr : Z.gcd s r = 1) by (rewrite Z.gcd_comm; exact hgcdrs).
  destruct (coprime_square_factor s r w hs0 hprod4 hgcdsr)
    as (v & hv0 & hvs).
  exists u, v, t.
  assert (hteq : u ^ 4 + v ^ 4 = t ^ 2).
  { rewrite htm in hmeq. rewrite hur, hvs in hmeq.
    rewrite hmeq. ring. }
  split.
  - split; [| split].
    + intro h0. clear -h0 hur hsr hs0. nia.
    + intro h0. clear -h0 hvs hneq hnpos. nia.
    + exact hteq.
  - assert (htpos : 0 < t) by (clear -htm hmpos ht0; nia).
    rewrite Z.abs_eq by lia.
    clear -htm hzeq hmpos hnpos htpos.
    nia.
Qed.

(* The unconditional primitive descent step: normalize signs, split on
   whether gcd(a, b) = 1, and use either the common-factor reduction or the
   coprime double-descent core. *)

Theorem Fermat42_odd_even_descent_step_holds :
    Fermat42_odd_even_descent_step.
Proof.
  intros a b c h haodd hbeven.
  pose proof (Fermat42_c_ne_zero h) as hcne.
  destruct h as (ha & hb & heq).
  set (a0 := Z.abs a).
  set (c0 := Z.abs c).
  assert (ha0 : 0 < a0) by (unfold a0; destruct (Z.abs_spec a); lia).
  assert (hc0 : 0 < c0) by (unfold c0; destruct (Z.abs_spec c); lia).
  assert (heq0 : a0 ^ 4 + b ^ 4 = c0 ^ 2).
  { unfold a0, c0. rewrite abs_pow4, abs_sq. exact heq. }
  assert (ha0odd : Z.Odd a0) by (apply Odd_abs, haodd).
  set (g := Z.gcd a0 b).
  assert (hgpos : 0 < g).
  { unfold g.
    pose proof (Z.gcd_nonneg a0 b).
    assert (Z.gcd a0 b <> 0)
      by (intro h0; pose proof (Z.gcd_eq_0_l _ _ h0); lia).
    lia. }
  destruct (Z.eq_dec g 1) as [hg1 | hgne].
  - destruct (Fermat42_coprime_odd_even_core a0 b c0
      ha0 ha0odd hb hbeven hc0 hg1 heq0)
      as (a' & b' & c' & hsol & hlt).
    exists a', b', c'.
    split; [exact hsol |].
    unfold cMeasure.
    apply Z2Nat.inj_lt; [apply Z.abs_nonneg | apply Z.abs_nonneg |].
    (* [hlt] bounds [Z.abs c'] by [c0 := Z.abs c] definitionally. *)
    exact hlt.
  - assert (hg2 : 2 <= g) by lia.
    pose proof (Z.gcd_divide_l a0 b) as hga.
    pose proof (Z.gcd_divide_r a0 b) as hgb.
    fold g in hga, hgb.
    destruct hga as (a1 & ha1).
    destruct hgb as (b1 & hb1).
    assert (hdiv : ((g ^ 2) ^ 2 | c0 ^ 2)).
    { exists (a1 ^ 4 + b1 ^ 4).
      rewrite <- heq0, ha1, hb1. ring. }
    destruct (divide_of_divide_square (g ^ 2) c0 hdiv) as (c1 & hc1).
    assert (heq1 : a1 ^ 4 + b1 ^ 4 = c1 ^ 2).
    { apply (Z.mul_cancel_r _ _ (g ^ 4)); [clear -hgpos; nia |].
      replace ((a1 ^ 4 + b1 ^ 4) * g ^ 4)
        with ((a1 * g) ^ 4 + (b1 * g) ^ 4) by ring.
      rewrite <- ha1, <- hb1.
      replace (c1 ^ 2 * g ^ 4) with ((c1 * g ^ 2) ^ 2) by ring.
      rewrite <- hc1.
      exact heq0. }
    exists a1, b1, c1.
    split.
    + split; [| split].
      * intro h0. clear -h0 ha1 ha0. nia.
      * intro h0. apply hb. clear -h0 hb1. nia.
      * exact heq1.
    + unfold cMeasure.
      apply Z2Nat.inj_lt; [apply Z.abs_nonneg | apply Z.abs_nonneg |].
      assert (hc1pos : 0 < c1) by (clear -hc1 hc0 hgpos; nia).
      rewrite (Z.abs_eq c1) by lia.
      unfold c0 in hc1.
      clear -hc1 hc1pos hg2.
      nia.
Qed.

(* ==================== unconditional results ====================

   The descent step is a theorem, so every parametrized statement above is
   now available unconditionally.  These are the public entry points. *)

Theorem Fermat42_descent_step_holds : Fermat42_descent_step.
Proof.
  exact (Fermat42_descent_step_of_odd_even
    Fermat42_odd_even_descent_step_holds).
Qed.

Theorem Fermat42_mixed_parity_descent_step_holds :
    Fermat42_mixed_parity_descent_step.
Proof.
  exact (Fermat42_mixed_parity_descent_step_of_odd_even
    Fermat42_odd_even_descent_step_holds).
Qed.

Theorem no_Fermat42 : forall a b c : Z, ~ Fermat42 a b c.
Proof.
  exact (no_Fermat42_of_descent Fermat42_descent_step_holds).
Qed.

Theorem Fermat42_descent_statement_holds : Fermat42_descent_statement.
Proof.
  exact (Fermat42_descent_statement_of_step Fermat42_descent_step_holds).
Qed.

(* Fermat's Last Theorem for exponent 4, right-hand side a square, over Z. *)
Theorem fermat_four_no_square_right_int_solutions
    {a b c : Z} (ha : a <> 0) (hb : b <> 0) :
    ~ ((a ^ 4 + b ^ 4)%Z = (c ^ 2)%Z).
Proof.
  exact (fermat_four_no_square_right_int_solutions_of_statement
    Fermat42_descent_statement_holds ha hb).
Qed.

(* Fermat's Last Theorem for exponent 4 over the positive naturals. *)
Theorem fermat_four_no_positive_nat_solutions
    {a b c : nat}
    (ha : (0 < a)%nat) (hb : (0 < b)%nat) (hc : (0 < c)%nat) :
    (a ^ 4 + b ^ 4 <> c ^ 4)%nat.
Proof.
  exact (fermat_four_no_positive_nat_solutions_of_statement
    Fermat42_descent_statement_holds ha hb hc).
Qed.

End FermatFour.
End LeanProofs.
