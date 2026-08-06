From Stdlib Require Import Arith.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** A reusable finite mixed-radix identity.  The least-significant digit of
    [code] is at position zero, exactly as in the direct Mu-recursive
    evaluators. *)
Module PolynomialFormulasSexticMuRecMixedRadixSemantics.

Section RadixBijection.

Variables b m : nat.

Lemma radix_join_bound (digit : 'I_b) (rest : 'I_m) :
  (rest * b + digit < b * m)%N.
Proof.
have hlow : (rest * b + digit < rest.+1 * b)%N.
  rewrite mulSn [(b + rest * b)%N]addnC ltn_add2l.
  exact: valP digit.
have hhigh : (rest.+1 * b <= b * m)%N.
  rewrite [(b * m)%N]mulnC leq_pmul2r.
  - exact: valP rest.
  - exact: leq_ltn_trans (leq0n digit) (valP digit).
apply/ltP.
exact: (Nat.lt_le_trans _ _ _ (elimT ltP hlow) (elimT leP hhigh)).
Qed.

Definition radix_join (entry : 'I_b * 'I_m) : 'I_((b * m)%N) :=
  Ordinal (radix_join_bound entry.1 entry.2).

Definition radix_split (hb : (0 < b)%N) (code : 'I_((b * m)%N)) :
    'I_b * 'I_m.
Proof.
refine
  (@Ordinal b ((val code) %% b)%N _,
   @Ordinal m ((val code) %/ b)%N _).
- by rewrite ltn_mod.
- rewrite ltn_divLR // [(m * b)%N]mulnC.
  exact: valP code.
Defined.

Lemma radix_split_joinK (hb : (0 < b)%N) :
  cancel radix_join (radix_split hb).
Proof.
move=> [digit rest].
apply: injective_projections; apply: val_inj=> /=.
- by rewrite modnMDl modn_small //; exact: valP digit.
- by rewrite divnMDl // divn_small ?addn0 //; exact: valP digit.
Qed.

Lemma radix_join_splitK (hb : (0 < b)%N) :
  cancel (radix_split hb) radix_join.
Proof.
move=> code; apply: val_inj=> /=.
by rewrite -divn_eq.
Qed.

Lemma radix_join_bijective (hb : (0 < b)%N) : bijective radix_join.
Proof.
apply: (@Bijective _ _ radix_join (radix_split hb)).
- exact: radix_split_joinK.
- exact: radix_join_splitK.
Qed.

Lemma radix_join_tail_digit (hb : (0 < b)%N) (digit : 'I_b)
    (rest exponent : nat) :
  ((((rest * b + digit)%N %/ (b ^ exponent.+1)) %% b)%N) =
  (((rest %/ (b ^ exponent)) %% b)%N).
Proof.
rewrite expnS divnMA divnMDl //.
by rewrite (@divn_small digit b (valP digit)) addn0.
Qed.

End RadixBijection.

Section MixedRadix.

Variable R : comSemiRingType.

Lemma mixed_radix_sum_product (b n : nat)
    (term : 'I_n -> nat -> R) :
  (0 < b)%N ->
  \sum_(code < b ^ n)
      \prod_(i : 'I_n)
        term i (((code %/ (b ^ (val i))) %% b)%N) =
  \prod_(i : 'I_n) \sum_(digit < b) term i digit.
Proof.
elim: n term => [|n ih] term hb.
- by rewrite expn0 big_ord1 !big_ord0.
- rewrite expnS.
  rewrite (reindex (@radix_join b (b ^ n))) /=;
    last first.
      apply: onW_bij.
      exact: (@radix_join_bijective b (b ^ n) hb).
  rewrite -(@pair_bigA R 0 +%R ('I_b) ('I_(b ^ n))
    (fun digit rest =>
      \prod_(i : 'I_n.+1)
        term i
          ((((rest * b + digit)%N %/ (b ^ (val i))) %% b)%N))) /=.
  under eq_bigr do under eq_bigr do rewrite big_ord_recl /=.
  under eq_bigr do under eq_bigr do rewrite expn0 divn1 modnMDl
    modn_small ?ltn_ord //.
  under eq_bigr do under eq_bigr do under eq_bigr do
    rewrite (radix_join_tail_digit hb).
  rewrite -big_distrlr.
  rewrite (ih (fun i digit => term (lift ord0 i) digit) hb).
  by rewrite big_ord_recl.
Qed.

End MixedRadix.

End PolynomialFormulasSexticMuRecMixedRadixSemantics.
