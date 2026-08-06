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

Lemma radix_join_mod_digit (digit : 'I_b) (rest : nat) :
  (((rest * b + digit)%N %% b)%N) = digit.
Proof.
by rewrite modnMDl modn_small //; exact: valP digit.
Qed.

Lemma radix_join_div_rest (hb : (0 < b)%N) (digit : 'I_b)
    (rest : nat) :
  (((rest * b + digit)%N %/ b)%N) = rest.
Proof.
by rewrite divnMDl // divn_small ?addn0 //; exact: valP digit.
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

Section ObserverBridge.

Variable T : Type.

Fixpoint mixed_radix_term_from (one : T) (mul : T -> T -> T)
    (digit_term : nat -> nat -> T) (b position count code : nat) : T :=
  match count with
  | 0 => one
  | count'.+1 =>
      mul (digit_term position ((code %% b)%N))
        (mixed_radix_term_from one mul digit_term b position.+1 count'
          ((code %/ b)%N))
  end.

Fixpoint cartesian_terms (one : T) (mul : T -> T -> T)
    (factors : seq (seq T)) : seq T :=
  match factors with
  | [::] => [:: one]
  | head :: tail =>
      flatten
        [seq [seq mul x y | y <- cartesian_terms one mul tail]
          | x <- head]
  end.

Variable R : comSemiRingType.

Lemma mixed_radix_cartesian_observer_sum
    (one : T) (mul : T -> T -> T) (digit_term : nat -> nat -> T)
    (factor_terms : nat -> seq T) (observe : T -> R)
    (b position count : nat) :
  (0 < b)%N ->
  (forall (i : nat) (target : T -> R),
      \sum_(digit < b) target (digit_term i digit) =
      \sum_(term <- factor_terms i) target term) ->
  \sum_(code < b ^ count)
      observe
        (mixed_radix_term_from one mul digit_term b position count code) =
  \sum_(term <- cartesian_terms one mul
      [seq factor_terms i | i <- iota position count]) observe term.
Proof.
move=> hb hfactor.
elim: count position observe => [|count ih] position observe.
- by rewrite /= expn0 big_ord1 big_seq1.
- rewrite /= expnS.
  rewrite (reindex (@radix_join b (b ^ count))) /=;
    last first.
      apply: onW_bij.
      exact: (@radix_join_bijective b (b ^ count) hb).
  rewrite -(@pair_bigA R 0 +%R ('I_b) ('I_(b ^ count))
    (fun digit rest =>
      observe
        (mixed_radix_term_from one mul digit_term b position count.+1
          (rest * b + digit)%N))) /=.
  under eq_bigr => digit _ do
    under eq_bigr => rest _ do
      rewrite /= (radix_join_mod_digit digit rest)
        (radix_join_div_rest hb digit rest).
  under eq_bigr => digit _ do
    rewrite (ih position.+1
      (fun tail_term =>
        observe (mul (digit_term position digit) tail_term))).
  rewrite (hfactor position
    (fun x =>
      \sum_(tail_term <- cartesian_terms one mul
          [seq factor_terms i | i <- iota position.+1 count])
        observe (mul x tail_term))).
  rewrite big_flatten big_map.
  apply: eq_bigr => term _.
  by rewrite big_map.
Qed.

End ObserverBridge.

End PolynomialFormulasSexticMuRecMixedRadixSemantics.
