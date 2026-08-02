From mathcomp Require Import all_ssreflect all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticFactorCompleteness SexticSparseResolvents SexticNewtonPowerSums
  SexticComputedResolvents SexticSeparatingSearch SexticSeparatingExistence
  SexticSeparatingSelector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Coefficient-only totalization of the separating search. *)
Module PolynomialFormulasSexticTotalSeparatingSelector.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticFactorCompleteness.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticSeparatingSearch.
Import PolynomialFormulasSexticSeparatingExistence.
Import PolynomialFormulasSexticSeparatingSelector.

(** This is the constructive core hidden inside the classical
    [not_irreducible_bounded_proper_factor] direction: once a particular
    proper divisor is supplied, either it or its complementary factor has
    size at most four. *)
Lemma proper_rational_divisor_has_small_factor
    (p q : {poly rat}) :
  size p = 7%N -> size q != 1%N -> q %| p -> ~ (q %= p) ->
  exists r : {poly rat}, (1 < size r <= 4)%N /\ r %| p.
Proof.
move=> hp7 hq1 hqdiv hqneqp.
have hp0 : p != 0 by rewrite -size_poly_gt0 hp7.
have hq0 : q != 0.
  apply: contraTneq hqdiv=> ->.
  by rewrite dvd0p (negPf hp0).
have hqgt1 : (1 < size q)%N.
  by rewrite ltn_neqAle eq_sym hq1 size_poly_gt0 hq0.
have hqsize_ne : size q != size p.
  apply/eqP=> hsize.
  apply: hqneqp.
  move: (dvdp_size_eqp hqdiv).
  by rewrite hsize eqxx => <-.
have hqlt : (size q < size p)%N.
  rewrite ltn_neqAle hqsize_ne.
  exact: dvdp_leq hp0 hqdiv.
case/dvdpP/sig_eqW: hqdiv=> s hproduct.
have hs0 : s != 0.
  apply/negP=> /eqP hszero.
  by move: hp0; rewrite hproduct hszero mul0r eqxx.
have hsdiv : s %| p.
  by rewrite hproduct; exact: dvdp_mulIl.
have hqdiv' : q %| p.
  by rewrite hproduct; exact: dvdp_mulIr.
have hsize_product : size p = (size s + size q).-1.
  by rewrite hproduct size_mul.
case hqle4: (size q <= 4)%N.
- have hqle4P : (size q <= 4)%N by rewrite hqle4.
  exists q; split; last exact: hqdiv'.
  by apply/andP; split.
- have hqgt4 : (4 < size q)%N.
    by rewrite ltnNge hqle4.
  have hspos : (0 < size s)%N by rewrite size_poly_gt0 hs0.
  have hsumpos : (0 < size s + size q)%N :=
    leq_trans hspos (leq_addr (size q) (size s)).
  have hsum_eq : (size p).+1 = size s + size q.
    rewrite hsize_product.
    exact: prednK hsumpos.
  have /orP [/eqP hq5 | /eqP hq6] :
      (size q == 5%N) || (size q == 6%N).
    move: hqgt4 hqlt; rewrite hp7.
    by case: (size q)=> [|[|[|[|[|[|[|n]]]]]]] //.
  + have hs3 : size s = 3%N.
      move: hsum_eq; rewrite hp7 hq5 /=.
      move=> heq.
      apply/eqP; rewrite -(eqn_add2r 5%N); apply/eqP.
      exact: esym heq.
    exists s; split; last exact: hsdiv.
    by rewrite hs3.
  + have hs2 : size s = 2%N.
      move: hsum_eq; rewrite hp7 hq6 /=.
      move=> heq.
      apply/eqP; rewrite -(eqn_add2r 6%N); apply/eqP.
      exact: esym heq.
    exists s; split; last exact: hsdiv.
    by rewrite hs2.
Qed.

(** Unlike [has_bounded_proper_factorP], this direction needs no excluded
    middle: an arbitrary counterexample to irreducibility supplies the
    concrete divisor consumed by the preceding lemma. *)
Lemma no_bounded_proper_factor_irreducible (f : monic_sextic) :
  has_bounded_proper_factor f = false ->
  irreducible_poly (monic_polynomial f).
Proof.
move=> hnone.
pose pQ := map_poly (intr : int -> rat) (monic_polynomial f).
have hpQsize : size pQ = 7%N.
  by rewrite /pQ size_rat_int_poly size_monic_polynomial.
have hpQirr : irreducible_poly pQ.
  split; first by rewrite hpQsize.
  move=> q hq1 hqdiv.
  case heq: (q %= pQ); first by [].
  have hqneq : ~ (q %= pQ) by rewrite heq.
  have [s [hssmall hsdiv]] :=
    proper_rational_divisor_has_small_factor
      hpQsize hq1 hqdiv hqneq.
  have hsgt : (1 < size s)%N := (andP hssmall).1.
  have [sz [hszmonic [hszsize hszdiv]]] :=
    lift_monic_rational_factor hsgt hsdiv.
  have hszsmall : (1 < size sz <= 4)%N.
    by rewrite hszsize.
  have hfound : has_bounded_proper_factor f :=
    small_monic_factor_found hszmonic hszsmall hszdiv.
  by move: hnone; rewrite hfound.
exact: (proj1 (irreducible_rat_int (monic_polynomial f))) hpQirr.
Qed.

(** Guarding the separating test by the factor Boolean makes it total on
    reducible inputs: those inputs succeed already at index zero. *)
Definition pair_total_separatesb (f : monic_sextic) (n : nat) : bool :=
  has_bounded_proper_factor f ||
    pair_separatesb f (parameter_at n).

Definition triple_total_separatesb (f : monic_sextic) (n : nat) : bool :=
  has_bounded_proper_factor f ||
    triple_separatesb f (parameter_at n).

Lemma pair_total_separates_eventually_of_roots roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) :
  exists n, pair_total_separatesb f n = true.
Proof.
case hfactor: (has_bounded_proper_factor f).
- exists 0%N.
  by rewrite /pair_total_separatesb hfactor.
- have [n hn] := pair_separating_eventually_true hvieta hroots.
  exists n.
  by rewrite /pair_total_separatesb hfactor hn.
Qed.

Lemma triple_total_separates_eventually_of_roots roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots)
    (hroots : tuple_injective roots) :
  exists n, triple_total_separatesb f n = true.
Proof.
case hfactor: (has_bounded_proper_factor f).
- exists 0%N.
  by rewrite /triple_total_separatesb hfactor.
- have [n hn] := triple_separating_eventually_true hvieta hroots.
  exists n.
  by rewrite /triple_total_separatesb hfactor hn.
Qed.

End PolynomialFormulasSexticTotalSeparatingSelector.
