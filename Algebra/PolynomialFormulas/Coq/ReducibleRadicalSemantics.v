From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From PolynomialFormulas Require Import
  AbelRuffini LowDegreeRadicals SexticRecursiveCore QuinticRecursiveFactor
  SexticReducibleSemantics SexticFactorSelector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Radical semantics for the reducible quintic branch and for the
    quadratic/cubic branches of the recursive sextic decision.  All degree
    bookkeeping is stated in terms of MathComp polynomial [size], i.e. one
    more than the degree of a nonzero polynomial. *)
Module PolynomialFormulasReducibleRadicalSemantics.

Module LDR := PolynomialFormulasLowDegreeRadicals.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SRS := PolynomialFormulasSexticReducibleSemantics.
Module SFS := PolynomialFormulasSexticFactorSelector.

Import LeanProofs.PolynomialFormulasAbelRuffini.

(** A product of two nonzero polynomials of degree at most four has radical
    formulas for all its roots.  This is the common semantic endpoint for
    all factor branches below. *)
Lemma radical_formula_solves_small_product
    (p a b : {poly rat}) :
  p = a * b -> a != 0 -> b != 0 ->
  (size a <= 5)%N -> (size b <= 5)%N ->
  radical_formula_solves p.
Proof.
move=> -> ha0 hb0 ha5 hb5.
apply: (SRS.radical_formula_solves_mul a b).2; split.
- exact: LDR.low_degree_radical_formula ha0 ha5.
- exact: LDR.low_degree_radical_formula hb0 hb5.
Qed.

(** A proper factor of size two or three in a quintic leaves a cofactor of
    size five or four respectively. *)
Lemma radical_formula_solves_size6_small_factor
    (p q : {poly rat}) :
  size p = 6%N -> (1 < size q <= 3)%N -> q %| p ->
  radical_formula_solves p.
Proof.
move=> hp6 /andP[hqgt1 hqle3] hqdiv.
have hp0 : p != 0 by rewrite -size_poly_gt0 hp6.
have hq0 : q != 0.
  rewrite -size_poly_gt0.
  exact: ltn_trans (isT : (0 < 1)%N) hqgt1.
case/dvdpP/sig_eqW: hqdiv=> r hproduct.
have hr0 : r != 0.
  apply/negP=> /eqP hrzero.
  by move: hp0; rewrite hproduct hrzero mul0r eqxx.
have hrpos : (0 < size r)%N by rewrite size_poly_gt0 hr0.
have hsize_product : size p = (size r + size q).-1.
  by rewrite hproduct size_mul.
have hsumpos : (0 < size r + size q)%N :=
  leq_trans hrpos (leq_addr (size q) (size r)).
have hsum_eq : (size p).+1 = size r + size q.
  rewrite hsize_product.
  exact: prednK hsumpos.
have /orP[/eqP hq2 | /eqP hq3] :
    (size q == 2%N) || (size q == 3%N).
  move: hqgt1 hqle3.
  by case: (size q)=> [|[|[|[|n]]]] //.
- have hr5 : size r = 5%N.
    move: hsum_eq; rewrite hp6 hq2 /= => heq.
    apply/eqP; rewrite -(eqn_add2r 2%N); apply/eqP.
    exact: esym heq.
  apply: (@radical_formula_solves_small_product p r q
    hproduct hr0 hq0).
  + by rewrite hr5.
  + by rewrite hq2.
- have hr4 : size r = 4%N.
    move: hsum_eq; rewrite hp6 hq3 /= => heq.
    apply/eqP; rewrite -(eqn_add2r 3%N); apply/eqP.
    exact: esym heq.
  apply: (@radical_formula_solves_small_product p r q
    hproduct hr0 hq0).
  + by rewrite hr4.
  + by rewrite hq3.
Qed.

(** Reducibility supplies exactly the small factor required by the preceding
    lemma.  Monicity is not needed for this stronger rational statement. *)
Theorem reducible_quintic_radical_formula (p : {poly rat}) :
  size p = 6%N -> ~ irreducible_poly p ->
  radical_formula_solves p.
Proof.
move=> hp6 hred.
have [q [hqsmall hqdiv]] :=
  QRF.reducible_size6_has_small_factor hp6 hred.
exact: radical_formula_solves_size6_small_factor hp6 hqsmall hqdiv.
Qed.

Theorem reducible_monic_quintic_radical_formula (p : {poly rat}) :
  size p = 6%N -> p \is monic -> ~ irreducible_poly p ->
  radical_formula_solves p.
Proof.
move=> hp6 _.
exact: reducible_quintic_radical_formula hp6.
Qed.

(** The integer-coefficient quintic representation used by the recursive
    decision is an immediate instance of the rational theorem. *)
Theorem reducible_monic_quintic_tuple_radical_formula
    (f : QRF.monic_quintic) :
  ~ irreducible_poly
      (map_poly (intr : int -> rat) (QRF.quintic_polynomial f)) ->
  radical_formula_solves
      (map_poly (intr : int -> rat) (QRF.quintic_polynomial f)).
Proof.
apply: reducible_quintic_radical_formula.
by rewrite size_rat_int_poly QRF.size_quintic_polynomial.
Qed.

(** For a sextic, a factor of size three or four leaves a cofactor of size
    five or four.  Thus both sides again have degree at most four. *)
Lemma radical_formula_solves_size7_nonlinear_factor
    (p q : {poly rat}) :
  size p = 7%N ->
  ((size q == 3%N) || (size q == 4%N)) ->
  q %| p -> radical_formula_solves p.
Proof.
move=> hp7 hqsize hqdiv.
have hp0 : p != 0 by rewrite -size_poly_gt0 hp7.
have hqpos : (0 < size q)%N.
  move: hqsize=> /orP[/eqP hq3 | /eqP hq4].
  - by rewrite hq3.
  - by rewrite hq4.
have hq0 : q != 0 by rewrite -size_poly_gt0.
case/dvdpP/sig_eqW: hqdiv=> r hproduct.
have hr0 : r != 0.
  apply/negP=> /eqP hrzero.
  by move: hp0; rewrite hproduct hrzero mul0r eqxx.
have hrpos : (0 < size r)%N by rewrite size_poly_gt0 hr0.
have hsize_product : size p = (size r + size q).-1.
  by rewrite hproduct size_mul.
have hsumpos : (0 < size r + size q)%N :=
  leq_trans hrpos (leq_addr (size q) (size r)).
have hsum_eq : (size p).+1 = size r + size q.
  rewrite hsize_product.
  exact: prednK hsumpos.
move: hqsize=> /orP[/eqP hq3 | /eqP hq4].
- have hr5 : size r = 5%N.
    move: hsum_eq; rewrite hp7 hq3 /= => heq.
    apply/eqP; rewrite -(eqn_add2r 3%N); apply/eqP.
    exact: esym heq.
  apply: (@radical_formula_solves_small_product p r q
    hproduct hr0 hq0).
  + by rewrite hr5.
  + by rewrite hq3.
- have hr4 : size r = 4%N.
    move: hsum_eq; rewrite hp7 hq4 /= => heq.
    apply/eqP; rewrite -(eqn_add2r 4%N); apply/eqP.
    exact: esym heq.
  apply: (@radical_formula_solves_small_product p r q
    hproduct hr0 hq0).
  + by rewrite hr4.
  + by rewrite hq4.
Qed.

(** In the bounded linear branch, the transparent selector computes an
    exact monic quintic quotient.  Once that quotient is known to be
    radical-solvable, the selected linear factor is covered by the
    low-degree theorem and product closure gives the sextic result. *)
Theorem bounded_linear_factor_radical_formula
    (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  radical_formula_solves
    (map_poly (intr : int -> rat)
      (QRF.quintic_polynomial
        (QRF.sextic_linear_quotient_quintic f
          (SFS.selected_sextic_linear_coefficient f)))) ->
  radical_formula_solves
    (map_poly (intr : int -> rat) (SRC.monic_polynomial f)).
Proof.
move=> hlinear hquintic.
have hfactor :
    map_poly (intr : int -> rat) (SRC.monic_polynomial f) =
      map_poly (intr : int -> rat)
        (SRC.linear_factor (SFS.selected_sextic_linear_coefficient f)) *
      map_poly (intr : int -> rat)
        (QRF.quintic_polynomial
          (QRF.sextic_linear_quotient_quintic f
            (SFS.selected_sextic_linear_coefficient f))).
  have hfactorZ := congr1 (map_poly (intr : int -> rat))
    (SFS.selected_sextic_linear_factorization_quintic hlinear).
  by move: hfactorZ; rewrite rmorphM.
rewrite hfactor.
apply: (SRS.radical_formula_solves_mul _ _).2; split=> //.
have hlinear_size :
    size (map_poly (intr : int -> rat)
      (SRC.linear_factor (SFS.selected_sextic_linear_coefficient f))) = 2%N.
  by rewrite size_rat_int_poly SRC.size_linear_factor.
have hlinear0 :
    map_poly (intr : int -> rat)
      (SRC.linear_factor (SFS.selected_sextic_linear_coefficient f)) != 0.
  by rewrite -size_poly_gt0 hlinear_size.
have hlinear5 :
    (size (map_poly (intr : int -> rat)
      (SRC.linear_factor (SFS.selected_sextic_linear_coefficient f))) <= 5)%N.
  by rewrite hlinear_size.
exact: LDR.low_degree_radical_formula hlinear0 hlinear5.
Qed.

(** A successful bounded nonlinear search supplies a quadratic or cubic
    integer divisor.  [dvdp_rat_int] transports it to the rational
    polynomial without changing either factor's size. *)
Theorem bounded_nonlinear_factor_radical_formula
    (f : SRC.monic_sextic) :
  SRC.has_bounded_nonlinear_factor f ->
  radical_formula_solves
    (map_poly (intr : int -> rat) (SRC.monic_polynomial f)).
Proof.
rewrite /SRC.has_bounded_nonlinear_factor.
move/orP=> [hquadratic | hcubic].
- have [b [_ [c [_ hdiv]]]] :=
    elimT (SRC.has_bounded_quadratic_factorP f) hquadratic.
  apply: (@radical_formula_solves_size7_nonlinear_factor
    (map_poly (intr : int -> rat) (SRC.monic_polynomial f))
    (map_poly (intr : int -> rat) (SRC.quadratic_factor b c))).
  + by rewrite size_rat_int_poly SRC.size_monic_polynomial.
  + apply/orP; left; apply/eqP.
    by rewrite size_rat_int_poly SRC.size_quadratic_factor.
  + by rewrite dvdp_rat_int.
- have [b [_ [c [_ [d [_ hdiv]]]]]] :=
    elimT (SRC.has_bounded_cubic_factorP f) hcubic.
  apply: (@radical_formula_solves_size7_nonlinear_factor
    (map_poly (intr : int -> rat) (SRC.monic_polynomial f))
    (map_poly (intr : int -> rat) (SRC.cubic_factor b c d))).
  + by rewrite size_rat_int_poly SRC.size_monic_polynomial.
  + apply/orP; right; apply/eqP.
    by rewrite size_rat_int_poly SRC.size_cubic_factor.
  + by rewrite dvdp_rat_int.
Qed.

End PolynomialFormulasReducibleRadicalSemantics.
