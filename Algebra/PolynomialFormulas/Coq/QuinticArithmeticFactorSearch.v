From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  SexticRecursiveCore QuinticRecursiveFactor SexticArithmeticFactorSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Integer-arithmetic versions of the bounded quintic factor searches. *)
Module PolynomialFormulasQuinticArithmeticFactorSearch.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasQuinticRecursiveFactor.
Import PolynomialFormulasSexticArithmeticFactorSearch.

Definition quintic_linear_q3 f c := (quintic_polynomial f)`_4 - c.
Definition quintic_linear_q2 f c :=
  (quintic_polynomial f)`_3 - c * quintic_linear_q3 f c.
Definition quintic_linear_q1 f c :=
  (quintic_polynomial f)`_2 - c * quintic_linear_q2 f c.
Definition quintic_linear_q0 f c :=
  (quintic_polynomial f)`_1 - c * quintic_linear_q1 f c.

Definition quintic_linear_remainder_zerob f c : bool :=
  (quintic_polynomial f)`_0 == c * quintic_linear_q0 f c.

Definition quintic_linear_quotient f c : {poly int} :=
  'X^4 + (quintic_linear_q3 f c)%:P * 'X^3 +
    (quintic_linear_q2 f c)%:P * 'X^2 +
    (quintic_linear_q1 f c)%:P * 'X +
    (quintic_linear_q0 f c)%:P.

Definition quintic_quadratic_q2 f b := (quintic_polynomial f)`_4 - b.
Definition quintic_quadratic_q1 f b c :=
  (quintic_polynomial f)`_3 - c - b * quintic_quadratic_q2 f b.
Definition quintic_quadratic_q0 f b c :=
  (quintic_polynomial f)`_2 - b * quintic_quadratic_q1 f b c -
    c * quintic_quadratic_q2 f b.

Definition quintic_quadratic_remainder_zerob f b c : bool :=
  ((quintic_polynomial f)`_1 ==
      b * quintic_quadratic_q0 f b c +
      c * quintic_quadratic_q1 f b c) &&
  ((quintic_polynomial f)`_0 == c * quintic_quadratic_q0 f b c).

Definition quintic_quadratic_quotient f b c : {poly int} :=
  'X^3 + (quintic_quadratic_q2 f b)%:P * 'X^2 +
    (quintic_quadratic_q1 f b c)%:P * 'X +
    (quintic_quadratic_q0 f b c)%:P.

Definition quintic_quadratic_remainder f b c : {poly int} :=
  ((quintic_polynomial f)`_1 -
      b * quintic_quadratic_q0 f b c -
      c * quintic_quadratic_q1 f b c)%:P * 'X +
  ((quintic_polynomial f)`_0 - c * quintic_quadratic_q0 f b c)%:P.

Lemma quintic_polynomial_coef0 f :
  (quintic_polynomial f)`_0 = linear_q0 (quintic_sextic_embedding f) 0.
Proof.
rewrite /quintic_polynomial /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma quintic_polynomial_coef1 f :
  (quintic_polynomial f)`_1 = linear_q1 (quintic_sextic_embedding f) 0.
Proof.
rewrite /quintic_polynomial /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma quintic_polynomial_coef2 f :
  (quintic_polynomial f)`_2 = linear_q2 (quintic_sextic_embedding f) 0.
Proof.
rewrite /quintic_polynomial /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma quintic_polynomial_coef3 f :
  (quintic_polynomial f)`_3 = linear_q3 (quintic_sextic_embedding f) 0.
Proof.
rewrite /quintic_polynomial /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma quintic_polynomial_coef4 f :
  (quintic_polynomial f)`_4 = linear_q4 (quintic_sextic_embedding f) 0.
Proof.
rewrite /quintic_polynomial /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
by simpl; rewrite ?mulr0 ?mulr1 ?add0r ?addr0.
Qed.

Lemma quintic_linear_division_identity f c :
  quintic_polynomial f =
    linear_factor c * quintic_linear_quotient f c +
      ((quintic_polynomial f)`_0 - c * quintic_linear_q0 f c)%:P.
Proof.
apply/polyP=> i.
rewrite /linear_factor /quintic_linear_quotient.
rewrite mulrDl !coefD coefXM coefCM.
case: i => [|[|[|[|[|[|i]]]]]].
all: repeat (first
  [ rewrite coefD | rewrite coefXM | rewrite coefCM
  | rewrite coefXn | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ]).
all: rewrite /quintic_linear_q0 /quintic_linear_q1
  /quintic_linear_q2 /quintic_linear_q3.
- by rewrite -quintic_polynomial_coef0 subrKC.
- by rewrite -quintic_polynomial_coef1 subrK.
- by rewrite -quintic_polynomial_coef2 subrK.
- by rewrite -quintic_polynomial_coef3 subrK.
- by rewrite -quintic_polynomial_coef4 subrK.
- have hlead := elimT monicP (quintic_polynomial_monic f).
  by move: hlead; rewrite lead_coefE size_quintic_polynomial.
- by [] .
Qed.

Lemma quintic_quadratic_division_identity f b c :
  quintic_polynomial f =
    quadratic_factor b c * quintic_quadratic_quotient f b c +
      quintic_quadratic_remainder f b c.
Proof.
apply/polyP=> i.
rewrite /quadratic_factor /quintic_quadratic_quotient
  /quintic_quadratic_remainder.
rewrite !mulrDl -[b%:P * 'X * _]mulrA !coefD.
case: i => [|[|[|[|[|[|i]]]]]].
all: repeat (first
  [ rewrite coefD | rewrite coefXnM | rewrite coefXM
  | rewrite coefCM | rewrite coefXn | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ]).
all: rewrite /quintic_quadratic_q0 /quintic_quadratic_q1
  /quintic_quadratic_q2.
- rewrite -quintic_polynomial_coef0.
  by rewrite ?add_add_sub_sub ?sub_sub_add_add ?subrKC ?subrK.
- rewrite -quintic_polynomial_coef1.
  by rewrite ?add_add_sub_sub ?sub_sub_add_add ?subrKC ?subrK.
- rewrite -quintic_polynomial_coef2.
  by rewrite ?add_add_sub_sub ?sub_sub_add_add ?subrKC ?subrK.
- rewrite -quintic_polynomial_coef3.
  by rewrite ?add_add_sub_sub ?sub_sub_add_add ?subrKC ?subrK.
- rewrite -quintic_polynomial_coef4.
  by rewrite ?add_add_sub_sub ?sub_sub_add_add ?subrKC ?subrK.
- have hlead := elimT monicP (quintic_polynomial_monic f).
  by move: hlead; rewrite lead_coefE size_quintic_polynomial.
- by [] .
Qed.

Lemma size_quintic_quadratic_remainder_le f b c :
  (size (quintic_quadratic_remainder f b c) <= 2)%N.
Proof.
apply/leq_sizeP=> i hi.
case: i hi=> [|[|i]] // hi.
by rewrite /quintic_quadratic_remainder !coefD coefCM coefX coefC /=
  !mulr0 !addr0.
Qed.

Lemma quintic_linear_remainder_zerob_dvdp f c :
  quintic_linear_remainder_zerob f c =
    (linear_factor c %| quintic_polynomial f).
Proof.
apply/idP/idP.
- move/eqP=> hzero.
  have hz : (quintic_polynomial f)`_0 -
      c * quintic_linear_q0 f c = 0 := sub_one_eq0_of_eq hzero.
  rewrite (quintic_linear_division_identity f c) hz rmorph0 addr0.
  exact: dvdp_mulIl.
- move=> hdiv; apply/eqP.
  have hprod : linear_factor c %|
      linear_factor c * quintic_linear_quotient f c := dvdp_mulIl _ _.
  have hrem : linear_factor c %|
      ((quintic_polynomial f)`_0 - c * quintic_linear_q0 f c)%:P.
    have hsum : linear_factor c %|
        linear_factor c * quintic_linear_quotient f c +
          ((quintic_polynomial f)`_0 - c * quintic_linear_q0 f c)%:P.
      rewrite -(quintic_linear_division_identity f c).
      exact: hdiv.
    by move: hsum; rewrite (@dvdp_addr _ _ _ _ hprod).
  have hrzero : ((quintic_polynomial f)`_0 -
      c * quintic_linear_q0 f c)%:P = 0.
    apply: divisible_smaller_zero hrem.
    rewrite size_linear_factor size_polyC.
    by case: ((quintic_polynomial f)`_0 -
      c * quintic_linear_q0 f c == 0).
  move/polyC_inj: hrzero.
  exact: subr0_eq.
Qed.

Lemma quintic_quadratic_remainder_zerob_dvdp f b c :
  quintic_quadratic_remainder_zerob f b c =
    (quadratic_factor b c %| quintic_polynomial f).
Proof.
apply/idP/idP.
- move/andP=> [/eqP h1 /eqP h0].
  have hz1 : (quintic_polynomial f)`_1 -
      b * quintic_quadratic_q0 f b c -
      c * quintic_quadratic_q1 f b c = 0 :=
    sub_two_eq0_of_eq h1.
  have hz0 : (quintic_polynomial f)`_0 -
      c * quintic_quadratic_q0 f b c = 0 := sub_one_eq0_of_eq h0.
  have hrem : quintic_quadratic_remainder f b c = 0.
    rewrite /quintic_quadratic_remainder hz1 hz0.
    by rewrite !rmorph0 !mul0r addr0.
  rewrite (quintic_quadratic_division_identity f b c) hrem addr0.
  exact: dvdp_mulIl.
- move=> hdiv.
  have hprod : quadratic_factor b c %|
      quadratic_factor b c * quintic_quadratic_quotient f b c :=
    dvdp_mulIl _ _.
  have hrem : quadratic_factor b c %|
      quintic_quadratic_remainder f b c.
    have hsum : quadratic_factor b c %|
        quadratic_factor b c * quintic_quadratic_quotient f b c +
          quintic_quadratic_remainder f b c.
      rewrite -(quintic_quadratic_division_identity f b c).
      exact: hdiv.
    by move: hsum; rewrite (@dvdp_addr _ _ _ _ hprod).
  have hrzero : quintic_quadratic_remainder f b c = 0.
    apply: divisible_smaller_zero hrem.
    rewrite size_quadratic_factor.
    exact: leq_ltn_trans
      (size_quintic_quadratic_remainder_le f b c) (ltnSn 2).
  have h1 := congr1 (fun p : {poly int} => p`_1) hrzero.
  have h0 := congr1 (fun p : {poly int} => p`_0) hrzero.
  rewrite /quintic_quadratic_remainder !coefD !coefCM !coefXn !coefX !coefC /=
    ?mulr0 ?mulr1 ?addr0 ?add0r in h1 h0.
  have h1' : (quintic_polynomial f)`_1 -
      b * quintic_quadratic_q0 f b c -
      c * quintic_quadratic_q1 f b c = 0.
    rewrite quintic_polynomial_coef1.
    exact: h1.
  have h0' : (quintic_polynomial f)`_0 -
      c * quintic_quadratic_q0 f b c = 0.
    rewrite quintic_polynomial_coef0.
    exact: h0.
  apply/andP; split; apply/eqP.
  - exact: sub_two_eq0 h1'.
  - exact: subr0_eq h0'.
Qed.

Definition has_arithmetic_quintic_linear_factor f : bool :=
  has (quintic_linear_remainder_zerob f)
    (symmetric_interval (quintic_root_bound f)).

Definition has_arithmetic_quintic_quadratic_factor f : bool :=
  has (fun b => has (quintic_quadratic_remainder_zerob f b)
    (symmetric_interval (quintic_root_bound f ^ 2)))
    (symmetric_interval (2 * quintic_root_bound f)).

Definition has_arithmetic_quintic_proper_factor f : bool :=
  has_arithmetic_quintic_linear_factor f ||
  has_arithmetic_quintic_quadratic_factor f.

Theorem has_arithmetic_quintic_linear_factorE f :
  has_arithmetic_quintic_linear_factor f =
    has_bounded_linear_factor f.
Proof.
rewrite /has_arithmetic_quintic_linear_factor /has_bounded_linear_factor.
apply: eq_has=> c.
exact: quintic_linear_remainder_zerob_dvdp.
Qed.

Theorem has_arithmetic_quintic_quadratic_factorE f :
  has_arithmetic_quintic_quadratic_factor f =
    has_bounded_quadratic_factor f.
Proof.
rewrite /has_arithmetic_quintic_quadratic_factor
  /has_bounded_quadratic_factor.
apply: eq_has=> b; apply: eq_has=> c.
exact: quintic_quadratic_remainder_zerob_dvdp.
Qed.

Theorem has_arithmetic_quintic_proper_factorE f :
  has_arithmetic_quintic_proper_factor f = has_bounded_proper_factor f.
Proof.
by rewrite /has_arithmetic_quintic_proper_factor
  /has_bounded_proper_factor has_arithmetic_quintic_linear_factorE
  has_arithmetic_quintic_quadratic_factorE.
Qed.

End PolynomialFormulasQuinticArithmeticFactorSearch.
