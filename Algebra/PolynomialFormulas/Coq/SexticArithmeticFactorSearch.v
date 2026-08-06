From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import SexticRecursiveCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Division-free bounded factor searches.

    The original transparent search asks MathComp's polynomial divisibility
    Boolean.  For the direct recursion certificate it is more convenient to
    use the already defined synthetic remainders.  The lemmas below prove that
    the two executable searches are extensionally identical. *)
Module PolynomialFormulasSexticArithmeticFactorSearch.

Import PolynomialFormulasSexticRecursiveCore.

Definition has_arithmetic_linear_factor (f : monic_sextic) : bool :=
  has (linear_remainder_zerob f) (symmetric_interval (root_bound f)).

Definition has_arithmetic_quadratic_factor (f : monic_sextic) : bool :=
  has (fun b => has (quadratic_remainder_zerob f b)
    (symmetric_interval (root_bound f ^ 2)))
    (symmetric_interval (2 * root_bound f)).

Definition has_arithmetic_cubic_factor (f : monic_sextic) : bool :=
  has (fun b => has (fun c => has (cubic_remainder_zerob f b c)
      (symmetric_interval (root_bound f ^ 3)))
    (symmetric_interval (3 * root_bound f ^ 2)))
    (symmetric_interval (3 * root_bound f)).

Lemma size_quadratic_remainder_le f b c :
  (size (quadratic_remainder f b c) <= 2)%N.
Proof.
apply/leq_sizeP=> i hi.
case: i hi=> [|[|i]] // hi.
by rewrite /quadratic_remainder !coefD coefCM coefX coefC /= !mulr0 !addr0.
Qed.

Lemma size_cubic_remainder_le f b c d :
  (size (cubic_remainder f b c d) <= 3)%N.
Proof.
apply/leq_sizeP=> i hi.
case: i hi=> [|[|[|i]]] // hi.
by rewrite /cubic_remainder !coefD !coefCM !coefXn !coefX !coefC /=
  !mulr0 !addr0.
Qed.

Lemma divisible_smaller_zero (q r : {poly int}) :
  (size r < size q)%N -> q %| r -> r = 0.
Proof.
move=> hsize hdiv.
apply/eqP; apply/negPn/negP=> hr.
have hle := dvdp_leq hr hdiv.
by move: hsize; rewrite ltnNge hle.
Qed.

Lemma sub_two_eq0 (x y z : int) : x - y - z = 0 -> x = y + z.
Proof.
move=> hzero.
by rewrite -(add_add_sub_sub x y z) hzero addr0.
Qed.

Lemma sub_one_eq0_of_eq (x y : int) : x = y -> x - y = 0.
Proof. by move=> ->; rewrite subrr. Qed.

Lemma sub_two_eq0_of_eq (x y z : int) : x = y + z -> x - y - z = 0.
Proof.
move=> ->.
by rewrite [y + z]addrC addrK subrr.
Qed.

Lemma sub_three_eq0 (x a b c : int) :
  x - a - b - c = 0 -> x = a + b + c.
Proof.
move=> hzero.
by rewrite -(add_add_add_sub_sub_sub x a b c) hzero addr0.
Qed.

Lemma sub_three_eq0_of_eq (x a b c : int) :
  x = a + b + c -> x - a - b - c = 0.
Proof.
move=> hx; apply/eqP.
rewrite !subr_eq0 !subr_eq hx.
apply/eqP.
transitivity (c + (a + b)); first exact: addrC.
transitivity (c + (b + a)).
- congr (c + _); exact: addrC.
- exact: (addrA c b a).
Qed.

Lemma linear_remainder_zerob_dvdp f c :
  linear_remainder_zerob f c =
    (linear_factor c %| monic_polynomial f).
Proof.
apply/idP/idP.
- move/linear_remainder_zeroP=> hzero.
  have hz : f`_0 - c * linear_q0 f c = 0 :=
    sub_one_eq0_of_eq hzero.
  have hrem : (f`_0 - c * linear_q0 f c)%:P = 0 by rewrite hz.
  rewrite (linear_division_identity f c) hrem addr0.
  exact: dvdp_mulIl.
- move=> hdiv; apply/linear_remainder_zeroP.
  have hprod : linear_factor c %|
      linear_factor c * linear_quotient f c := dvdp_mulIl _ _.
  have hrem : linear_factor c %|
      (f`_0 - c * linear_q0 f c)%:P.
    by move: hdiv; rewrite (linear_division_identity f c)
      (@dvdp_addr _ _ _ _ hprod).
  have hrzero : (f`_0 - c * linear_q0 f c)%:P = 0.
    apply: divisible_smaller_zero hrem.
    rewrite size_linear_factor size_polyC.
    by case: (f`_0 - c * linear_q0 f c == 0).
  move/polyC_inj: hrzero.
  exact: subr0_eq.
Qed.

Lemma quadratic_remainder_zerob_dvdp f b c :
  quadratic_remainder_zerob f b c =
    (quadratic_factor b c %| monic_polynomial f).
Proof.
apply/idP/idP.
- move/quadratic_remainder_zeroP=> [h1 h0].
  have hz1 : f`_1 - b * quadratic_q0 f b c -
      c * quadratic_q1 f b c = 0.
    exact: sub_two_eq0_of_eq h1.
  have hz0 : f`_0 - c * quadratic_q0 f b c = 0 :=
    sub_one_eq0_of_eq h0.
  have hrem : quadratic_remainder f b c = 0.
    rewrite /quadratic_remainder hz1 hz0.
    by rewrite !mul0r addr0.
  rewrite (quadratic_division_identity f b c) hrem addr0.
  exact: dvdp_mulIl.
- move=> hdiv; apply/quadratic_remainder_zeroP.
  have hprod : quadratic_factor b c %|
      quadratic_factor b c * quadratic_quotient f b c := dvdp_mulIl _ _.
  have hrem : quadratic_factor b c %| quadratic_remainder f b c.
    by move: hdiv; rewrite (quadratic_division_identity f b c)
      (@dvdp_addr _ _ _ _ hprod).
  have hrzero : quadratic_remainder f b c = 0.
    apply: divisible_smaller_zero hrem.
    rewrite size_quadratic_factor.
    exact: leq_ltn_trans (size_quadratic_remainder_le f b c) (ltnSn 2).
  have h1 := congr1 (fun p : {poly int} => p`_1) hrzero.
  have h0 := congr1 (fun p : {poly int} => p`_0) hrzero.
  rewrite /quadratic_remainder !coefD !coefCM !coefX !coefC /=
    ?mulr0 ?mulr1 ?addr0 ?add0r in h1 h0.
  split.
  - exact: sub_two_eq0 h1.
  - exact: subr0_eq h0.
Qed.

Lemma cubic_remainder_zerob_dvdp f b c d :
  cubic_remainder_zerob f b c d =
    (cubic_factor b c d %| monic_polynomial f).
Proof.
apply/idP/idP.
- move/cubic_remainder_zeroP=> [h2 [h1 h0]].
  have hz2 : f`_2 - b * cubic_q0 f b c d -
      c * cubic_q1 f b c - d * cubic_q2 f b = 0.
    exact: sub_three_eq0_of_eq h2.
  have hz1 : f`_1 - c * cubic_q0 f b c d -
      d * cubic_q1 f b c = 0.
    exact: sub_two_eq0_of_eq h1.
  have hz0 : f`_0 - d * cubic_q0 f b c d = 0 :=
    sub_one_eq0_of_eq h0.
  have hrem : cubic_remainder f b c d = 0.
    rewrite /cubic_remainder hz2 hz1 hz0.
    by rewrite !mul0r !addr0.
  rewrite (cubic_division_identity f b c d) hrem addr0.
  exact: dvdp_mulIl.
- move=> hdiv; apply/cubic_remainder_zeroP.
  have hprod : cubic_factor b c d %|
      cubic_factor b c d * cubic_quotient f b c d := dvdp_mulIl _ _.
  have hrem : cubic_factor b c d %| cubic_remainder f b c d.
    by move: hdiv; rewrite (cubic_division_identity f b c d)
      (@dvdp_addr _ _ _ _ hprod).
  have hrzero : cubic_remainder f b c d = 0.
    apply: divisible_smaller_zero hrem.
    rewrite size_cubic_factor.
    exact: leq_ltn_trans (size_cubic_remainder_le f b c d) (ltnSn 3).
  have h2 := congr1 (fun p : {poly int} => p`_2) hrzero.
  have h1 := congr1 (fun p : {poly int} => p`_1) hrzero.
  have h0 := congr1 (fun p : {poly int} => p`_0) hrzero.
  rewrite /cubic_remainder !coefD !coefCM !coefXn !coefX !coefC /=
    ?mulr0 ?mulr1 ?addr0 ?add0r in h2 h1 h0.
  split; first exact: sub_three_eq0 h2.
  split.
  - exact: sub_two_eq0 h1.
  - exact: subr0_eq h0.
Qed.

Theorem has_arithmetic_linear_factorE f :
  has_arithmetic_linear_factor f = has_bounded_linear_factor f.
Proof.
rewrite /has_arithmetic_linear_factor /has_bounded_linear_factor.
apply: eq_has=> c.
exact: linear_remainder_zerob_dvdp.
Qed.

Theorem has_arithmetic_quadratic_factorE f :
  has_arithmetic_quadratic_factor f = has_bounded_quadratic_factor f.
Proof.
rewrite /has_arithmetic_quadratic_factor /has_bounded_quadratic_factor.
apply: eq_has=> b; apply: eq_has=> c.
exact: quadratic_remainder_zerob_dvdp.
Qed.

Theorem has_arithmetic_cubic_factorE f :
  has_arithmetic_cubic_factor f = has_bounded_cubic_factor f.
Proof.
rewrite /has_arithmetic_cubic_factor /has_bounded_cubic_factor.
apply: eq_has=> b; apply: eq_has=> c; apply: eq_has=> d.
exact: cubic_remainder_zerob_dvdp.
Qed.

End PolynomialFormulasSexticArithmeticFactorSearch.
