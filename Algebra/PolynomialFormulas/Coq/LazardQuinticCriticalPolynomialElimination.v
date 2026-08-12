From Stdlib Require Import Ring Field Lia.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardCubicQuadraticElimination
  LazardCriticalPolynomialCommonDivisor
  LazardQuinticCriticalElimination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Polynomial lift of the three pointwise critical-elimination identities.

    This file is intentionally formula-independent after the five scalar
    parameters [a,b,g,d,e].  The only denominator-bearing identity is the
    already displayed quintic-by-cubic division; its six coefficients are
    checked separately by the kernel-producing field tactic. *)
Module PolynomialFormulasLazardQuinticCriticalPolynomialElimination.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Module PC := PolynomialFormulasLazardCriticalPolynomialCommonDivisor.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Local Open Scope ring_scope.

Section PolynomialElimination.

Variable F : fieldType.

Definition lazard_critical_h_poly (a b g : F) : {poly F} :=
  (((1 : F)%:P * 'X + a%:P) * 'X + b%:P) * 'X + g%:P.

Definition lazard_critical_hprime_poly (a b : F) : {poly F} :=
  PC.lazard_quadratic_polynomial b (2%:R * a) 3%:R.

Definition lazard_critical_ell_poly (e : F) : {poly F} :=
  'X + e%:P.

Definition lazard_critical_f_poly (a b g d e : F) : {poly F} :=
  lazard_critical_h_poly a b g ^+ 2 -
    d%:P * lazard_critical_ell_poly e.

Definition lazard_critical_A_poly (a b g e : F) : {poly F} :=
  PC.lazard_cubic_polynomial
    (CE.lazard_critical_cubic_coefficient0 a b g e)
    (CE.lazard_critical_cubic_coefficient1 a b e)
    (CE.lazard_critical_cubic_coefficient2 a e)
    (@CE.lazard_critical_cubic_coefficient3 F).

Definition lazard_critical_Q_poly (a b g d e : F) : {poly F} :=
  (4%:R : F)%:P * lazard_critical_ell_poly e *
      (lazard_critical_hprime_poly a b ^+ 2) - d%:P.

Definition lazard_critical_q_poly (a b e : F) : {poly F} :=
  PC.lazard_quadratic_polynomial
    ((- 4%:R * a ^+ 2 + 204%:R * a * e - 420%:R * b -
      216%:R * e ^+ 2) / 125%:R)
    ((- 132%:R * a + 36%:R * e) / 25%:R)
    ((- 36%:R) / 5%:R).

Definition lazard_critical_B_poly (a b g d e : F) : {poly F} :=
  PC.lazard_quadratic_polynomial
    (CE.lazard_square_linear_critical_remainder0 a b g d e)
    (CE.lazard_square_linear_critical_remainder1 a b g e)
    (CE.lazard_square_linear_critical_remainder2 a b g e).

(** Quotient and remainder after clearing their common denominator [125]. *)
Definition lazard_critical_scaled_q_poly (a b e : F) : {poly F} :=
  PC.lazard_quadratic_polynomial
    (CE.lazard_critical_scaled_quotient_coefficient0 a b e)
    (CE.lazard_critical_scaled_quotient_coefficient1 a e)
    (@CE.lazard_critical_scaled_quotient_coefficient2 F).

Definition lazard_critical_scaled_B_poly
    (a b g d e : F) : {poly F} :=
  PC.lazard_quadratic_polynomial
    (CE.lazard_critical_scaled_remainder_coefficient0 a b g d e)
    (CE.lazard_critical_scaled_remainder_coefficient1 a b g e)
    (CE.lazard_critical_scaled_remainder_coefficient2 a b g e).

Definition lazard_critical_quartic_polynomial
    (s0 s1 s2 s3 s4 : F) : {poly F} :=
  ((((s4%:P * 'X + s3%:P) * 'X + s2%:P) * 'X + s1%:P) * 'X +
    s0%:P).

Definition lazard_critical_quintic_polynomial
    (l0 l1 l2 l3 l4 l5 : F) : {poly F} :=
  (((((l5%:P * 'X + l4%:P) * 'X + l3%:P) * 'X + l2%:P) * 'X +
    l1%:P) * 'X + l0%:P).

Definition lazard_critical_scaled_Q_coefficient_poly
    (a b d e : F) : {poly F} :=
  lazard_critical_quintic_polynomial
    (CE.lazard_critical_scaled_quintic_coefficient0 b d e)
    (CE.lazard_critical_scaled_quintic_coefficient1 a b e)
    (CE.lazard_critical_scaled_quintic_coefficient2 a b e)
    (CE.lazard_critical_scaled_quintic_coefficient3 a b e)
    (CE.lazard_critical_scaled_quintic_coefficient4 a e)
    (@CE.lazard_critical_scaled_quintic_coefficient5 F).

Add Ring lazard_critical_elimination_poly_ring :
  (@PC.lazard_poly_ring_theory F).
Add Field lazard_critical_elimination_field :
  (@CE.lazard_critical_field_theory F).
Add Ring lazard_critical_elimination_scalar_ring :
  (@NR.lazard_numerator_ring_theory F).

Lemma lazard_critical_elimination_eqE (x y : F) :
  @NR.lazard_numerator_ring_eq F x y <-> x = y.
Proof. reflexivity. Qed.

Opaque PC.lazard_poly_ring_zero PC.lazard_poly_ring_one
  PC.lazard_poly_ring_add PC.lazard_poly_ring_mul
  PC.lazard_poly_ring_sub PC.lazard_poly_ring_opp
  PC.lazard_poly_ring_eq
  NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq CE.lazard_critical_div
  CE.lazard_critical_inv.

(** The custom polynomial-ring reflection bridge only recognizes its opaque
    zero and one.  Expand the few fixed coefficients used by the structural
    identities before changing to that bridge. *)
Lemma lazard_critical_poly_two_natrE :
  (2%:R : {poly F}) = 1 + 1.
Proof. exact: (@natrD {poly F} 1 1). Qed.

Lemma lazard_critical_poly_three_natrE :
  (3%:R : {poly F}) = 2%:R + 1.
Proof. exact: (@natrD {poly F} 2 1). Qed.

Lemma lazard_critical_poly_four_natrE :
  (4%:R : {poly F}) = 2%:R * 2%:R.
Proof. exact: (@natrM {poly F} 2 2). Qed.

Lemma lazard_critical_poly_five_natrE :
  (5%:R : {poly F}) = 4%:R + 1.
Proof. exact: (@natrD {poly F} 4 1). Qed.

Lemma lazard_critical_poly_six_natrE :
  (6%:R : {poly F}) = 3%:R * 2%:R.
Proof. exact: (@natrM {poly F} 3 2). Qed.

Ltac lazard_critical_elimination_poly_prepare :=
  repeat first
    [ rewrite polyC_exp | rewrite expr2 | rewrite polyCB | rewrite polyCN
    | rewrite polyCM | rewrite polyCD | rewrite polyC_natr ].

Ltac lazard_critical_elimination_poly_numerals :=
  repeat first
    [ rewrite lazard_critical_poly_six_natrE
    | rewrite lazard_critical_poly_five_natrE
    | rewrite lazard_critical_poly_four_natrE
    | rewrite lazard_critical_poly_three_natrE
    | rewrite lazard_critical_poly_two_natrE
    | rewrite polyC1 ].

Ltac finish_lazard_critical_elimination_poly_ring :=
  lazard_critical_elimination_poly_prepare;
  lazard_critical_elimination_poly_numerals;
  repeat first
    [ rewrite PC.lazard_poly_ring_addE
    | rewrite PC.lazard_poly_ring_mulE
    | rewrite PC.lazard_poly_ring_subE
    | rewrite PC.lazard_poly_ring_oppE
    | rewrite PC.lazard_poly_ring_zeroE
    | rewrite PC.lazard_poly_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (PC.lazard_poly_ring_eq lhs rhs)
  end;
  ring.

Ltac lazard_critical_elimination_prepare :=
  repeat first
    [ rewrite CE.lazard_critical_432_natrE
    | rewrite CE.lazard_critical_420_natrE
    | rewrite CE.lazard_critical_408_natrE
    | rewrite CE.lazard_critical_340_natrE
    | rewrite CE.lazard_critical_324_natrE
    | rewrite CE.lazard_critical_285_natrE
    | rewrite CE.lazard_critical_225_natrE
    | rewrite CE.lazard_critical_216_natrE
    | rewrite CE.lazard_critical_204_natrE
    | rewrite CE.lazard_critical_199_natrE
    | rewrite CE.lazard_critical_165_natrE
    | rewrite CE.lazard_critical_132_natrE
    | rewrite CE.lazard_critical_48_natrE
    | rewrite CE.lazard_critical_45_natrE
    | rewrite CE.lazard_critical_36_natrE
    | rewrite CE.lazard_critical_24_natrE
    | rewrite CE.lazard_critical_13_natrE
    | rewrite CE.lazard_critical_9_natrE ];
  lazard_numerator_prepare.

Ltac finish_lazard_critical_elimination_field :=
  lazard_critical_elimination_prepare;
  repeat first
    [ rewrite CE.lazard_critical_divE | rewrite CE.lazard_critical_invE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  field.

Ltac finish_lazard_critical_elimination_ring :=
  lazard_critical_elimination_prepare;
  match goal with
  | |- ?lhs = ?rhs =>
      apply (proj1 (lazard_critical_elimination_eqE lhs rhs))
  end;
  ring.

Lemma lazard_critical_scale_quadratic_polynomial
    (k b0 b1 b2 : F) :
  k%:P * PC.lazard_quadratic_polynomial b0 b1 b2 =
    PC.lazard_quadratic_polynomial
      (k * b0) (k * b1) (k * b2).
Proof.
rewrite /PC.lazard_quadratic_polynomial.
finish_lazard_critical_elimination_poly_ring.
Qed.

Lemma lazard_critical_scale_polynomial_product
    (k : F) (p q : {poly F}) :
  k%:P * (p * q) = p * (k%:P * q).
Proof. finish_lazard_critical_elimination_poly_ring. Qed.

Lemma lazard_critical_scale_q_poly a b e
    (five_neq0 : (5%:R : F) != 0) :
  (125%:R : F)%:P * lazard_critical_q_poly a b e =
    lazard_critical_scaled_q_poly a b e.
Proof.
rewrite /lazard_critical_q_poly /lazard_critical_scaled_q_poly
  /CE.lazard_critical_scaled_quotient_coefficient0
  /CE.lazard_critical_scaled_quotient_coefficient1
  /CE.lazard_critical_scaled_quotient_coefficient2
  lazard_critical_scale_quadratic_polynomial.
rewrite (CE.lazard_critical_scale_125_div_5 (- 36%:R) five_neq0)
  (CE.lazard_critical_scale_125_div_25
    (- 132%:R * a + 36%:R * e) five_neq0)
  (CE.lazard_critical_scale_125_div_125
    (- 4%:R * a ^+ 2 + 204%:R * a * e - 420%:R * b -
      216%:R * e ^+ 2) five_neq0).
reflexivity.
Qed.

Lemma lazard_critical_scale_B_poly a b g d e
    (five_neq0 : (5%:R : F) != 0) :
  (125%:R : F)%:P * lazard_critical_B_poly a b g d e =
    lazard_critical_scaled_B_poly a b g d e.
Proof.
rewrite /lazard_critical_B_poly /lazard_critical_scaled_B_poly
  /CE.lazard_critical_scaled_remainder_coefficient0
  /CE.lazard_critical_scaled_remainder_coefficient1
  /CE.lazard_critical_scaled_remainder_coefficient2
  /CE.lazard_square_linear_critical_remainder0
  /CE.lazard_square_linear_critical_remainder1
  /CE.lazard_square_linear_critical_remainder2
  lazard_critical_scale_quadratic_polynomial.
rewrite !CE.lazard_critical_scale_125_div_125 //.
Qed.

Lemma lazard_critical_quadratic_square_polynomial
    (t0 t1 t2 : F) :
  PC.lazard_quadratic_polynomial t0 t1 t2 ^+ 2 =
    lazard_critical_quartic_polynomial
      (t0 ^+ 2) (2%:R * t0 * t1)
      (t1 ^+ 2 + 2%:R * t0 * t2)
      (2%:R * t1 * t2) (t2 ^+ 2).
Proof.
rewrite /PC.lazard_quadratic_polynomial
  /lazard_critical_quartic_polynomial.
finish_lazard_critical_elimination_poly_ring.
Qed.

Lemma lazard_critical_hprime_poly_square a b :
  lazard_critical_hprime_poly a b ^+ 2 =
    lazard_critical_quartic_polynomial
      (b ^+ 2) (4%:R * a * b)
      (4%:R * a ^+ 2 + 6%:R * b) (12%:R * a) 9%:R.
Proof.
rewrite /lazard_critical_hprime_poly
  lazard_critical_quadratic_square_polynomial.
have hs1 : 2%:R * b * (2%:R * a) = 4%:R * a * b.
  finish_lazard_critical_elimination_ring.
have hs2 :
    (2%:R * a) ^+ 2 + 2%:R * b * 3%:R =
      4%:R * a ^+ 2 + 6%:R * b.
  finish_lazard_critical_elimination_ring.
have hs3 : 2%:R * (2%:R * a) * 3%:R = 12%:R * a.
  finish_lazard_critical_elimination_ring.
have hs4 : (3%:R : F) ^+ 2 = 9%:R.
  finish_lazard_critical_elimination_ring.
by rewrite hs1 hs2 hs3 hs4.
Qed.

Lemma lazard_critical_scaled_linear_quartic_polynomial_abstract
    (K Four E D S0 S1 S2 S3 S4 X : {poly F}) :
  K * (Four * (X + E) *
      ((((S4 * X + S3) * X + S2) * X + S1) * X + S0) - D) =
    (((((K * (Four * S4) * X +
          K * (Four * (S3 + E * S4))) * X +
        K * (Four * (S2 + E * S3))) * X +
      K * (Four * (S1 + E * S2))) * X +
    K * (Four * (S0 + E * S1))) * X +
    K * (Four * E * S0 - D)).
Proof. finish_lazard_critical_elimination_poly_ring. Qed.

Lemma lazard_critical_scaled_linear_quartic_polynomial
    (k four e d s0 s1 s2 s3 s4 : F) :
  k%:P * (four%:P * ('X + e%:P) *
      lazard_critical_quartic_polynomial s0 s1 s2 s3 s4 - d%:P) =
    lazard_critical_quintic_polynomial
      (k * (four * e * s0 - d))
      (k * (four * (s0 + e * s1)))
      (k * (four * (s1 + e * s2)))
      (k * (four * (s2 + e * s3)))
      (k * (four * (s3 + e * s4)))
      (k * (four * s4)).
Proof.
rewrite /lazard_critical_quartic_polynomial
  /lazard_critical_quintic_polynomial.
lazard_critical_elimination_poly_prepare.
exact: lazard_critical_scaled_linear_quartic_polynomial_abstract.
Qed.

Lemma lazard_critical_scale_Q_poly a b g d e :
  (125%:R : F)%:P * lazard_critical_Q_poly a b g d e =
    lazard_critical_scaled_Q_coefficient_poly a b d e.
Proof.
rewrite /lazard_critical_Q_poly /lazard_critical_ell_poly
  /lazard_critical_scaled_Q_coefficient_poly
  lazard_critical_hprime_poly_square
  lazard_critical_scaled_linear_quartic_polynomial.
rewrite (CE.lazard_critical_scaled_quintic_coefficient0E b d e)
  (CE.lazard_critical_scaled_quintic_coefficient1E a b e)
  (CE.lazard_critical_scaled_quintic_coefficient2E a b e)
  (CE.lazard_critical_scaled_quintic_coefficient3E a b e)
  (CE.lazard_critical_scaled_quintic_coefficient4E a e)
  (@CE.lazard_critical_scaled_quintic_coefficient5E F).
reflexivity.
Qed.

Lemma lazard_critical_cubic_quadratic_polynomial_expansion
    (r0 r1 r2 c0 c1 c2 c3 q0 q1 q2 : F) :
  PC.lazard_quadratic_polynomial r0 r1 r2 +
      PC.lazard_cubic_polynomial c0 c1 c2 c3 *
        PC.lazard_quadratic_polynomial q0 q1 q2 =
    lazard_critical_quintic_polynomial
      (r0 + c0 * q0)
      (r1 + c1 * q0 + c0 * q1)
      (r2 + c2 * q0 + c1 * q1 + c0 * q2)
      (c3 * q0 + c2 * q1 + c1 * q2)
      (c3 * q1 + c2 * q2)
      (c3 * q2).
Proof.
rewrite /PC.lazard_quadratic_polynomial /PC.lazard_cubic_polynomial
  /lazard_critical_quintic_polynomial.
finish_lazard_critical_elimination_poly_ring.
Qed.

Lemma lazard_critical_scaled_B_add_Aq_polynomial a b g d e :
  lazard_critical_scaled_B_poly a b g d e +
      lazard_critical_A_poly a b g e *
        lazard_critical_scaled_q_poly a b e =
    lazard_critical_scaled_Q_coefficient_poly a b d e.
Proof.
rewrite /lazard_critical_scaled_B_poly /lazard_critical_A_poly
  /lazard_critical_scaled_q_poly
  /lazard_critical_scaled_Q_coefficient_poly
  lazard_critical_cubic_quadratic_polynomial_expansion.
rewrite (CE.lazard_critical_scaled_division_coefficient0 a b g d e)
  (CE.lazard_critical_scaled_division_coefficient1 a b g e)
  (CE.lazard_critical_scaled_division_coefficient2 a b g e)
  (CE.lazard_critical_scaled_division_coefficient3 a b e)
  (CE.lazard_critical_scaled_division_coefficient4 a e)
  (@CE.lazard_critical_scaled_division_coefficient5 F).
reflexivity.
Qed.

Lemma lazard_critical_A_poly_structure_abstract
    (A B G E X : {poly F}) :
  ((((- (5%:R : {poly F})) * X +
        ((- (3%:R : {poly F})) * A - (6%:R : {poly F}) * E)) * X +
      ((- (4%:R : {poly F})) * A * E - B)) * X +
    (G - (2%:R : {poly F}) * B * E)) =
  (((((1 : {poly F}) * X + A) * X + B) * X + G) -
    (2%:R : {poly F}) * (X + E) *
      (((3%:R : {poly F}) * X + (2%:R : {poly F}) * A) * X + B)).
Proof. finish_lazard_critical_elimination_poly_ring. Qed.

(** The coefficient cubic is the polynomial form of [h-2 ell h']. *)
Lemma lazard_critical_A_poly_structure a b g e :
  lazard_critical_A_poly a b g e =
    lazard_critical_h_poly a b g -
      (2%:R : F)%:P * lazard_critical_ell_poly e *
        lazard_critical_hprime_poly a b.
Proof.
rewrite /lazard_critical_A_poly /lazard_critical_h_poly
  /lazard_critical_hprime_poly /lazard_critical_ell_poly
  /CE.lazard_critical_cubic_coefficient0
  /CE.lazard_critical_cubic_coefficient1
  /CE.lazard_critical_cubic_coefficient2
  /CE.lazard_critical_cubic_coefficient3
  /PC.lazard_cubic_polynomial /PC.lazard_quadratic_polynomial.
lazard_critical_elimination_poly_prepare.
exact: lazard_critical_A_poly_structure_abstract.
Qed.

Lemma lazard_critical_h_poly_derivative a b g :
  (lazard_critical_h_poly a b g)^`() =
    lazard_critical_hprime_poly a b.
Proof.
rewrite /lazard_critical_h_poly /lazard_critical_hprime_poly
  /PC.lazard_quadratic_polynomial !derivE !mulr_natl.
finish_lazard_critical_elimination_poly_ring.
Qed.

Lemma lazard_critical_f_poly_derivative a b g d e :
  (lazard_critical_f_poly a b g d e)^`() =
    (2%:R : F)%:P * lazard_critical_h_poly a b g *
      lazard_critical_hprime_poly a b - d%:P.
Proof.
rewrite /lazard_critical_f_poly derivB deriv_exp
  lazard_critical_h_poly_derivative derivM derivC
  /lazard_critical_ell_poly derivD derivC.
rewrite derivX expr1 -mulr_natl mul0r add0r addr0 mulr1.
finish_lazard_critical_elimination_poly_ring.
Qed.

(** Polynomial versions of the first two pointwise eliminations. *)
Theorem lazard_critical_eliminate_f_polynomial a b g d e :
  lazard_critical_f_poly a b g d e =
    lazard_critical_ell_poly e *
      (lazard_critical_f_poly a b g d e)^`() +
    lazard_critical_h_poly a b g *
      lazard_critical_A_poly a b g e.
Proof.
rewrite lazard_critical_f_poly_derivative
  lazard_critical_A_poly_structure
  /lazard_critical_f_poly.
finish_lazard_critical_elimination_poly_ring.
Qed.

Lemma lazard_critical_eliminate_derivative_abstract
    (H L P D : {poly F}) :
  (2%:R : F)%:P * H * P - D =
    (4%:R : F)%:P * L * (P ^+ 2) - D +
      ((2%:R : F)%:P * P) *
        (H - (2%:R : F)%:P * L * P).
Proof. finish_lazard_critical_elimination_poly_ring. Qed.

Lemma lazard_critical_mul_not0 (x y : F) :
  x <> 0 -> y <> 0 -> x * y <> 0.
Proof.
move=> hx hy hxy.
have hxb : x != 0 by apply/negP=> /eqP; exact: hx.
have hyb : y != 0 by apply/negP=> /eqP; exact: hy.
move: (mulf_neq0 hxb hyb).
by rewrite hxy eqxx.
Qed.

Theorem lazard_critical_eliminate_derivative_polynomial a b g d e :
  (lazard_critical_f_poly a b g d e)^`() =
    lazard_critical_Q_poly a b g d e +
    ((2%:R : F)%:P * lazard_critical_hprime_poly a b) *
      lazard_critical_A_poly a b g e.
Proof.
rewrite lazard_critical_f_poly_derivative
  lazard_critical_A_poly_structure
  /lazard_critical_Q_poly.
exact: lazard_critical_eliminate_derivative_abstract.
Qed.

(** Expand one fixed coefficient of a concrete polynomial expression. *)
Ltac lazard_critical_expand_coefficient :=
  repeat first
    [ rewrite expr2
    | rewrite coefD | rewrite coefB | rewrite coefN
    | rewrite coefM;
      repeat rewrite big_ord_recl;
      rewrite big_ord0 /=
    | rewrite coefXn | rewrite coefX | rewrite coefC ];
  simpl.

Lemma lazard_size_MXaddC_le (p : {poly F}) (c : F) (n : nat) :
  leq (size p) n -> leq (size (p * 'X + c%:P)) n.+1.
Proof.
move=> hp.
rewrite size_MXaddC.
case: ifP=> _.
- exact: leq0n.
- exact: hp.
Qed.

Lemma lazard_pred_le_of_le_succ (m n : nat) :
  leq m n.+1 -> leq m.-1 n.
Proof. by case: m. Qed.

Lemma lazard_critical_A_poly_size_le a b g e :
  leq (size (lazard_critical_A_poly a b g e)) 4.
Proof.
rewrite /lazard_critical_A_poly /PC.lazard_cubic_polynomial.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
exact: size_polyC_leq1.
Qed.

Lemma lazard_critical_B_poly_size_le a b g d e :
  leq (size (lazard_critical_B_poly a b g d e)) 3.
Proof.
rewrite /lazard_critical_B_poly /PC.lazard_quadratic_polynomial.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
exact: size_polyC_leq1.
Qed.

Lemma lazard_critical_q_poly_size_le a b e :
  leq (size (lazard_critical_q_poly a b e)) 3.
Proof.
rewrite /lazard_critical_q_poly /PC.lazard_quadratic_polynomial.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
exact: size_polyC_leq1.
Qed.

Lemma lazard_critical_scaled_q_poly_size_le a b e :
  leq (size (lazard_critical_scaled_q_poly a b e)) 3.
Proof.
rewrite /lazard_critical_scaled_q_poly /PC.lazard_quadratic_polynomial.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
exact: size_polyC_leq1.
Qed.

Lemma lazard_critical_scaled_B_poly_size_le a b g d e :
  leq (size (lazard_critical_scaled_B_poly a b g d e)) 3.
Proof.
rewrite /lazard_critical_scaled_B_poly /PC.lazard_quadratic_polynomial.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
exact: size_polyC_leq1.
Qed.

Lemma lazard_critical_hprime_poly_size_le a b :
  leq (size (lazard_critical_hprime_poly a b)) 3.
Proof.
rewrite /lazard_critical_hprime_poly /PC.lazard_quadratic_polynomial.
apply: lazard_size_MXaddC_le.
apply: lazard_size_MXaddC_le.
exact: size_polyC_leq1.
Qed.

Lemma lazard_critical_Q_poly_size_le a b g d e :
  leq (size (lazard_critical_Q_poly a b g d e)) 6.
Proof.
rewrite /lazard_critical_Q_poly.
have hell : leq (size (lazard_critical_ell_poly e)) 2.
  by rewrite /lazard_critical_ell_poly size_XaddC.
have hhprime := lazard_critical_hprime_poly_size_le a b.
have hsquare :
    leq (size (lazard_critical_hprime_poly a b ^+ 2)) 5.
  have hs := size_poly_exp_leq (lazard_critical_hprime_poly a b) 2.
  apply: (leq_trans hs).
  move: hhprime.
  case: (size (lazard_critical_hprime_poly a b)) =>
    [|[|[|[|n]]]] //.
have hmul1 :
    leq (size ((4%:R : F)%:P * lazard_critical_ell_poly e)) 2.
  have hc := size_polyC_leq1 (4%:R : F).
  have hsum :
      leq (size ((4%:R : F)%:P) +
        size (lazard_critical_ell_poly e)) 3.
    exact: leq_add hc hell.
  exact: leq_trans (size_polyMleq _ _)
    (lazard_pred_le_of_le_succ hsum).
have hmul2 :
    leq (size ((4%:R : F)%:P * lazard_critical_ell_poly e *
      lazard_critical_hprime_poly a b ^+ 2)) 6.
  have hsum :
      leq (size ((4%:R : F)%:P * lazard_critical_ell_poly e) +
        size (lazard_critical_hprime_poly a b ^+ 2)) 7.
    exact: leq_add hmul1 hsquare.
  exact: leq_trans (size_polyMleq _ _)
    (lazard_pred_le_of_le_succ hsum).
have hdiff := size_polyD
  ((4%:R : F)%:P * lazard_critical_ell_poly e *
    lazard_critical_hprime_poly a b ^+ 2) (- d%:P).
apply: (leq_trans hdiff).
rewrite size_polyN geq_max hmul2.
have h16 : leq 1 6 by [].
exact: leq_trans (size_polyC_leq1 d) h16.
Qed.

Lemma lazard_critical_B_add_Aq_size_le a b g d e :
  leq (size (lazard_critical_B_poly a b g d e +
    lazard_critical_A_poly a b g e * lazard_critical_q_poly a b e)) 6.
Proof.
have hA := lazard_critical_A_poly_size_le a b g e.
have hq := lazard_critical_q_poly_size_le a b e.
have hAq :
    leq (size (lazard_critical_A_poly a b g e *
      lazard_critical_q_poly a b e)) 6.
  have hsum :
      leq (size (lazard_critical_A_poly a b g e) +
        size (lazard_critical_q_poly a b e)) 7.
    exact: leq_add hA hq.
  exact: leq_trans (size_polyMleq _ _)
    (lazard_pred_le_of_le_succ hsum).
have hadd := size_polyD (lazard_critical_B_poly a b g d e)
  (lazard_critical_A_poly a b g e * lazard_critical_q_poly a b e).
apply: (leq_trans hadd).
rewrite geq_max hAq andbT.
have h36 : leq 3 6 by [].
exact: leq_trans (lazard_critical_B_poly_size_le a b g d e) h36.
Qed.

(** Size bounds for the denominator-cleared identity. *)
Lemma lazard_critical_scaled_Q_poly_size_le a b g d e :
  leq (size ((125%:R : F)%:P *
    lazard_critical_Q_poly a b g d e)) 6.
Proof.
have hc := size_polyC_leq1 (125%:R : F).
have hQ := lazard_critical_Q_poly_size_le a b g d e.
have hsum :
    leq (size ((125%:R : F)%:P) +
      size (lazard_critical_Q_poly a b g d e)) 7.
  exact: leq_add hc hQ.
exact: leq_trans (size_polyMleq _ _)
  (lazard_pred_le_of_le_succ hsum).
Qed.

Lemma lazard_critical_scaled_B_add_Aq_size_le a b g d e :
  leq (size (lazard_critical_scaled_B_poly a b g d e +
    lazard_critical_A_poly a b g e *
      lazard_critical_scaled_q_poly a b e)) 6.
Proof.
have hA := lazard_critical_A_poly_size_le a b g e.
have hq := lazard_critical_scaled_q_poly_size_le a b e.
have hAq :
    leq (size (lazard_critical_A_poly a b g e *
      lazard_critical_scaled_q_poly a b e)) 6.
  have hsum :
      leq (size (lazard_critical_A_poly a b g e) +
        size (lazard_critical_scaled_q_poly a b e)) 7.
    exact: leq_add hA hq.
  exact: leq_trans (size_polyMleq _ _)
    (lazard_pred_le_of_le_succ hsum).
have hadd := size_polyD (lazard_critical_scaled_B_poly a b g d e)
  (lazard_critical_A_poly a b g e *
    lazard_critical_scaled_q_poly a b e).
apply: (leq_trans hadd).
rewrite geq_max hAq andbT.
have h36 : leq 3 6 by [].
exact: leq_trans
  (lazard_critical_scaled_B_poly_size_le a b g d e) h36.
Qed.

Lemma lazard_critical_scaled_division_polynomial a b g d e :
  (125%:R : F)%:P * lazard_critical_Q_poly a b g d e =
    lazard_critical_scaled_B_poly a b g d e +
      lazard_critical_A_poly a b g e *
        lazard_critical_scaled_q_poly a b e.
Proof.
rewrite lazard_critical_scale_Q_poly.
exact: esym (lazard_critical_scaled_B_add_Aq_polynomial a b g d e).
Qed.

(** The original division follows by cancelling the nonzero constant [125]. *)
Theorem lazard_critical_division_polynomial a b g d e
    (five_neq0 : (5%:R : F) != 0) :
  lazard_critical_Q_poly a b g d e =
    lazard_critical_B_poly a b g d e +
      lazard_critical_A_poly a b g e * lazard_critical_q_poly a b e.
Proof.
have hundred_twenty_five_poly_neq0 :
    ((125%:R : F)%:P : {poly F}) != 0.
  by rewrite polyC_eq0
    (CE.lazard_critical_hundred_twenty_five_neq0 five_neq0).
have hscaled :
    (125%:R : F)%:P * lazard_critical_Q_poly a b g d e =
      (125%:R : F)%:P *
        (lazard_critical_B_poly a b g d e +
          lazard_critical_A_poly a b g e * lazard_critical_q_poly a b e).
  rewrite lazard_critical_scaled_division_polynomial.
  rewrite -(lazard_critical_scale_B_poly a b g d e five_neq0).
  rewrite -(lazard_critical_scale_q_poly a b e five_neq0).
  finish_lazard_critical_elimination_poly_ring.
exact: (mulfI hundred_twenty_five_poly_neq0 hscaled).
Qed.

End PolynomialElimination.

Print Assumptions lazard_critical_eliminate_f_polynomial.
Print Assumptions lazard_critical_eliminate_derivative_polynomial.
Print Assumptions lazard_critical_division_polynomial.

End PolynomialFormulasLazardQuinticCriticalPolynomialElimination.
