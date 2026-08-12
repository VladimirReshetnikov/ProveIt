From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardCubicQuadraticElimination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Polynomial form of the three-case cubic--quadratic zero certificate.

    The scalar elimination theorem distinguishes an explicit common-root
    case, a zero linear-pseudo-remainder case, and a zero quadratic case.
    Here each case is converted into an actual nonconstant common polynomial
    divisor.  This is the exact input required by
    [LazardCriticalCommonDivisor]; no resultant-library axiom is used. *)
Module PolynomialFormulasLazardCriticalPolynomialCommonDivisor.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Local Open Scope ring_scope.

Section PolynomialCommonDivisor.

Variable F : fieldType.

(** Horner-form coefficient polynomials matching the scalar definitions in
    [LazardCubicQuadraticElimination]. *)
Definition lazard_cubic_polynomial
    (a0 a1 a2 a3 : F) : {poly F} :=
  (((a3%:P * 'X + a2%:P) * 'X + a1%:P) * 'X + a0%:P).

Definition lazard_quadratic_polynomial
    (b0 b1 b2 : F) : {poly F} :=
  ((b2%:P * 'X + b1%:P) * 'X + b0%:P).

Definition lazard_pseudo_quotient_polynomial
    (a2 a3 b1 b2 : F) : {poly F} :=
  (a3 * b2)%:P * 'X + (a2 * b2 - a3 * b1)%:P.

Add Ring lazard_critical_scalar_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_critical_scalar_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_cubic_polynomial_horner a0 a1 a2 a3 x :
  (lazard_cubic_polynomial a0 a1 a2 a3).[x] =
    CQ.lazard_cubic_value a0 a1 a2 a3 x.
Proof.
rewrite /lazard_cubic_polynomial /CQ.lazard_cubic_value !hornerE.
change (((a3 * x + a2) * x + a1) * x + a0 =
  a0 + a1 * x + (a2 * x) * x + ((a3 * x) * x) * x).
finish_lazard_critical_scalar_ring.
Qed.

Lemma lazard_quadratic_polynomial_horner b0 b1 b2 x :
  (lazard_quadratic_polynomial b0 b1 b2).[x] =
    CQ.lazard_quadratic_value b0 b1 b2 x.
Proof.
rewrite /lazard_quadratic_polynomial /CQ.lazard_quadratic_value !hornerE.
change ((b2 * x + b1) * x + b0 =
  b0 + b1 * x + (b2 * x) * x).
finish_lazard_critical_scalar_ring.
Qed.

(** A local ring bridge for identities in the polynomial ring itself. *)
Definition lazard_poly_ring_carrier : Type := {poly F}.
Definition lazard_poly_ring_zero : lazard_poly_ring_carrier := 0.
Definition lazard_poly_ring_one : lazard_poly_ring_carrier := 1.
Definition lazard_poly_ring_add :
    lazard_poly_ring_carrier -> lazard_poly_ring_carrier ->
      lazard_poly_ring_carrier := @GRing.add {poly F}.
Definition lazard_poly_ring_mul :
    lazard_poly_ring_carrier -> lazard_poly_ring_carrier ->
      lazard_poly_ring_carrier := @GRing.mul {poly F}.
Definition lazard_poly_ring_sub :
    lazard_poly_ring_carrier -> lazard_poly_ring_carrier ->
      lazard_poly_ring_carrier := fun p q => p - q.
Definition lazard_poly_ring_opp :
    lazard_poly_ring_carrier -> lazard_poly_ring_carrier :=
  @GRing.opp {poly F}.
Definition lazard_poly_ring_eq :
    lazard_poly_ring_carrier -> lazard_poly_ring_carrier -> Prop :=
  @eq lazard_poly_ring_carrier.

Lemma lazard_poly_ring_addE p q :
  p + q = lazard_poly_ring_add p q. Proof. reflexivity. Qed.
Lemma lazard_poly_ring_mulE p q :
  p * q = lazard_poly_ring_mul p q. Proof. reflexivity. Qed.
Lemma lazard_poly_ring_subE p q :
  p - q = lazard_poly_ring_sub p q. Proof. reflexivity. Qed.
Lemma lazard_poly_ring_oppE p :
  - p = lazard_poly_ring_opp p. Proof. reflexivity. Qed.
Lemma lazard_poly_ring_zeroE :
  (0 : {poly F}) = lazard_poly_ring_zero. Proof. reflexivity. Qed.
Lemma lazard_poly_ring_oneE :
  (1 : {poly F}) = lazard_poly_ring_one. Proof. reflexivity. Qed.

Lemma lazard_poly_ring_theory :
  @ring_theory lazard_poly_ring_carrier
    lazard_poly_ring_zero lazard_poly_ring_one
    lazard_poly_ring_add lazard_poly_ring_mul lazard_poly_ring_sub
    lazard_poly_ring_opp lazard_poly_ring_eq.
Proof.
constructor; unfold lazard_poly_ring_carrier, lazard_poly_ring_zero,
  lazard_poly_ring_one, lazard_poly_ring_add, lazard_poly_ring_mul,
  lazard_poly_ring_sub, lazard_poly_ring_opp, lazard_poly_ring_eq; intros.
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

Add Ring lazard_critical_polynomial_ring : lazard_poly_ring_theory.
Opaque lazard_poly_ring_zero lazard_poly_ring_one lazard_poly_ring_add
  lazard_poly_ring_mul lazard_poly_ring_sub lazard_poly_ring_opp
  lazard_poly_ring_eq.

Ltac finish_lazard_critical_polynomial_ring :=
  repeat first
    [ rewrite polyC_exp | rewrite expr2 | rewrite polyCB | rewrite polyCN
    | rewrite polyCM | rewrite polyCD | rewrite polyC_natr ];
  repeat first
    [ rewrite lazard_poly_ring_addE | rewrite lazard_poly_ring_mulE
    | rewrite lazard_poly_ring_subE | rewrite lazard_poly_ring_oppE
    | rewrite lazard_poly_ring_zeroE | rewrite lazard_poly_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (lazard_poly_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_abstract_cubic_quadratic_pseudo_division
    (A0 A1 A2 A3 B0 B1 B2 XX : {poly F}) :
  (B2 * B2) * (((A3 * XX + A2) * XX + A1) * XX + A0) =
    ((A3 * B2) * XX + (A2 * B2 - A3 * B1)) *
        ((B2 * XX + B1) * XX + B0) +
      (A1 * (B2 * B2) - A3 * B0 * B2 - A2 * B1 * B2 +
        A3 * (B1 * B1)) * XX +
      (A0 * (B2 * B2) - A2 * B0 * B2 + A3 * B0 * B1).
Proof.
finish_lazard_critical_polynomial_ring.
Qed.

(** Polynomial pseudo-division.  It is the scalar identity from the
    elimination file with the indeterminate retained, so it has no
    denominator hypothesis. *)
Theorem lazard_cubic_quadratic_polynomial_pseudo_division
    (a0 a1 a2 a3 b0 b1 b2 : F) :
  b2 ^+ 2 *: lazard_cubic_polynomial a0 a1 a2 a3 =
    lazard_pseudo_quotient_polynomial a2 a3 b1 b2 *
      lazard_quadratic_polynomial b0 b1 b2 +
    (CQ.lazard_cubic_quadratic_R1 a1 a2 a3 b0 b1 b2)%:P * 'X +
    (CQ.lazard_cubic_quadratic_R0 a0 a2 a3 b0 b1 b2)%:P.
Proof.
rewrite -mul_polyC /lazard_cubic_polynomial
  /lazard_quadratic_polynomial /lazard_pseudo_quotient_polynomial
  /CQ.lazard_cubic_quadratic_R1 /CQ.lazard_cubic_quadratic_R0.
repeat first
  [ rewrite polyC_exp | rewrite expr2 | rewrite polyCB | rewrite polyCN
  | rewrite polyCM | rewrite polyCD | rewrite polyC_natr ].
exact: lazard_abstract_cubic_quadratic_pseudo_division.
Qed.

Lemma lazard_quadratic_polynomial_size b0 b1 b2
    (b2_neq0 : b2 != 0) :
  size (lazard_quadratic_polynomial b0 b1 b2) = 3%N.
Proof.
have hb2C : (b2%:P : {poly F}) != 0 by rewrite polyC_eq0.
have hinner : size (b2%:P * 'X + b1%:P) = 2%N.
  by rewrite size_MXaddC (negPf hb2C) /= size_polyC b2_neq0.
have hinner0 : (b2%:P * 'X + b1%:P : {poly F}) != 0.
  by rewrite -size_poly_gt0 hinner.
rewrite /lazard_quadratic_polynomial size_MXaddC
  (negPf hinner0) /= hinner.
reflexivity.
Qed.

Lemma lazard_cubic_polynomial_size a0 a1 a2 a3
    (a3_neq0 : a3 != 0) :
  size (lazard_cubic_polynomial a0 a1 a2 a3) = 4%N.
Proof.
have ha3C : (a3%:P : {poly F}) != 0 by rewrite polyC_eq0.
have h1 : size (a3%:P * 'X + a2%:P) = 2%N.
  by rewrite size_MXaddC (negPf ha3C) /= size_polyC a3_neq0.
have h1nz : (a3%:P * 'X + a2%:P : {poly F}) != 0.
  by rewrite -size_poly_gt0 h1.
have h2 :
    size ((a3%:P * 'X + a2%:P) * 'X + a1%:P) = 3%N.
  by rewrite size_MXaddC (negPf h1nz) /= h1.
have h2nz :
    ((a3%:P * 'X + a2%:P) * 'X + a1%:P : {poly F}) != 0.
  by rewrite -size_poly_gt0 h2.
rewrite /lazard_cubic_polynomial size_MXaddC
  (negPf h2nz) /= h2.
reflexivity.
Qed.

(** Complete conversion of a zero value of the explicit thirteen-term
    scalar into a nonconstant common divisor of the corresponding cubic and
    quadratic polynomials.  This semantic consequence is proved directly;
    it does not rely on an identification with a library resultant. *)
Theorem lazard_resultant_zero_nonconstant_common_divisor
    (a0 a1 a2 a3 b0 b1 b2 : F)
    (a3_neq0 : a3 != 0)
    (hresultant :
      CQ.lazard_cubic_quadratic_resultant_value
        a0 a1 a2 a3 b0 b1 b2 = 0) :
  exists u : {poly F},
    (1 < size u)%N /\
    (u %| lazard_cubic_polynomial a0 a1 a2 a3) /\
    (u %| lazard_quadratic_polynomial b0 b1 b2).
Proof.
have hcases := CQ.lazard_cubic_quadratic_zero_certificate
  a3_neq0 hresultant.
case: hcases=> [[x [hAx hBx]] | [[b2_neq0 [hR1 hR0]] |
    [hb2 [hb1 hb0]]]].
- exists ('X - x%:P); split.
  + by rewrite size_XsubC.
  + split.
    * by rewrite -root_factor_theorem rootE
        lazard_cubic_polynomial_horner hAx eqxx.
    * by rewrite -root_factor_theorem rootE
        lazard_quadratic_polynomial_horner hBx eqxx.
- exists (lazard_quadratic_polynomial b0 b1 b2); split.
  + by rewrite lazard_quadratic_polynomial_size.
  + split; last exact: dvdpp.
    have hpseudo := lazard_cubic_quadratic_polynomial_pseudo_division
      a0 a1 a2 a3 b0 b1 b2.
    rewrite hR1 hR0 !polyC0 !mul0r !addr0 in hpseudo.
    exact: eq_dvdp (expf_neq0 2 b2_neq0) hpseudo.
- exists (lazard_cubic_polynomial a0 a1 a2 a3); split.
  + by rewrite lazard_cubic_polynomial_size.
  + split; first exact: dvdpp.
    rewrite /lazard_quadratic_polynomial hb2 hb1 hb0
      !polyC0 !mul0r !addr0 mul0r.
    by rewrite dvdp0.
Qed.

End PolynomialCommonDivisor.

Print Assumptions lazard_cubic_quadratic_polynomial_pseudo_division.
Print Assumptions lazard_resultant_zero_nonconstant_common_divisor.

End PolynomialFormulasLazardCriticalPolynomialCommonDivisor.
