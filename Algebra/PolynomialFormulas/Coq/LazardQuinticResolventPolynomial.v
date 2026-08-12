From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The coefficient-side Lazard--Cayley sextic from Section 7.

    This file deliberately defines the displayed polynomial itself, rather
    than identifying it only up to a nonzero scalar.  The separate executable
    Dummit resolvent uses an integral homogeneous scale; any bridge to that
    polynomial must therefore state the scale explicitly. *)
Module PolynomialFormulasLazardQuinticResolventPolynomial.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section ResolventPolynomial.

Variable F : fieldType.

(** The discriminant of [X^5 + p X^3 + q X^2 + r X + s], in the exact
    coefficient normalization used in Lazard's Section 7. *)
Definition lazard_resolvent_discriminant
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  108%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_s c ^+ 2 -
    72%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
      RP.lazard_root_r c * RP.lazard_root_s c +
    16%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_r c ^+ 3 +
    16%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 3 *
      RP.lazard_root_s c -
    4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c ^+ 2 -
    900%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c *
      RP.lazard_root_s c ^+ 2 +
    825%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_s c ^+ 2 +
    560%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_r c ^+ 2 * RP.lazard_root_s c -
    128%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 4 -
    630%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
      RP.lazard_root_r c * RP.lazard_root_s c +
    144%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c ^+ 3 -
    3750%:R * RP.lazard_root_p c * RP.lazard_root_q c *
      RP.lazard_root_s c ^+ 3 +
    2000%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 *
      RP.lazard_root_s c ^+ 2 +
    108%:R * RP.lazard_root_q c ^+ 5 * RP.lazard_root_s c -
    27%:R * RP.lazard_root_q c ^+ 4 * RP.lazard_root_r c ^+ 2 +
    2250%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c *
      RP.lazard_root_s c ^+ 2 -
    1600%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 3 *
      RP.lazard_root_s c +
    256%:R * RP.lazard_root_r c ^+ 5 +
    3125%:R * RP.lazard_root_s c ^+ 4.

Definition lazard_resolvent_core_linear
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 6%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
    2%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
    50%:R * RP.lazard_root_q c * RP.lazard_root_s c +
    24%:R * RP.lazard_root_r c ^+ 2.

Definition lazard_resolvent_core_constant
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  - 15%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
      RP.lazard_root_s c -
    16%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c ^+ 2 +
    13%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 *
      RP.lazard_root_r c +
    125%:R * RP.lazard_root_p c * RP.lazard_root_s c ^+ 2 -
    2%:R * RP.lazard_root_q c ^+ 4 -
    200%:R * RP.lazard_root_q c * RP.lazard_root_r c *
      RP.lazard_root_s c +
    64%:R * RP.lazard_root_r c ^+ 3.

(** Twice the monic cubic whose square is the first term of the sextic. *)
Definition lazard_resolvent_core
    (c : RP.LazardDepressedRootCoefficients F) (z : F) : F :=
  2%:R * z ^+ 3 + 8%:R * z ^+ 2 * RP.lazard_root_r c +
    lazard_resolvent_core_linear c * z +
    lazard_resolvent_core_constant c.

Definition lazard_resolvent_cubic_a
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  4%:R * RP.lazard_root_r c.

Definition lazard_resolvent_cubic_b
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  lazard_resolvent_core_linear c / 2%:R.

Definition lazard_resolvent_cubic_g
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  lazard_resolvent_core_constant c / 2%:R.

Definition lazard_resolvent_linear_e
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  3%:R * RP.lazard_root_r c + RP.lazard_root_p c ^+ 2 / 4%:R.

Definition lazard_resolvent_cubic
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  'X ^+ 3 + (lazard_resolvent_cubic_a c)%:P * 'X ^+ 2 +
    (lazard_resolvent_cubic_b c)%:P * 'X +
    (lazard_resolvent_cubic_g c)%:P.

Definition lazard_resolvent_line
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  'X + (lazard_resolvent_linear_e c)%:P.

(** Lazard's monic sextic, with no homogeneous coefficient scale. *)
Definition lazard_resolvent_polynomial
    (c : RP.LazardDepressedRootCoefficients F) : {poly F} :=
  lazard_resolvent_cubic c ^+ 2 -
    lazard_resolvent_discriminant c *: lazard_resolvent_line c.

Definition lazard_resolvent_eval
    (c : RP.LazardDepressedRootCoefficients F) (z : F) : F :=
  (lazard_resolvent_core c z / 2%:R) ^+ 2 -
    (z + 3%:R * RP.lazard_root_r c +
      RP.lazard_root_p c ^+ 2 / 4%:R) *
      lazard_resolvent_discriminant c.

(** Cayley's variable [Theta] translated to Lazard's scalar invariant
    variable [z = i4]. *)
Definition lazard_resolvent_cayley_theta
    (c : RP.LazardDepressedRootCoefficients F) (z : F) : F :=
  4%:R * z + RP.lazard_root_p c ^+ 2 +
    12%:R * RP.lazard_root_r c.

Add Ring lazard_resolvent_ring : (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_resolvent_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_resolvent_cubic_horner c z :
  (lazard_resolvent_cubic c).[z] =
    z ^+ 3 + lazard_resolvent_cubic_a c * z ^+ 2 +
      lazard_resolvent_cubic_b c * z + lazard_resolvent_cubic_g c.
Proof. by rewrite /lazard_resolvent_cubic !hornerE. Qed.

Lemma lazard_resolvent_line_horner c z :
  (lazard_resolvent_line c).[z] = z + lazard_resolvent_linear_e c.
Proof. by rewrite /lazard_resolvent_line !hornerE. Qed.

Lemma lazard_resolvent_polynomial_horner_square c z :
  (lazard_resolvent_polynomial c).[z] =
    (z ^+ 3 + lazard_resolvent_cubic_a c * z ^+ 2 +
      lazard_resolvent_cubic_b c * z + lazard_resolvent_cubic_g c) ^+ 2 -
    lazard_resolvent_discriminant c *
      (z + lazard_resolvent_linear_e c).
Proof.
rewrite /lazard_resolvent_polynomial hornerD hornerN horner_exp hornerZ
  lazard_resolvent_cubic_horner lazard_resolvent_line_horner.
reflexivity.
Qed.

(** The displayed cubic really is one half of the fraction-free core. *)
Lemma lazard_resolvent_two_mul_cubic_horner c z
    (two_neq0 : (2%:R : F) != 0) :
  2%:R * (lazard_resolvent_cubic c).[z] =
    lazard_resolvent_core c z.
Proof.
have hb :
    2%:R * lazard_resolvent_cubic_b c =
      lazard_resolvent_core_linear c.
  rewrite /lazard_resolvent_cubic_b [2%:R * _]mulrC.
  by rewrite divfK.
have hg :
    2%:R * lazard_resolvent_cubic_g c =
      lazard_resolvent_core_constant c.
  rewrite /lazard_resolvent_cubic_g [2%:R * _]mulrC.
  by rewrite divfK.
rewrite lazard_resolvent_cubic_horner /lazard_resolvent_core
  /lazard_resolvent_cubic_a -hb -hg.
finish_lazard_resolvent_ring.
Qed.

Lemma lazard_resolvent_cubic_horner_core c z
    (two_neq0 : (2%:R : F) != 0) :
  (lazard_resolvent_cubic c).[z] =
    lazard_resolvent_core c z / 2%:R.
Proof.
apply: (mulfI two_neq0).
rewrite [2%:R * (_ / 2%:R)]mulrC divfK //.
exact: lazard_resolvent_two_mul_cubic_horner.
Qed.

(** Evaluation of the literal monic polynomial is exactly Lazard's printed
    scalar sextic expression. *)
Theorem lazard_resolvent_polynomial_horner c z
    (two_neq0 : (2%:R : F) != 0) :
  (lazard_resolvent_polynomial c).[z] = lazard_resolvent_eval c z.
Proof.
rewrite /lazard_resolvent_polynomial hornerD hornerN horner_exp hornerZ
  (lazard_resolvent_cubic_horner_core c z two_neq0)
  lazard_resolvent_line_horner
  /lazard_resolvent_eval /lazard_resolvent_linear_e.
finish_lazard_resolvent_ring.
Qed.

(** The fraction-free equation printed by Lazard is equivalent to vanishing
    of the monic sextic. *)
Theorem lazard_resolvent_eval_eq0_iff c z
    (two_neq0 : (2%:R : F) != 0) :
  lazard_resolvent_eval c z = 0 <->
    lazard_resolvent_cayley_theta c z *
      lazard_resolvent_discriminant c =
    lazard_resolvent_core c z ^+ 2.
Proof.
have four_neq0 : (4%:R : F) != 0.
  rewrite (@NR.lazard_numerator_four_natrE F).
  by rewrite mulf_neq0 //.
have hscaled :
    lazard_resolvent_core c z ^+ 2 -
      lazard_resolvent_cayley_theta c z *
        lazard_resolvent_discriminant c =
    4%:R * lazard_resolvent_eval c z.
  rewrite /lazard_resolvent_eval /lazard_resolvent_cayley_theta.
  have hcore :
      4%:R * (lazard_resolvent_core c z / 2%:R) ^+ 2 =
        lazard_resolvent_core c z ^+ 2.
    have hhalf :
        2%:R * (lazard_resolvent_core c z / 2%:R) =
          lazard_resolvent_core c z.
      rewrite [2%:R * (_ / 2%:R)]mulrC.
      by rewrite divfK.
    rewrite -[lazard_resolvent_core c z in RHS]hhalf
      (@NR.lazard_numerator_four_natrE F).
    finish_lazard_resolvent_ring.
  rewrite -hcore.
  have hquarter :
      4%:R * (RP.lazard_root_p c ^+ 2 / 4%:R) =
        RP.lazard_root_p c ^+ 2.
    rewrite [4%:R * (_ / 4%:R)]mulrC.
    by rewrite divfK.
  have htheta :
      4%:R *
          (z + 3%:R * RP.lazard_root_r c +
            RP.lazard_root_p c ^+ 2 / 4%:R) =
        4%:R * z + RP.lazard_root_p c ^+ 2 +
          12%:R * RP.lazard_root_r c.
    rewrite -[RP.lazard_root_p c ^+ 2 in RHS]hquarter.
    rewrite !mulrDr mulrA /=.
    rewrite -natrM /=.
    by rewrite addrAC.
  rewrite -htheta.
  rewrite [RHS]mulrBr.
  have hassoc :
      4%:R *
          (z + 3%:R * RP.lazard_root_r c +
            RP.lazard_root_p c ^+ 2 / 4%:R) *
          lazard_resolvent_discriminant c =
        4%:R *
          ((z + 3%:R * RP.lazard_root_r c +
            RP.lazard_root_p c ^+ 2 / 4%:R) *
            lazard_resolvent_discriminant c).
    exact: esym (mulrA _ _ _).
  rewrite hassoc.
  reflexivity.
split.
- move=> hzero.
  have hdiff :
      lazard_resolvent_core c z ^+ 2 -
        lazard_resolvent_cayley_theta c z *
          lazard_resolvent_discriminant c = 0.
    by rewrite hscaled hzero mulr0.
  apply/eqP.
  move/eqP: hdiff.
  by rewrite subr_eq0 eq_sym.
- move=> heq.
  apply: (mulfI four_neq0).
  rewrite mulr0 -hscaled.
  by rewrite heq subrr.
Qed.

(** A coefficient-opaque derivative calculation for a monic cubic.  Keeping
    this generic prevents simplification from traversing the large Lazard
    coefficient formulas. *)
Lemma monic_cubic_derivative_horner (a b g z : F) :
  ('X ^+ 3 + a%:P * 'X ^+ 2 + b%:P * 'X + g%:P)^`().[z] =
    3%:R * z ^+ 2 + 2%:R * a * z + b.
Proof.
rewrite !derivD !deriv_mulC !derivXn derivX derivC /= !addr0 !mulr1.
rewrite !hornerD !hornerM !hornerC !hornerMn !hornerXn.
rewrite !expr1.
rewrite [3%:R * z ^+ 2]mulr_natl [2%:R * a]mulr_natl expr2.
by rewrite mulrDr mulrDl.
Qed.

(** Pointwise derivative of the monic cubic. *)
Lemma lazard_resolvent_cubic_derivative_horner c z :
  (lazard_resolvent_cubic c)^`().[z] =
    3%:R * z ^+ 2 + 2%:R * lazard_resolvent_cubic_a c * z +
      lazard_resolvent_cubic_b c.
Proof.
rewrite /lazard_resolvent_cubic.
exact: monic_cubic_derivative_horner.
Qed.

(** A coefficient-opaque derivative calculation for a squared polynomial
    minus a scalar multiple of a monic line. *)
Lemma square_minus_line_derivative_horner
    (h : {poly F}) (d e z : F) :
  (h ^+ 2 - d *: ('X + e%:P))^`().[z] =
    2%:R * h.[z] * h^`().[z] - d.
Proof.
rewrite expr2 derivB derivM derivZ derivD derivX derivC.
rewrite !hornerE /=.
rewrite [h^`().[z] * h.[z]]mulrC.
rewrite [2%:R * h.[z]]mulr_natl.
by rewrite mulrDl.
Qed.

(** Pointwise derivative of [h^2 - d (X+e)]. *)
Theorem lazard_resolvent_polynomial_derivative_horner c z :
  (lazard_resolvent_polynomial c)^`().[z] =
    2%:R * (lazard_resolvent_cubic c).[z] *
      (lazard_resolvent_cubic c)^`().[z] -
    lazard_resolvent_discriminant c.
Proof.
rewrite /lazard_resolvent_polynomial /lazard_resolvent_line.
exact: square_minus_line_derivative_horner.
Qed.

End ResolventPolynomial.

Print Assumptions lazard_resolvent_polynomial_horner.
Print Assumptions lazard_resolvent_eval_eq0_iff.
Print Assumptions lazard_resolvent_polynomial_derivative_horner.

End PolynomialFormulasLazardQuinticResolventPolynomial.
