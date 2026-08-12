From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootProjections LazardQuinticVieta
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Exact normalization and Tschirnhaus translation for a general quintic.

    The formula modules work with the monic depressed polynomial

      [Y^5 + p Y^3 + q Y^2 + r Y + s].

    This module supplies the previously missing coefficient-level bridge.
    For [a != 0], substituting [X = Y - b/(5a)] in the general quintic is
    exactly [a] times its depressed form.  The final theorems transport a
    five-root Vieta factorization, including multiplicities, back to the
    original general quintic.  No root choice or solvability assumption is
    hidden in this normalization step. *)
Module PolynomialFormulasLazardQuinticGeneralDepression.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Module V := PolynomialFormulasLazardQuinticVieta.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section GeneralDepression.

Variable F : fieldType.

Add Ring lazard_general_depression_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_general_depression_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Coefficients of [a X^5 + b X^4 + c X^3 + d X^2 + e X + f]. *)
Record LazardGeneralQuinticCoefficients := Build_LazardGeneralQuinticCoefficients {
  lazard_general_a : F;
  lazard_general_b : F;
  lazard_general_c : F;
  lazard_general_d : F;
  lazard_general_e : F;
  lazard_general_f : F
}.

Definition lazard_general_quintic_eval
    (c : LazardGeneralQuinticCoefficients) (x : F) : F :=
  lazard_general_a c * x ^+ 5 +
  lazard_general_b c * x ^+ 4 +
  lazard_general_c c * x ^+ 3 +
  lazard_general_d c * x ^+ 2 +
  lazard_general_e c * x + lazard_general_f c.

(** Translation amount in [X = Y - b/(5a)]. *)
Definition lazard_depression_shift
    (c : LazardGeneralQuinticCoefficients) : F :=
  lazard_general_b c / (5%:R * lazard_general_a c).

(** Depressed coefficients, written in a factored form tailored to the
    exact expansion proof.  The four public cancellation lemmas below show
    directly that these are the coefficients obtained by expansion. *)
Definition lazard_depress_general
    (c : LazardGeneralQuinticCoefficients) :
    LazardDepressedRootCoefficients F :=
  let a := lazard_general_a c in
  let h := lazard_depression_shift c in
  {| lazard_root_p :=
       (lazard_general_c c - 10%:R * a * h ^+ 2) / a;
     lazard_root_q :=
       (lazard_general_d c - 3%:R * lazard_general_c c * h +
          20%:R * a * h ^+ 3) / a;
     lazard_root_r :=
       (lazard_general_e c - 2%:R * lazard_general_d c * h +
          3%:R * lazard_general_c c * h ^+ 2 -
          15%:R * a * h ^+ 4) / a;
     lazard_root_s :=
       (lazard_general_f c - lazard_general_e c * h +
          lazard_general_d c * h ^+ 2 -
          lazard_general_c c * h ^+ 3 + 4%:R * a * h ^+ 5) / a |}.

Lemma lazard_depression_denominator_neq0
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0)
    (five_neq0 : (5%:R : F) != 0) :
  5%:R * lazard_general_a c != 0.
Proof. exact (mulf_neq0 five_neq0 ha). Qed.

Lemma lazard_depression_shift_cancel
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0)
    (five_neq0 : (5%:R : F) != 0) :
  (5%:R * lazard_general_a c) * lazard_depression_shift c =
    lazard_general_b c.
Proof.
have hden := lazard_depression_denominator_neq0 (c := c) ha five_neq0.
rewrite /lazard_depression_shift mulrC.
exact (divfK hden _).
Qed.

Lemma lazard_depress_general_p_cancel
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0) :
  lazard_general_a c * lazard_root_p (lazard_depress_general c) =
    lazard_general_c c -
      10%:R * lazard_general_a c * lazard_depression_shift c ^+ 2.
Proof.
rewrite /lazard_depress_general /= [lazard_general_a c * _]mulrC.
exact (divfK ha _).
Qed.

Lemma lazard_depress_general_q_cancel
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0) :
  lazard_general_a c * lazard_root_q (lazard_depress_general c) =
    lazard_general_d c -
      3%:R * lazard_general_c c * lazard_depression_shift c +
      20%:R * lazard_general_a c * lazard_depression_shift c ^+ 3.
Proof.
rewrite /lazard_depress_general /= [lazard_general_a c * _]mulrC.
exact (divfK ha _).
Qed.

Lemma lazard_depress_general_r_cancel
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0) :
  lazard_general_a c * lazard_root_r (lazard_depress_general c) =
    lazard_general_e c -
      2%:R * lazard_general_d c * lazard_depression_shift c +
      3%:R * lazard_general_c c * lazard_depression_shift c ^+ 2 -
      15%:R * lazard_general_a c * lazard_depression_shift c ^+ 4.
Proof.
rewrite /lazard_depress_general /= [lazard_general_a c * _]mulrC.
exact (divfK ha _).
Qed.

Lemma lazard_depress_general_s_cancel
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0) :
  lazard_general_a c * lazard_root_s (lazard_depress_general c) =
    lazard_general_f c -
      lazard_general_e c * lazard_depression_shift c +
      lazard_general_d c * lazard_depression_shift c ^+ 2 -
      lazard_general_c c * lazard_depression_shift c ^+ 3 +
      4%:R * lazard_general_a c * lazard_depression_shift c ^+ 5.
Proof.
rewrite /lazard_depress_general /= [lazard_general_a c * _]mulrC.
exact (divfK ha _).
Qed.

(** Exact normalization and Tschirnhaus identity. *)
Theorem lazard_general_depression_eval
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0)
    (five_neq0 : (5%:R : F) != 0) (y : F) :
  lazard_general_quintic_eval c (y - lazard_depression_shift c) =
    lazard_general_a c *
      V.lazard_depressed_quintic_eval
        (lazard_root_p (lazard_depress_general c))
        (lazard_root_q (lazard_depress_general c))
        (lazard_root_r (lazard_depress_general c))
        (lazard_root_s (lazard_depress_general c)) y.
Proof.
pose h := lazard_depression_shift c.
have hb := lazard_depression_shift_cancel (c := c) ha five_neq0.
have hp := lazard_depress_general_p_cancel (c := c) ha.
have hq := lazard_depress_general_q_cancel (c := c) ha.
have hr := lazard_depress_general_r_cancel (c := c) ha.
have hs := lazard_depress_general_s_cancel (c := c) ha.
fold h in hb, hp, hq, hr, hs |- *.
rewrite /lazard_general_quintic_eval /V.lazard_depressed_quintic_eval.
have hright :
    lazard_general_a c *
        (y ^+ 5 + lazard_root_p (lazard_depress_general c) * y ^+ 3 +
          lazard_root_q (lazard_depress_general c) * y ^+ 2 +
          lazard_root_r (lazard_depress_general c) * y +
          lazard_root_s (lazard_depress_general c)) =
      lazard_general_a c * y ^+ 5 +
        (lazard_general_a c *
          lazard_root_p (lazard_depress_general c)) * y ^+ 3 +
        (lazard_general_a c *
          lazard_root_q (lazard_depress_general c)) * y ^+ 2 +
        (lazard_general_a c *
          lazard_root_r (lazard_depress_general c)) * y +
        lazard_general_a c *
          lazard_root_s (lazard_depress_general c).
  finish_lazard_general_depression_ring.
rewrite hright hp hq hr hs -hb.
finish_lazard_general_depression_ring.
Qed.

(** Every depressed root translates to a root of the original polynomial. *)
Theorem lazard_general_root_of_depressed_root
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0)
    (five_neq0 : (5%:R : F) != 0) (y : F)
    (hy : V.lazard_depressed_quintic_eval
      (lazard_root_p (lazard_depress_general c))
      (lazard_root_q (lazard_depress_general c))
      (lazard_root_r (lazard_depress_general c))
      (lazard_root_s (lazard_depress_general c)) y = 0) :
  lazard_general_quintic_eval c (y - lazard_depression_shift c) = 0.
Proof.
rewrite (lazard_general_depression_eval (c := c) ha five_neq0 y) hy mulr0.
reflexivity.
Qed.

(** In a field, a zero product of the five displayed linear factors selects
    one of their indexed roots.  Keeping this finite bookkeeping here avoids
    repeating the same nested zero-product argument in every formula-level
    completeness theorem. *)
Lemma lazard_five_linear_factors_zero_exists
    (x : F) (xv : 'I_5 -> F) :
  (x - xv o0) * (x - xv o1) * (x - xv o2) *
      (x - xv o3) * (x - xv o4) = 0 ->
  exists k : 'I_5, x = xv k.
Proof.
move=> hzero.
have hzero_bool :
    (x - xv o0) * (x - xv o1) * (x - xv o2) *
      (x - xv o3) * (x - xv o4) == 0.
  apply/eqP.
  exact: hzero.
move: hzero_bool; rewrite !mulf_eq0.
move/orP=> [h0123 | h4].
- move/orP: h0123=> [h012 | h3].
  + move/orP: h012=> [h01 | h2].
    * move/orP: h01=> [h0 | h1].
      -- exists o0.
         by move: h0; rewrite subr_eq0 => /eqP.
      -- exists o1.
         by move: h1; rewrite subr_eq0 => /eqP.
    * exists o2.
      by move: h2; rewrite subr_eq0 => /eqP.
  + exists o3.
    by move: h3; rewrite subr_eq0 => /eqP.
- exists o4.
  by move: h4; rewrite subr_eq0 => /eqP.
Qed.

(** A five-root Vieta certificate for the depressed form gives an exact
    multiplicity-preserving factorization of the original quintic. *)
Theorem lazard_general_vieta_eval_factorization
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0)
    (five_neq0 : (5%:R : F) != 0)
    (xv : 'I_5 -> F)
    (hv : V.lazard_depressed_five_root_relations
      (lazard_root_p (lazard_depress_general c))
      (lazard_root_q (lazard_depress_general c))
      (lazard_root_r (lazard_depress_general c))
      (lazard_root_s (lazard_depress_general c)) xv)
    (x : F) :
  lazard_general_quintic_eval c x =
    lazard_general_a c *
      (x - (xv o0 - lazard_depression_shift c)) *
      (x - (xv o1 - lazard_depression_shift c)) *
      (x - (xv o2 - lazard_depression_shift c)) *
      (x - (xv o3 - lazard_depression_shift c)) *
      (x - (xv o4 - lazard_depression_shift c)).
Proof.
pose h := lazard_depression_shift c.
have htranslated := lazard_general_depression_eval
  (c := c) ha five_neq0 (x + h).
fold h in htranslated |- *.
have hcancel : x + h - h = x.
  finish_lazard_general_depression_ring.
rewrite hcancel in htranslated.
rewrite (V.lazard_depressed_vieta_eval_factorization hv (x + h))
  in htranslated.
rewrite htranslated.
finish_lazard_general_depression_ring.
Qed.

(** The translated five values are all roots of the original polynomial. *)
Corollary lazard_general_vieta_output_root
    (c : LazardGeneralQuinticCoefficients)
    (ha : lazard_general_a c != 0)
    (five_neq0 : (5%:R : F) != 0)
    (xv : 'I_5 -> F)
    (hv : V.lazard_depressed_five_root_relations
      (lazard_root_p (lazard_depress_general c))
      (lazard_root_q (lazard_depress_general c))
      (lazard_root_r (lazard_depress_general c))
      (lazard_root_s (lazard_depress_general c)) xv)
    (k : 'I_5) :
  lazard_general_quintic_eval c
    (xv k - lazard_depression_shift c) = 0.
Proof.
apply: (lazard_general_root_of_depressed_root (c := c) ha five_neq0).
rewrite (V.lazard_depressed_vieta_eval_factorization hv).
case: k=> [[|[|[|[|[|k]]]]] hk].
- have -> : @Ordinal 5 0 hk = o0 by apply: val_inj.
  by rewrite subrr !mul0r.
- have -> : @Ordinal 5 1 hk = o1 by apply: val_inj.
  by rewrite subrr !mulr0 !mul0r.
- have -> : @Ordinal 5 2 hk = o2 by apply: val_inj.
  by rewrite subrr !mulr0 !mul0r.
- have -> : @Ordinal 5 3 hk = o3 by apply: val_inj.
  by rewrite subrr !mulr0 !mul0r.
- have -> : @Ordinal 5 4 hk = o4 by apply: val_inj.
  by rewrite subrr !mulr0.
- by move: hk.
Qed.

End GeneralDepression.

End PolynomialFormulasLazardQuinticGeneralDepression.
