From Stdlib Require Import Ring Field.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticResolventPolynomial
  LazardCubicQuadraticElimination.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Pointwise Euclidean elimination for Lazard's square-minus-linear sextic.

    This is the general algebraic part of the determinant/separability bridge.
    It is independent of the large coefficient certificate identifying the
    final scalar with the Figure-3 determinant. *)
Module PolynomialFormulasLazardQuinticCriticalElimination.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Local Open Scope ring_scope.

Section CriticalElimination.

Variable F : fieldType.

Definition lazard_square_linear_h (a b g x : F) : F :=
  x ^+ 3 + a * x ^+ 2 + b * x + g.

Definition lazard_square_linear_hprime (a b x : F) : F :=
  3%:R * x ^+ 2 + 2%:R * a * x + b.

Definition lazard_square_linear_ell (e x : F) : F := x + e.

Definition lazard_square_linear_f (a b g d e x : F) : F :=
  lazard_square_linear_h a b g x ^+ 2 -
    d * lazard_square_linear_ell e x.

Definition lazard_square_linear_fprime (a b g d x : F) : F :=
  2%:R * lazard_square_linear_h a b g x *
    lazard_square_linear_hprime a b x - d.

Definition lazard_square_linear_critical_cubic
    (a b g e x : F) : F :=
  lazard_square_linear_h a b g x -
    2%:R * lazard_square_linear_ell e x *
      lazard_square_linear_hprime a b x.

Definition lazard_square_linear_critical_quintic
    (a b g d e x : F) : F :=
  4%:R * lazard_square_linear_ell e x *
      lazard_square_linear_hprime a b x ^+ 2 - d.

Definition lazard_square_linear_critical_quotient
    (a b e x : F) : F :=
  (- 36%:R / 5%:R) * x ^+ 2 +
    ((- 132%:R * a + 36%:R * e) / 25%:R) * x +
    (- 4%:R * a ^+ 2 + 204%:R * a * e - 420%:R * b -
      216%:R * e ^+ 2) / 125%:R.

Definition lazard_square_linear_critical_remainder0
    (a b g d e : F) : F :=
  - (8%:R * a ^+ 2 * b * e - 4%:R * a ^+ 2 * g -
      408%:R * a * b * e ^+ 2 + 204%:R * a * e * g +
      340%:R * b ^+ 2 * e + 432%:R * b * e ^+ 3 -
      420%:R * b * g + 125%:R * d - 216%:R * e ^+ 2 * g) /
    125%:R.

Definition lazard_square_linear_critical_remainder1
    (a b g e : F) : F :=
  - 4%:R *
    (4%:R * a ^+ 3 * e + a ^+ 2 * b -
      204%:R * a ^+ 2 * e ^+ 2 + 199%:R * a * b * e +
      216%:R * a * e ^+ 3 - 165%:R * a * g -
      20%:R * b ^+ 2 - 36%:R * b * e ^+ 2 + 45%:R * e * g) /
    125%:R.

Definition lazard_square_linear_critical_remainder2
    (a b g e : F) : F :=
  - 4%:R *
    (3%:R * a ^+ 3 + 13%:R * a ^+ 2 * e - 20%:R * a * b -
      324%:R * a * e ^+ 2 + 285%:R * b * e +
      324%:R * e ^+ 3 - 225%:R * g) /
    125%:R.

Definition lazard_square_linear_critical_remainder
    (a b g d e x : F) : F :=
  lazard_square_linear_critical_remainder0 a b g d e +
    lazard_square_linear_critical_remainder1 a b g e * x +
      lazard_square_linear_critical_remainder2 a b g e * x ^+ 2.

(** Named coefficients of the denominator-cleared division.  They are shared
    by the pointwise proof below and by the polynomial lift. *)
Definition lazard_critical_cubic_coefficient0 (a b g e : F) : F :=
  g - 2%:R * b * e.
Definition lazard_critical_cubic_coefficient1 (a b e : F) : F :=
  - 4%:R * a * e - b.
Definition lazard_critical_cubic_coefficient2 (a e : F) : F :=
  - 3%:R * a - 6%:R * e.
Definition lazard_critical_cubic_coefficient3 : F := - 5%:R.

Definition lazard_critical_scaled_quotient_coefficient0
    (a b e : F) : F :=
  - 4%:R * a ^+ 2 + 204%:R * a * e - 420%:R * b -
    216%:R * e ^+ 2.
Definition lazard_critical_scaled_quotient_coefficient1 (a e : F) : F :=
  5%:R * (- 132%:R * a + 36%:R * e).
Definition lazard_critical_scaled_quotient_coefficient2 : F :=
  25%:R * (- 36%:R).

Definition lazard_critical_scaled_remainder_coefficient0
    (a b g d e : F) : F :=
  - (8%:R * a ^+ 2 * b * e - 4%:R * a ^+ 2 * g -
    408%:R * a * b * e ^+ 2 + 204%:R * a * e * g +
    340%:R * b ^+ 2 * e + 432%:R * b * e ^+ 3 -
    420%:R * b * g + 125%:R * d - 216%:R * e ^+ 2 * g).
Definition lazard_critical_scaled_remainder_coefficient1
    (a b g e : F) : F :=
  - 4%:R *
    (4%:R * a ^+ 3 * e + a ^+ 2 * b -
      204%:R * a ^+ 2 * e ^+ 2 + 199%:R * a * b * e +
      216%:R * a * e ^+ 3 - 165%:R * a * g -
      20%:R * b ^+ 2 - 36%:R * b * e ^+ 2 + 45%:R * e * g).
Definition lazard_critical_scaled_remainder_coefficient2
    (a b g e : F) : F :=
  - 4%:R *
    (3%:R * a ^+ 3 + 13%:R * a ^+ 2 * e - 20%:R * a * b -
      324%:R * a * e ^+ 2 + 285%:R * b * e +
      324%:R * e ^+ 3 - 225%:R * g).

Definition lazard_critical_scaled_quintic_coefficient0
    (b d e : F) : F :=
  125%:R * (4%:R * b ^+ 2 * e - d).
Definition lazard_critical_scaled_quintic_coefficient1
    (a b e : F) : F :=
  125%:R * (4%:R * b ^+ 2 + 16%:R * a * b * e).
Definition lazard_critical_scaled_quintic_coefficient2
    (a b e : F) : F :=
  125%:R * (16%:R * a * b + 16%:R * a ^+ 2 * e +
    24%:R * b * e).
Definition lazard_critical_scaled_quintic_coefficient3
    (a b e : F) : F :=
  125%:R * (16%:R * a ^+ 2 + 24%:R * b + 48%:R * a * e).
Definition lazard_critical_scaled_quintic_coefficient4 (a e : F) : F :=
  125%:R * (48%:R * a + 36%:R * e).
Definition lazard_critical_scaled_quintic_coefficient5 : F :=
  125%:R * 36%:R.

(** Numerals occurring only in the Euclidean quotient and remainder. *)
Lemma lazard_critical_9_natrE : (9%:R : F) = 3%:R * 3%:R.
Proof. exact: (@natrM F 3 3). Qed.
Lemma lazard_critical_13_natrE : (13%:R : F) = 12%:R + 1.
Proof. exact: (@natrD F 12 1). Qed.
Lemma lazard_critical_24_natrE : (24%:R : F) = 2%:R * 12%:R.
Proof. exact: (@natrM F 2 12). Qed.
Lemma lazard_critical_36_natrE : (36%:R : F) = 3%:R * 12%:R.
Proof. exact: (@natrM F 3 12). Qed.
Lemma lazard_critical_48_natrE : (48%:R : F) = 4%:R * 12%:R.
Proof. exact: (@natrM F 4 12). Qed.
Lemma lazard_critical_132_natrE : (132%:R : F) = 12%:R * 11%:R.
Proof. exact: (@natrM F 12 11). Qed.
Lemma lazard_critical_204_natrE :
  (204%:R : F) = 2%:R * 100%:R + 4%:R.
Proof. rewrite -(@natrM F 2 100) -(@natrD F 200 4). reflexivity. Qed.
Lemma lazard_critical_420_natrE : (420%:R : F) = 21%:R * 20%:R.
Proof. exact: (@natrM F 21 20). Qed.
Lemma lazard_critical_216_natrE : (216%:R : F) = 18%:R * 12%:R.
Proof. exact: (@natrM F 18 12). Qed.
Lemma lazard_critical_408_natrE :
  (408%:R : F) = 4%:R * 100%:R + 8%:R.
Proof. rewrite -(@natrM F 4 100) -(@natrD F 400 8). reflexivity. Qed.
Lemma lazard_critical_340_natrE : (340%:R : F) = 34%:R * 10%:R.
Proof. exact: (@natrM F 34 10). Qed.
Lemma lazard_critical_432_natrE : (432%:R : F) = 2%:R * 216%:R.
Proof. exact: (@natrM F 2 216). Qed.
Lemma lazard_critical_199_natrE :
  (199%:R : F) = 100%:R + 9%:R * 11%:R.
Proof. rewrite -(@natrM F 9 11) -(@natrD F 100 99). reflexivity. Qed.
Lemma lazard_critical_165_natrE : (165%:R : F) = 15%:R * 11%:R.
Proof. exact: (@natrM F 15 11). Qed.
Lemma lazard_critical_45_natrE : (45%:R : F) = 5%:R * 9%:R.
Proof. exact: (@natrM F 5 9). Qed.
Lemma lazard_critical_324_natrE : (324%:R : F) = 18%:R * 18%:R.
Proof. exact: (@natrM F 18 18). Qed.
Lemma lazard_critical_285_natrE :
  (285%:R : F) = 20%:R * 14%:R + 5%:R.
Proof. rewrite -(@natrM F 20 14) -(@natrD F 280 5). reflexivity. Qed.
Lemma lazard_critical_225_natrE : (225%:R : F) = 15%:R * 15%:R.
Proof. exact: (@natrM F 15 15). Qed.

Definition lazard_critical_div : F -> F -> F := fun x y => x / y.
Definition lazard_critical_inv : F -> F := @GRing.inv F.
Lemma lazard_critical_divE (x y : F) :
  x / y = lazard_critical_div x y. Proof. reflexivity. Qed.
Lemma lazard_critical_invE (x : F) :
  x^-1 = lazard_critical_inv x. Proof. reflexivity. Qed.

Lemma lazard_critical_field_theory :
  @field_theory (NR.lazard_numerator_ring_carrier F)
    (@NR.lazard_numerator_ring_zero F)
    (@NR.lazard_numerator_ring_one F)
    (@NR.lazard_numerator_ring_add F)
    (@NR.lazard_numerator_ring_mul F)
    (@NR.lazard_numerator_ring_sub F)
    (@NR.lazard_numerator_ring_opp F)
    lazard_critical_div lazard_critical_inv
    (@NR.lazard_numerator_ring_eq F).
Proof.
constructor.
- exact: (@NR.lazard_numerator_ring_theory F).
- unfold NR.lazard_numerator_ring_one, NR.lazard_numerator_ring_zero,
    NR.lazard_numerator_ring_eq.
  move=> h10; have h := (@oner_neq0 F).
  by move: h; rewrite h10 eqxx.
- by unfold lazard_critical_div, lazard_critical_inv,
    NR.lazard_numerator_ring_mul, NR.lazard_numerator_ring_eq.
- move=> x hx.
  unfold lazard_critical_inv, NR.lazard_numerator_ring_mul,
    NR.lazard_numerator_ring_one, NR.lazard_numerator_ring_zero,
    NR.lazard_numerator_ring_eq in *.
  apply: mulVr; rewrite unitfE.
  apply/negP=> /eqP hx0; exact: hx hx0.
Qed.

(** Wrapper-level form of [5], used to expose the denominator side
    condition to the registered field theory after its operations are made
    opaque. *)
Definition lazard_critical_five_wrapped :
    NR.lazard_numerator_ring_carrier F :=
  @NR.lazard_numerator_ring_add F
    (@NR.lazard_numerator_ring_mul F
      (@NR.lazard_numerator_ring_add F
        (@NR.lazard_numerator_ring_one F)
        (@NR.lazard_numerator_ring_one F))
      (@NR.lazard_numerator_ring_add F
        (@NR.lazard_numerator_ring_one F)
        (@NR.lazard_numerator_ring_one F)))
    (@NR.lazard_numerator_ring_one F).

Lemma lazard_critical_five_wrappedE :
  lazard_critical_five_wrapped = (5%:R : F).
Proof.
rewrite /lazard_critical_five_wrapped
  /NR.lazard_numerator_ring_add /NR.lazard_numerator_ring_mul
  /NR.lazard_numerator_ring_one.
by rewrite -!NR.lazard_numerator_two_natrE
  -NR.lazard_numerator_four_natrE -NR.lazard_numerator_five_natrE.
Qed.

Lemma lazard_critical_five_wrapped_neq0
    (five_neq0 : (5%:R : F) != 0) :
  ~ @NR.lazard_numerator_ring_eq F lazard_critical_five_wrapped
      (@NR.lazard_numerator_ring_zero F).
Proof.
rewrite /NR.lazard_numerator_ring_eq /NR.lazard_numerator_ring_zero
  lazard_critical_five_wrappedE.
move=> hfive.
by move: five_neq0; rewrite hfive eqxx.
Qed.

Add Ring lazard_critical_ring : (@NR.lazard_numerator_ring_theory F).
Add Field lazard_critical_field : lazard_critical_field_theory.
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq lazard_critical_div lazard_critical_inv.

Ltac lazard_critical_prepare :=
  repeat first
    [ rewrite lazard_critical_432_natrE
    | rewrite lazard_critical_420_natrE
    | rewrite lazard_critical_408_natrE
    | rewrite lazard_critical_340_natrE
    | rewrite lazard_critical_324_natrE
    | rewrite lazard_critical_285_natrE
    | rewrite lazard_critical_225_natrE
    | rewrite lazard_critical_216_natrE
    | rewrite lazard_critical_204_natrE
    | rewrite lazard_critical_199_natrE
    | rewrite lazard_critical_165_natrE
    | rewrite lazard_critical_132_natrE
    | rewrite lazard_critical_48_natrE
    | rewrite lazard_critical_45_natrE
    | rewrite lazard_critical_36_natrE
    | rewrite lazard_critical_24_natrE
    | rewrite lazard_critical_13_natrE
    | rewrite lazard_critical_9_natrE ];
  lazard_numerator_prepare.

Ltac finish_lazard_critical_ring :=
  lazard_critical_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Coefficients of [125 * 4 * (X + e) * h'(X)^2 - 125 * d]. *)
Lemma lazard_critical_scaled_quintic_coefficient0E b d e :
  125%:R * (4%:R * e * (b ^+ 2) - d) =
    lazard_critical_scaled_quintic_coefficient0 b d e.
Proof.
rewrite /lazard_critical_scaled_quintic_coefficient0.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_quintic_coefficient1E a b e :
  125%:R * (4%:R * (b ^+ 2 + e * (4%:R * a * b))) =
    lazard_critical_scaled_quintic_coefficient1 a b e.
Proof.
rewrite /lazard_critical_scaled_quintic_coefficient1.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_quintic_coefficient2E a b e :
  125%:R * (4%:R *
    (4%:R * a * b + e * (4%:R * a ^+ 2 + 6%:R * b))) =
    lazard_critical_scaled_quintic_coefficient2 a b e.
Proof.
rewrite /lazard_critical_scaled_quintic_coefficient2.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_quintic_coefficient3E a b e :
  125%:R * (4%:R *
    (4%:R * a ^+ 2 + 6%:R * b + e * (12%:R * a))) =
    lazard_critical_scaled_quintic_coefficient3 a b e.
Proof.
rewrite /lazard_critical_scaled_quintic_coefficient3.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_quintic_coefficient4E a e :
  125%:R * (4%:R * (12%:R * a + e * 9%:R)) =
    lazard_critical_scaled_quintic_coefficient4 a e.
Proof.
rewrite /lazard_critical_scaled_quintic_coefficient4.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_quintic_coefficient5E :
  125%:R * (4%:R * (9%:R : F)) =
    lazard_critical_scaled_quintic_coefficient5.
Proof.
rewrite /lazard_critical_scaled_quintic_coefficient5.
finish_lazard_critical_ring.
Qed.

(** The six denominator-cleared cubic-times-quadratic coefficient
    identities. *)
Lemma lazard_critical_scaled_division_coefficient0 a b g d e :
  lazard_critical_scaled_remainder_coefficient0 a b g d e +
      lazard_critical_cubic_coefficient0 a b g e *
        lazard_critical_scaled_quotient_coefficient0 a b e =
    lazard_critical_scaled_quintic_coefficient0 b d e.
Proof.
rewrite /lazard_critical_scaled_remainder_coefficient0
  /lazard_critical_cubic_coefficient0
  /lazard_critical_scaled_quotient_coefficient0
  /lazard_critical_scaled_quintic_coefficient0.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_division_coefficient1 a b g e :
  lazard_critical_scaled_remainder_coefficient1 a b g e +
      lazard_critical_cubic_coefficient1 a b e *
        lazard_critical_scaled_quotient_coefficient0 a b e +
      lazard_critical_cubic_coefficient0 a b g e *
        lazard_critical_scaled_quotient_coefficient1 a e =
    lazard_critical_scaled_quintic_coefficient1 a b e.
Proof.
rewrite /lazard_critical_scaled_remainder_coefficient1
  /lazard_critical_cubic_coefficient1
  /lazard_critical_scaled_quotient_coefficient0
  /lazard_critical_cubic_coefficient0
  /lazard_critical_scaled_quotient_coefficient1
  /lazard_critical_scaled_quintic_coefficient1.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_division_coefficient2 a b g e :
  lazard_critical_scaled_remainder_coefficient2 a b g e +
      lazard_critical_cubic_coefficient2 a e *
        lazard_critical_scaled_quotient_coefficient0 a b e +
      lazard_critical_cubic_coefficient1 a b e *
        lazard_critical_scaled_quotient_coefficient1 a e +
      lazard_critical_cubic_coefficient0 a b g e *
        lazard_critical_scaled_quotient_coefficient2 =
    lazard_critical_scaled_quintic_coefficient2 a b e.
Proof.
rewrite /lazard_critical_scaled_remainder_coefficient2
  /lazard_critical_cubic_coefficient2
  /lazard_critical_scaled_quotient_coefficient0
  /lazard_critical_cubic_coefficient1
  /lazard_critical_scaled_quotient_coefficient1
  /lazard_critical_cubic_coefficient0
  /lazard_critical_scaled_quotient_coefficient2
  /lazard_critical_scaled_quintic_coefficient2.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_division_coefficient3 a b e :
  lazard_critical_cubic_coefficient3 *
      lazard_critical_scaled_quotient_coefficient0 a b e +
    lazard_critical_cubic_coefficient2 a e *
      lazard_critical_scaled_quotient_coefficient1 a e +
    lazard_critical_cubic_coefficient1 a b e *
      lazard_critical_scaled_quotient_coefficient2 =
    lazard_critical_scaled_quintic_coefficient3 a b e.
Proof.
rewrite /lazard_critical_cubic_coefficient3
  /lazard_critical_scaled_quotient_coefficient0
  /lazard_critical_cubic_coefficient2
  /lazard_critical_scaled_quotient_coefficient1
  /lazard_critical_cubic_coefficient1
  /lazard_critical_scaled_quotient_coefficient2
  /lazard_critical_scaled_quintic_coefficient3.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_division_coefficient4 a e :
  lazard_critical_cubic_coefficient3 *
      lazard_critical_scaled_quotient_coefficient1 a e +
    lazard_critical_cubic_coefficient2 a e *
      lazard_critical_scaled_quotient_coefficient2 =
    lazard_critical_scaled_quintic_coefficient4 a e.
Proof.
rewrite /lazard_critical_cubic_coefficient3
  /lazard_critical_scaled_quotient_coefficient1
  /lazard_critical_cubic_coefficient2
  /lazard_critical_scaled_quotient_coefficient2
  /lazard_critical_scaled_quintic_coefficient4.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_scaled_division_coefficient5 :
  lazard_critical_cubic_coefficient3 *
      lazard_critical_scaled_quotient_coefficient2 =
    lazard_critical_scaled_quintic_coefficient5.
Proof.
rewrite /lazard_critical_cubic_coefficient3
  /lazard_critical_scaled_quotient_coefficient2
  /lazard_critical_scaled_quintic_coefficient5.
finish_lazard_critical_ring.
Qed.

Lemma lazard_critical_mul_reorder_left (p q r : F) :
  (p * q) * r = (r * p) * q.
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_mul_reorder_right (p q r : F) :
  (p * q) * r = (r * q) * p.
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_scale_product (k p q : F) :
  k * (p * q) = p * (k * q).
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_scale_sum_product (k r c q : F) :
  k * (r + c * q) = k * r + c * (k * q).
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_quadratic_reverse (q0 q1 q2 x : F) :
  q2 * x ^+ 2 + q1 * x + q0 = q0 + q1 * x + q2 * x ^+ 2.
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_twenty_five_neq0
    (five_neq0 : (5%:R : F) != 0) :
  (25%:R : F) != 0.
Proof.
rewrite NR.lazard_numerator_twenty_five_natrE.
apply: mulf_neq0.
- exact five_neq0.
- exact five_neq0.
Qed.

Lemma lazard_critical_hundred_twenty_five_neq0
    (five_neq0 : (5%:R : F) != 0) :
  (125%:R : F) != 0.
Proof.
rewrite NR.lazard_numerator_hundred_twenty_five_natrE.
exact: mulf_neq0 five_neq0
  (lazard_critical_twenty_five_neq0 five_neq0).
Qed.

Lemma lazard_critical_scale_125_div_5 (z : F)
    (five_neq0 : (5%:R : F) != 0) :
  125%:R * (z / 5%:R) = 25%:R * z.
Proof.
rewrite NR.lazard_numerator_hundred_twenty_five_natrE
  lazard_critical_mul_reorder_left divfK //.
by rewrite mulrC.
Qed.

Lemma lazard_critical_scale_125_div_25 (z : F)
    (five_neq0 : (5%:R : F) != 0) :
  125%:R * (z / 25%:R) = 5%:R * z.
Proof.
rewrite NR.lazard_numerator_hundred_twenty_five_natrE
  lazard_critical_mul_reorder_right divfK //.
- by rewrite mulrC.
- exact: lazard_critical_twenty_five_neq0 five_neq0.
Qed.

Lemma lazard_critical_scale_125_div_125 (z : F)
    (five_neq0 : (5%:R : F) != 0) :
  125%:R * (z / 125%:R) = z.
Proof.
rewrite [125%:R * _]mulrC divfK //.
exact: lazard_critical_hundred_twenty_five_neq0 five_neq0.
Qed.

Lemma lazard_critical_cubic_quadratic_product_expansion
    (c0 c1 c2 c3 q0 q1 q2 r0 r1 r2 x : F) :
  (r0 + r1 * x + r2 * x ^+ 2) +
      (c0 + c1 * x + c2 * x ^+ 2 + c3 * x ^+ 3) *
        (q0 + q1 * x + q2 * x ^+ 2) =
    (r0 + c0 * q0) +
      (r1 + c1 * q0 + c0 * q1) * x +
      (r2 + c2 * q0 + c1 * q1 + c0 * q2) * x ^+ 2 +
      (c3 * q0 + c2 * q1 + c1 * q2) * x ^+ 3 +
      (c3 * q1 + c2 * q2) * x ^+ 4 +
      (c3 * q2) * x ^+ 5.
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_quadratic_square_expansion
    (t0 t1 t2 x : F) :
  (t0 + t1 * x + t2 * x ^+ 2) ^+ 2 =
    t0 ^+ 2 + (2%:R * t0 * t1) * x +
      (t1 ^+ 2 + 2%:R * t0 * t2) * x ^+ 2 +
      (2%:R * t1 * t2) * x ^+ 3 + t2 ^+ 2 * x ^+ 4.
Proof. finish_lazard_critical_ring. Qed.

Lemma lazard_critical_scaled_linear_quartic_expansion
    (k four e d s0 s1 s2 s3 s4 x : F) :
  k * (four * (x + e) *
        (s0 + s1 * x + s2 * x ^+ 2 + s3 * x ^+ 3 + s4 * x ^+ 4) - d) =
    k * (four * e * s0 - d) +
      (k * (four * (s0 + e * s1))) * x +
      (k * (four * (s1 + e * s2))) * x ^+ 2 +
      (k * (four * (s2 + e * s3))) * x ^+ 3 +
      (k * (four * (s3 + e * s4))) * x ^+ 4 +
      (k * (four * s4)) * x ^+ 5.
Proof. finish_lazard_critical_ring. Qed.

(** The two elementary elimination identities behind the discriminant
    reduction. *)
Theorem lazard_square_linear_eliminate_sextic a b g d e x :
  lazard_square_linear_f a b g d e x -
      lazard_square_linear_ell e x *
        lazard_square_linear_fprime a b g d x =
    lazard_square_linear_h a b g x *
      lazard_square_linear_critical_cubic a b g e x.
Proof.
rewrite /lazard_square_linear_f /lazard_square_linear_fprime
  /lazard_square_linear_critical_cubic.
finish_lazard_critical_ring.
Qed.

Theorem lazard_square_linear_eliminate_cubic a b g d e x :
  lazard_square_linear_fprime a b g d x -
      2%:R * lazard_square_linear_hprime a b x *
        lazard_square_linear_critical_cubic a b g e x =
    lazard_square_linear_critical_quintic a b g d e x.
Proof.
rewrite /lazard_square_linear_fprime
  /lazard_square_linear_critical_cubic
  /lazard_square_linear_critical_quintic.
finish_lazard_critical_ring.
Qed.

(** The critical cubic has the fixed leading coefficient [-5]. *)
Theorem lazard_square_linear_critical_cubic_coefficients a b g e x :
  lazard_square_linear_critical_cubic a b g e x =
    (g - 2%:R * b * e) + (- 4%:R * a * e - b) * x +
      (- 3%:R * a - 6%:R * e) * x ^+ 2 - 5%:R * x ^+ 3.
Proof.
rewrite /lazard_square_linear_critical_cubic
  /lazard_square_linear_h /lazard_square_linear_hprime
  /lazard_square_linear_ell.
finish_lazard_critical_ring.
Qed.

(** Exact Euclidean reduction of the critical quintic by the critical cubic.
    The denominator hypothesis is stated only once; nonzeroness of [25] and
    [125] is generated from it by the field certificate. *)
Theorem lazard_square_linear_critical_division a b g d e x
    (five_neq0 : (5%:R : F) != 0) :
  lazard_square_linear_critical_quintic a b g d e x =
    lazard_square_linear_critical_remainder a b g d e x +
      lazard_square_linear_critical_cubic a b g e x *
        lazard_square_linear_critical_quotient a b e x.
Proof.
pose n0 :=
  8%:R * a ^+ 2 * b * e - 4%:R * a ^+ 2 * g -
    408%:R * a * b * e ^+ 2 + 204%:R * a * e * g +
    340%:R * b ^+ 2 * e + 432%:R * b * e ^+ 3 -
    420%:R * b * g + 125%:R * d - 216%:R * e ^+ 2 * g.
pose n1 :=
  4%:R * a ^+ 3 * e + a ^+ 2 * b - 204%:R * a ^+ 2 * e ^+ 2 +
    199%:R * a * b * e + 216%:R * a * e ^+ 3 - 165%:R * a * g -
    20%:R * b ^+ 2 - 36%:R * b * e ^+ 2 + 45%:R * e * g.
pose n2 :=
  3%:R * a ^+ 3 + 13%:R * a ^+ 2 * e - 20%:R * a * b -
    324%:R * a * e ^+ 2 + 285%:R * b * e + 324%:R * e ^+ 3 -
    225%:R * g.
pose q0 :=
  - 4%:R * a ^+ 2 + 204%:R * a * e - 420%:R * b -
    216%:R * e ^+ 2.
pose c0 := g - 2%:R * b * e.
pose c1 := - 4%:R * a * e - b.
pose c2 := - 3%:R * a - 6%:R * e.
pose c3 : F := - 5%:R.
pose q1 := 5%:R * (- 132%:R * a + 36%:R * e).
pose q2 : F := 25%:R * (- 36%:R).
pose r0 := - n0.
pose r1 := - 4%:R * n1.
pose r2 := - 4%:R * n2.
pose l0 := 125%:R * (4%:R * b ^+ 2 * e - d).
pose l1 := 125%:R * (4%:R * b ^+ 2 + 16%:R * a * b * e).
pose l2 :=
  125%:R * (16%:R * a * b + 16%:R * a ^+ 2 * e +
    24%:R * b * e).
pose l3 :=
  125%:R * (16%:R * a ^+ 2 + 24%:R * b + 48%:R * a * e).
pose l4 := 125%:R * (48%:R * a + 36%:R * e).
pose l5 : F := 125%:R * 36%:R.
pose s0 := b ^+ 2.
pose s1 := 4%:R * a * b.
pose s2 := 4%:R * a ^+ 2 + 6%:R * b.
pose s3 := 12%:R * a.
pose s4 : F := 9%:R.
pose t0 := b.
pose t1 := 2%:R * a.
pose t2 : F := 3%:R.
pose scaled_remainder :=
  r0 + r1 * x + r2 * x ^+ 2.
pose scaled_quotient :=
  q0 + q1 * x + q2 * x ^+ 2.
have hrem :
    125%:R * lazard_square_linear_critical_remainder a b g d e x =
      scaled_remainder.
  rewrite /lazard_square_linear_critical_remainder
    /lazard_square_linear_critical_remainder0
    /lazard_square_linear_critical_remainder1
    /lazard_square_linear_critical_remainder2.
  fold n0 n1 n2 r0 r1 r2 scaled_remainder.
  transitivity
    (125%:R * (r0 / 125%:R) +
      (125%:R * (r1 / 125%:R)) * x +
      (125%:R * (r2 / 125%:R)) * x ^+ 2).
  - finish_lazard_critical_ring.
  - rewrite !lazard_critical_scale_125_div_125 //.
have hquot :
    125%:R * lazard_square_linear_critical_quotient a b e x =
      scaled_quotient.
  rewrite /lazard_square_linear_critical_quotient.
  fold q0 q1 q2 scaled_quotient.
  transitivity
    ((125%:R * ((- 36%:R) / 5%:R)) * x ^+ 2 +
      (125%:R * ((- 132%:R * a + 36%:R * e) / 25%:R)) * x +
      125%:R * (q0 / 125%:R)).
  - finish_lazard_critical_ring.
  - rewrite (lazard_critical_scale_125_div_5 (- 36%:R) five_neq0)
      (lazard_critical_scale_125_div_25
        (- 132%:R * a + 36%:R * e) five_neq0)
      (lazard_critical_scale_125_div_125 q0 five_neq0).
    exact: lazard_critical_quadratic_reverse.
have hcubic :
    lazard_square_linear_critical_cubic a b g e x =
      c0 + c1 * x + c2 * x ^+ 2 + c3 * x ^+ 3.
  rewrite lazard_square_linear_critical_cubic_coefficients
    /c0 /c1 /c2 /c3.
  finish_lazard_critical_ring.
have hprime_form :
    lazard_square_linear_hprime a b x =
      t0 + t1 * x + t2 * x ^+ 2.
  rewrite /lazard_square_linear_hprime /t0 /t1 /t2.
  finish_lazard_critical_ring.
have hs0 : t0 ^+ 2 = s0.
  by rewrite /t0 /s0.
have hs1 : 2%:R * t0 * t1 = s1.
  rewrite /t0 /t1 /s1.
  finish_lazard_critical_ring.
have hs2 : t1 ^+ 2 + 2%:R * t0 * t2 = s2.
  rewrite /t0 /t1 /t2 /s2.
  finish_lazard_critical_ring.
have hs3 : 2%:R * t1 * t2 = s3.
  rewrite /t1 /t2 /s3.
  finish_lazard_critical_ring.
have hs4 : t2 ^+ 2 = s4.
  rewrite /t2 /s4.
  finish_lazard_critical_ring.
have hsquare :
    lazard_square_linear_hprime a b x ^+ 2 =
      s0 + s1 * x + s2 * x ^+ 2 + s3 * x ^+ 3 + s4 * x ^+ 4.
  rewrite hprime_form lazard_critical_quadratic_square_expansion
    hs0 hs1 hs2 hs3 hs4.
  reflexivity.
have hl0 : 125%:R * (4%:R * e * s0 - d) = l0.
  rewrite /s0 /l0.
  exact: lazard_critical_scaled_quintic_coefficient0E.
have hl1 : 125%:R * (4%:R * (s0 + e * s1)) = l1.
  rewrite /s0 /s1 /l1.
  exact: lazard_critical_scaled_quintic_coefficient1E.
have hl2 : 125%:R * (4%:R * (s1 + e * s2)) = l2.
  rewrite /s1 /s2 /l2.
  exact: lazard_critical_scaled_quintic_coefficient2E.
have hl3 : 125%:R * (4%:R * (s2 + e * s3)) = l3.
  rewrite /s2 /s3 /l3.
  exact: lazard_critical_scaled_quintic_coefficient3E.
have hl4 : 125%:R * (4%:R * (s3 + e * s4)) = l4.
  rewrite /s3 /s4 /l4.
  exact: lazard_critical_scaled_quintic_coefficient4E.
have hl5 : 125%:R * (4%:R * s4) = l5.
  rewrite /s4 /l5.
  exact: lazard_critical_scaled_quintic_coefficient5E.
have hleft :
    125%:R * lazard_square_linear_critical_quintic a b g d e x =
      l0 + l1 * x + l2 * x ^+ 2 + l3 * x ^+ 3 + l4 * x ^+ 4 +
        l5 * x ^+ 5.
  rewrite /lazard_square_linear_critical_quintic hsquare
    /lazard_square_linear_ell.
  rewrite lazard_critical_scaled_linear_quartic_expansion
    hl0 hl1 hl2 hl3 hl4 hl5.
  reflexivity.
have hcoef0 : r0 + c0 * q0 = l0.
  rewrite /r0 /c0 /q0 /l0 /n0.
  exact: lazard_critical_scaled_division_coefficient0.
have hcoef1 : r1 + c1 * q0 + c0 * q1 = l1.
  rewrite /r1 /c1 /c0 /q1 /q0 /l1 /n1.
  exact: lazard_critical_scaled_division_coefficient1.
have hcoef2 : r2 + c2 * q0 + c1 * q1 + c0 * q2 = l2.
  rewrite /r2 /c2 /c1 /c0 /q2 /q1 /q0 /l2 /n2.
  exact: lazard_critical_scaled_division_coefficient2.
have hcoef3 : c3 * q0 + c2 * q1 + c1 * q2 = l3.
  rewrite /c3 /c2 /c1 /q2 /q1 /q0 /l3.
  exact: lazard_critical_scaled_division_coefficient3.
have hcoef4 : c3 * q1 + c2 * q2 = l4.
  rewrite /c3 /c2 /q2 /q1 /l4.
  exact: lazard_critical_scaled_division_coefficient4.
have hcoef5 : c3 * q2 = l5.
  rewrite /c3 /q2 /l5.
  exact: lazard_critical_scaled_division_coefficient5.
have hright :
    scaled_remainder +
        lazard_square_linear_critical_cubic a b g e x * scaled_quotient =
      (r0 + c0 * q0) +
        (r1 + c1 * q0 + c0 * q1) * x +
        (r2 + c2 * q0 + c1 * q1 + c0 * q2) * x ^+ 2 +
        (c3 * q0 + c2 * q1 + c1 * q2) * x ^+ 3 +
        (c3 * q1 + c2 * q2) * x ^+ 4 +
        (c3 * q2) * x ^+ 5.
  rewrite hcubic /scaled_remainder /scaled_quotient.
  exact: lazard_critical_cubic_quadratic_product_expansion.
have hscaled :
    125%:R * lazard_square_linear_critical_quintic a b g d e x =
      scaled_remainder +
        lazard_square_linear_critical_cubic a b g e x * scaled_quotient.
  rewrite hleft hright hcoef0 hcoef1 hcoef2 hcoef3 hcoef4 hcoef5.
  reflexivity.
apply: (mulfI (lazard_critical_hundred_twenty_five_neq0 five_neq0)).
rewrite (lazard_critical_scale_sum_product
    (125%:R : F)
    (lazard_square_linear_critical_remainder a b g d e x)
    (lazard_square_linear_critical_cubic a b g e x)
    (lazard_square_linear_critical_quotient a b e x))
  hrem hquot hscaled.
reflexivity.
Qed.

(** Lazard specialization of the generic square-minus-linear values. *)
Definition lazard_critical_a
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  LR.lazard_resolvent_cubic_a c.
Definition lazard_critical_b
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  LR.lazard_resolvent_cubic_b c.
Definition lazard_critical_g
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  LR.lazard_resolvent_cubic_g c.
Definition lazard_critical_d
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  LR.lazard_resolvent_discriminant c.
Definition lazard_critical_e
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  LR.lazard_resolvent_linear_e c.

Definition lazard_critical_remainder0
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  lazard_square_linear_critical_remainder0
    (lazard_critical_a c) (lazard_critical_b c)
    (lazard_critical_g c) (lazard_critical_d c) (lazard_critical_e c).
Definition lazard_critical_remainder1
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  lazard_square_linear_critical_remainder1
    (lazard_critical_a c) (lazard_critical_b c)
    (lazard_critical_g c) (lazard_critical_e c).
Definition lazard_critical_remainder2
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  lazard_square_linear_critical_remainder2
    (lazard_critical_a c) (lazard_critical_b c)
    (lazard_critical_g c) (lazard_critical_e c).

Definition lazard_critical_resultant_value
    (c : RP.LazardDepressedRootCoefficients F) : F :=
  CQ.lazard_cubic_quadratic_resultant_value
    (lazard_critical_g c -
      2%:R * lazard_critical_b c * lazard_critical_e c)
    (- 4%:R * lazard_critical_a c * lazard_critical_e c -
      lazard_critical_b c)
    (- 3%:R * lazard_critical_a c - 6%:R * lazard_critical_e c)
    (- 5%:R)
    (lazard_critical_remainder0 c)
    (lazard_critical_remainder1 c)
    (lazard_critical_remainder2 c).

(** The literal sextic and its derivative are exactly the generic pointwise
    pair used by the eliminations above. *)
Theorem lazard_resolvent_horner_as_square_linear c x :
  (LR.lazard_resolvent_polynomial c).[x] =
    lazard_square_linear_f
      (lazard_critical_a c) (lazard_critical_b c)
      (lazard_critical_g c) (lazard_critical_d c)
      (lazard_critical_e c) x.
Proof.
rewrite LR.lazard_resolvent_polynomial_horner_square
  /lazard_square_linear_f /lazard_square_linear_h
  /lazard_square_linear_ell /lazard_critical_a /lazard_critical_b
  /lazard_critical_g /lazard_critical_d /lazard_critical_e.
reflexivity.
Qed.

Theorem lazard_resolvent_derivative_horner_as_square_linear c x :
  (LR.lazard_resolvent_polynomial c)^`().[x] =
    lazard_square_linear_fprime
      (lazard_critical_a c) (lazard_critical_b c)
      (lazard_critical_g c) (lazard_critical_d c) x.
Proof.
rewrite LR.lazard_resolvent_polynomial_derivative_horner
  LR.lazard_resolvent_cubic_horner
  LR.lazard_resolvent_cubic_derivative_horner
  /lazard_square_linear_fprime /lazard_square_linear_h
  /lazard_square_linear_hprime /lazard_critical_a /lazard_critical_b
  /lazard_critical_g /lazard_critical_d.
reflexivity.
Qed.

End CriticalElimination.

Print Assumptions lazard_square_linear_eliminate_sextic.
Print Assumptions lazard_square_linear_eliminate_cubic.
Print Assumptions lazard_square_linear_critical_division.

End PolynomialFormulasLazardQuinticCriticalElimination.
