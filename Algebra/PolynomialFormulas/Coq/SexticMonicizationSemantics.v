From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability SexticRecursiveCore
  SexticReducibleSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

(** Semantic correctness of the integral monicization used by the recursive
    sextic procedure.  If [a] is the leading coefficient of [p], the change
    of variable [y = a * x] turns [p] into the integral monic polynomial

      y^6 + p_5 y^5 + p_4 a y^4 + ... + p_0 a^5.

    The proof below also transports explicit radical expressions through this
    nonzero rational scaling. *)
Module PolynomialFormulasSexticMonicizationSemantics.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SRS := PolynomialFormulasSexticReducibleSemantics.
Module QRD := PolynomialFormulasQuinticRadicalDecidability.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Definition leading_coefficient (p : {poly int}) : int := p`_6.

Definition integral_monicization (p : {poly int}) : {poly int} :=
  SRC.monic_polynomial (SRC.monicize (SRC.coefficients_of_poly p)).

Definition rational_monicization (p : {poly int}) : {poly rat} :=
  map_poly (intr : int -> rat) (integral_monicization p).

Lemma monicize_coefficients_of_poly_nth (p : {poly int}) i
    (hi : (i < 6)%N) :
  nth 0 (SRC.monicize (SRC.coefficients_of_poly p)) i =
    p`_i * p`_6 ^+ (5 - i)%N.
Proof.
rewrite -(inordK hi) -tnth_nth /SRC.monicize tnth_mktuple.
rewrite (SRC.coefficients_of_poly_nthE p
  (ltn_trans (ltn_ord (inord i)) (ltnSn 6))).
rewrite (SRC.coefficients_of_poly_nthE p (i := 6%N) isT).
case: i hi => [|[|[|[|[|[|i]]]]]] //= _.
all: by rewrite !inordK //=.
Qed.

Lemma integral_monicizationE (p : {poly int}) :
  integral_monicization p =
    'X^6 + (p`_5)%:P * 'X^5 + (p`_4 * p`_6)%:P * 'X^4 +
    (p`_3 * p`_6 ^ 2)%:P * 'X^3 +
    (p`_2 * p`_6 ^ 3)%:P * 'X^2 +
    (p`_1 * p`_6 ^ 4)%:P * 'X + (p`_0 * p`_6 ^ 5)%:P.
Proof.
rewrite /integral_monicization /SRC.monic_polynomial.
rewrite !monicize_coefficients_of_poly_nth //=.
by rewrite !expr0 !expr1 !mulr1.
Qed.

Lemma integral_monicization_coef0 p :
  (integral_monicization p)`_0 = p`_0 * p`_6 ^+ 5.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma integral_monicization_coef1 p :
  (integral_monicization p)`_1 = p`_1 * p`_6 ^+ 4.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma integral_monicization_coef2 p :
  (integral_monicization p)`_2 = p`_2 * p`_6 ^+ 3.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma integral_monicization_coef3 p :
  (integral_monicization p)`_3 = p`_3 * p`_6 ^+ 2.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma integral_monicization_coef4 p :
  (integral_monicization p)`_4 = p`_4 * p`_6.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma integral_monicization_coef5 p :
  (integral_monicization p)`_5 = p`_5.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma integral_monicization_coef6 p :
  (integral_monicization p)`_6 = 1.
Proof.
by rewrite integral_monicizationE !coefD !coefCM !coefXn !coefX !coefC /=
  ?mulr0 ?mulr1 ?addr0 ?add0r.
Qed.

Lemma sextic_polynomialE (p : {poly int}) (hp_size : size p = 7%N) :
  p =
    p`_6 *: 'X^6 + p`_5 *: 'X^5 + p`_4 *: 'X^4 +
    p`_3 *: 'X^3 + p`_2 *: 'X^2 + p`_1 *: 'X + (p`_0)%:P.
Proof.
apply/polyP=> i.
case: i => [|[|[|[|[|[|[|i]]]]]]].
all: rewrite !coefD !coefZ !coefXn ?coefX ?coefC /=.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite addr0 | rewrite add0r ]).
all: try by [].
rewrite nth_default // hp_size.
by [].
Qed.

Section MappedMonicization.

Variable R : comRingType.
Variable phi : {rmorphism int -> R}.

(** Expose MathComp's packed ring operations to the standard normalization
    tactic; this is proof infrastructure only, not an additional axiom. *)
Let ring_carrier : Type := R.
Local Definition ring_zero : ring_carrier := @GRing.zero R.
Local Definition ring_one : ring_carrier := @GRing.one R.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add R.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul R.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp R.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma ring_addE (x y : R) : x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma ring_mulE (x y : R) : x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma ring_subE (x y : R) : x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma ring_oppE (x : R) : - x = ring_opp x. Proof. reflexivity. Qed.
Lemma ring_zeroE : (0 : R) = ring_zero. Proof. reflexivity. Qed.
Lemma ring_oneE : @GRing.one R = ring_one. Proof. reflexivity. Qed.

Lemma mathcomp_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
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

Add Ring sextic_monicization_ring : mathcomp_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_monicization_ring :=
  repeat first
    [ rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma monicization_scale_identity (a c0 c1 c2 c3 c4 c5 x : R) :
  c0 * a ^+ 5 + (c1 * a ^+ 4) * (a * x) +
    (c2 * a ^+ 3) * (a * x) ^+ 2 +
    (c3 * a ^+ 2) * (a * x) ^+ 3 +
    (c4 * a) * (a * x) ^+ 4 + c5 * (a * x) ^+ 5 +
    (a * x) ^+ 6 =
  a ^+ 5 *
    (c0 + c1 * x + c2 * x ^+ 2 + c3 * x ^+ 3 +
      c4 * x ^+ 4 + c5 * x ^+ 5 + a * x ^+ 6).
Proof.
rewrite !exprS !expr0.
finish_monicization_ring.
Qed.

Lemma mapped_sextic_horner (p : {poly int})
    (hp_size : size p = 7%N) (x : R) :
  (map_poly phi p).[x] =
    phi p`_0 + phi p`_1 * x + phi p`_2 * x ^+ 2 + phi p`_3 * x ^+ 3 +
    phi p`_4 * x ^+ 4 + phi p`_5 * x ^+ 5 + phi p`_6 * x ^+ 6.
Proof.
have hsize : (size (map_poly phi p) <= 7)%N.
  rewrite /map_poly hp_size.
  exact: size_poly.
rewrite (@horner_coef_wide R 7 (map_poly phi p) x hsize).
rewrite !big_ord_recr big_ord0 /= !coef_map.
by rewrite expr0 mulr1 add0r.
Qed.

(** The defining change-of-variable identity, simultaneously for the
    rational and algebraic-closure coefficient embeddings used below. *)
Lemma mapped_monicization_horner (p : {poly int})
    (hp_size : size p = 7%N) (x : R) :
  (map_poly phi (integral_monicization p)).[phi p`_6 * x] =
    (phi p`_6) ^+ 5 * (map_poly phi p).[x].
Proof.
have hm_size : size (integral_monicization p) = 7%N.
  exact: SRC.size_monic_polynomial.
rewrite (@mapped_sextic_horner (integral_monicization p) hm_size
  (phi p`_6 * x)).
rewrite (mapped_sextic_horner hp_size).
rewrite integral_monicization_coef0 integral_monicization_coef1
  integral_monicization_coef2 integral_monicization_coef3
  integral_monicization_coef4 integral_monicization_coef5
  integral_monicization_coef6.
rewrite !rmorphM !rmorph1 mul1r.
exact: monicization_scale_identity.
Qed.

End MappedMonicization.

(** Mapping integer coefficients through the rationals gives the same
    algebraic-closure polynomial as the direct integer cast. *)
Lemma map_int_rat_algC (p : {poly int}) :
  map_poly ratrC (map_poly (intr : int -> rat) p) =
    map_poly (intr : int -> algC) p.
Proof.
rewrite -map_poly_comp.
apply: eq_map_poly=> z /=.
exact: rmorph_int.
Qed.

Lemma rational_monicization_horner (p : {poly int})
    (hp_size : size p = 7%N) (x : algC) :
  (map_poly ratrC (rational_monicization p)).[
      ((p`_6)%:~R : algC) * x] =
    ((p`_6)%:~R : algC) ^+ 5 *
      (map_poly ratrC (QRD.int_to_rat_poly p)).[x].
Proof.
rewrite /rational_monicization /QRD.int_to_rat_poly !map_int_rat_algC.
exact: (@mapped_monicization_horner algC (intr : int -> algC)
  p hp_size x).
Qed.

Lemma root_to_rational_monicization (p : {poly int})
    (hp_size : size p = 7%N) (x : algC) :
  x \in root (map_poly ratrC (QRD.int_to_rat_poly p)) ->
  ((p`_6)%:~R : algC) * x \in
    root (map_poly ratrC (rational_monicization p)).
Proof.
move/rootP=> hx; apply/rootP.
by rewrite (rational_monicization_horner hp_size) hx mulr0.
Qed.

Lemma root_from_rational_monicization (p : {poly int})
    (hp_size : size p = 7%N) (hp6 : p`_6 != 0) (y : algC) :
  y \in root (map_poly ratrC (rational_monicization p)) ->
  ((p`_6)%:~R : algC)^-1 * y \in
    root (map_poly ratrC (QRD.int_to_rat_poly p)).
Proof.
pose a : algC := (p`_6)%:~R.
have ha : a != 0 by rewrite /a intr_eq0.
have ha5 : a ^+ 5 != 0 := expf_neq0 5 ha.
move/rootP=> hy; apply/rootP.
have hscale : a * (a^-1 * y) = y.
  by rewrite mulrA mulfV // mul1r.
have hid := rational_monicization_horner hp_size (a^-1 * y).
have hprod : a ^+ 5 *
    (map_poly ratrC (QRD.int_to_rat_poly p)).[a^-1 * y] = 0.
  by rewrite -hid /a hscale hy.
have /orP [ha5z | hxz] :
    (a ^+ 5 == 0) ||
    ((map_poly ratrC (QRD.int_to_rat_poly p)).[a^-1 * y] == 0).
  rewrite -mulf_eq0.
  exact/eqP.
- by move: ha5; rewrite ha5z.
- exact/eqP.
Qed.

(** Radical expressions are closed under multiplication by a rational and
    by its inverse.  These transparent constructors are the only syntactic
    operations needed for the root transport. *)
Definition scale_algterm (c : rat) (t : algterm rat) : algterm rat :=
  BinOp Mul (Base c) t.

Definition inverse_scale_algterm (c : rat) (t : algterm rat) : algterm rat :=
  BinOp Mul (UnOp Inv (Base c)) t.

Lemma algT_eval_scale c t :
  algT_eval ratrC (scale_algterm c t) =
    ratrC c * algT_eval ratrC t.
Proof. by []. Qed.

Lemma algT_eval_inverse_scale c t :
  algT_eval ratrC (inverse_scale_algterm c t) =
    (ratrC c)^-1 * algT_eval ratrC t.
Proof. by []. Qed.

(** Integral monicization preserves exactly the rootwise property of having
    an explicit expression by rational constants, field operations, roots of
    unity, and radicals. *)
Theorem all_roots_radical_int_monicization (p : {poly int})
    (hp_size : size p = 7%N) (hp6 : p`_6 != 0) :
  QRD.all_roots_radical_int p <->
    radical_formula_solves (rational_monicization p).
Proof.
pose a : algC := (p`_6)%:~R.
have ha : a != 0 by rewrite /a intr_eq0.
rewrite /QRD.all_roots_radical_int /radical_formula_solves.
split.
- move=> hp y hy.
  pose x := a^-1 * y.
  have hx : x \in root (map_poly ratrC (QRD.int_to_rat_poly p)).
    rewrite /x /a.
    exact: (@root_from_rational_monicization p hp_size hp6 y hy).
  have [t ht] := hp x hx.
  exists (scale_algterm ((p`_6)%:~R : rat) t).
  rewrite algT_eval_scale ht ratr_int /x /a.
  by rewrite mulrA mulfV // mul1r.
- move=> hm x hx.
  pose y := a * x.
  have hy : y \in root (map_poly ratrC (rational_monicization p)).
    rewrite /y /a.
    exact: (@root_to_rational_monicization p hp_size x hx).
  have [t ht] := hm y hy.
  exists (inverse_scale_algterm ((p`_6)%:~R : rat) t).
  rewrite algT_eval_inverse_scale ht ratr_int /y /a.
  by rewrite mulrA mulVf // mul1r.
Qed.

Corollary all_roots_radical_int_monicize (p : {poly int})
    (hp_size : size p = 7%N) (hp6 : p`_6 != 0) :
  QRD.all_roots_radical_int p <->
  radical_formula_solves
    (map_poly (intr : int -> rat)
      (SRC.monic_polynomial
        (SRC.monicize (SRC.coefficients_of_poly p)))).
Proof. exact: all_roots_radical_int_monicization hp_size hp6. Qed.

End PolynomialFormulasSexticMonicizationSemantics.
