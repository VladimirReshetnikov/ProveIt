From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Executable coefficient arithmetic used by the Coq sextic decision.

    Unlike the semantic [numfield] reflector, every definition in this file
    is a transparent Gallina program on fixed tuples, integers, naturals, and
    finite lists. *)
Module PolynomialFormulasSexticRecursiveCore.

Definition sextic_coefficients := 7.-tuple int.
Definition monic_sextic := 6.-tuple int.

Definition coefficients_of_poly (p : {poly int}) : sextic_coefficients :=
  [tuple p`_i | i < 7].

Lemma coefficients_of_polyE (p : {poly int}) (i : 'I_7) :
  tnth (coefficients_of_poly p) i = p`_i.
Proof. by rewrite /coefficients_of_poly tnth_mktuple. Qed.

Lemma coefficients_of_poly_nthE (p : {poly int}) i (hi : (i < 7)%N) :
  nth 0 (coefficients_of_poly p) i = p`_i.
Proof.
rewrite /coefficients_of_poly -(inordK hi).
exact: nth_mktuple.
Qed.

Definition is_sexticb (a : sextic_coefficients) : bool := a`_6 != 0.

Lemma is_sexticP (a : sextic_coefficients) :
  reflect (a`_6 <> 0) (is_sexticb a).
Proof.
apply: (iffP negP).
- by move=> h /eqP ha; apply: h.
- by move=> h /eqP ha; apply: h.
Qed.

(** Integral monicization:
    [Y^6 + a5 Y^5 + a4 a6 Y^4 + ... + a0 a6^5]. *)
Definition monicize (a : sextic_coefficients) : monic_sextic :=
  [tuple a`_i * a`_6 ^ (5 - i) | i < 6].

Lemma monicize_coefficients_of_poly_monic (p : {poly int})
    (hp6 : p`_6 = 1) (i : 'I_6) :
  tnth (monicize (coefficients_of_poly p)) i = p`_i.
Proof.
rewrite /monicize tnth_mktuple.
rewrite (coefficients_of_poly_nthE p (ltn_trans (ltn_ord i) (ltnSn 6))).
rewrite (coefficients_of_poly_nthE p (i := 6%N) isT).
rewrite hp6.
by rewrite exp1rz mulr1.
Qed.

Lemma monicize_coefficients_of_poly_monic_nth (p : {poly int})
    (hp6 : p`_6 = 1) i (hi : (i < 6)%N) :
  nth 0 (monicize (coefficients_of_poly p)) i = p`_i.
Proof.
rewrite -(inordK hi) -tnth_nth.
exact: monicize_coefficients_of_poly_monic.
Qed.

Definition height (f : monic_sextic) : nat :=
  absz f`_0 + (absz f`_1 + (absz f`_2 +
    (absz f`_3 + (absz f`_4 + absz f`_5)))).

Definition root_bound (f : monic_sextic) : nat := height f + 2.

(** The explicit list [-R, ..., R]. *)
Definition symmetric_interval (R : nat) : seq int :=
  [seq (k%:Z - R%:Z : int) | k <- iota 0 (2 * R + 1)].

Lemma size_symmetric_interval (R : nat) :
  size (symmetric_interval R) = 2 * R + 1.
Proof. by rewrite /symmetric_interval size_map size_iota. Qed.

Lemma mem_symmetric_interval (R : nat) (z : int) :
  z \in symmetric_interval R <->
  exists k : nat, (k < 2 * R + 1)%N /\ z = (k%:Z - R%:Z : int).
Proof.
rewrite /symmetric_interval.
split.
- move/mapP=> [k]; rewrite mem_iota add0n => hk ->.
  by exists k; split.
- move=> [k [hk ->]].
  apply/mapP; exists k => //; by rewrite mem_iota add0n.
Qed.

(** Synthetic division by [X + c]. *)
Definition linear_q4 (f : monic_sextic) (c : int) := f`_5 - c.
Definition linear_q3 (f : monic_sextic) (c : int) :=
  f`_4 - c * linear_q4 f c.
Definition linear_q2 (f : monic_sextic) (c : int) :=
  f`_3 - c * linear_q3 f c.
Definition linear_q1 (f : monic_sextic) (c : int) :=
  f`_2 - c * linear_q2 f c.
Definition linear_q0 (f : monic_sextic) (c : int) :=
  f`_1 - c * linear_q1 f c.

Definition linear_remainder_zerob (f : monic_sextic) (c : int) : bool :=
  f`_0 == c * linear_q0 f c.

Lemma linear_remainder_zeroP (f : monic_sextic) (c : int) :
  reflect (f`_0 = c * linear_q0 f c) (linear_remainder_zerob f c).
Proof. exact: eqP. Qed.

(** Synthetic division by [X^2 + bX + c]. *)
Definition quadratic_q3 (f : monic_sextic) (b : int) := f`_5 - b.
Definition quadratic_q2 (f : monic_sextic) (b c : int) :=
  f`_4 - c - b * quadratic_q3 f b.
Definition quadratic_q1 (f : monic_sextic) (b c : int) :=
  f`_3 - b * quadratic_q2 f b c - c * quadratic_q3 f b.
Definition quadratic_q0 (f : monic_sextic) (b c : int) :=
  f`_2 - b * quadratic_q1 f b c - c * quadratic_q2 f b c.

Definition quadratic_remainder_zerob
    (f : monic_sextic) (b c : int) : bool :=
  (f`_1 == b * quadratic_q0 f b c + c * quadratic_q1 f b c) &&
  (f`_0 == c * quadratic_q0 f b c).

Lemma quadratic_remainder_zeroP (f : monic_sextic) (b c : int) :
  reflect
    (f`_1 = b * quadratic_q0 f b c + c * quadratic_q1 f b c /\
     f`_0 = c * quadratic_q0 f b c)
    (quadratic_remainder_zerob f b c).
Proof.
rewrite /quadratic_remainder_zerob.
apply: (iffP andP).
- by move=> [/eqP h1 /eqP h0]; split.
- move=> [h1 h0]; split; exact/eqP.
Qed.

(** Synthetic division by [X^3 + bX^2 + cX + d]. *)
Definition cubic_q2 (f : monic_sextic) (b : int) := f`_5 - b.
Definition cubic_q1 (f : monic_sextic) (b c : int) :=
  f`_4 - c - b * cubic_q2 f b.
Definition cubic_q0 (f : monic_sextic) (b c d : int) :=
  f`_3 - d - b * cubic_q1 f b c - c * cubic_q2 f b.

Definition cubic_remainder_zerob
    (f : monic_sextic) (b c d : int) : bool :=
  (f`_2 == b * cubic_q0 f b c d + c * cubic_q1 f b c +
      d * cubic_q2 f b) &&
  (f`_1 == c * cubic_q0 f b c d + d * cubic_q1 f b c) &&
  (f`_0 == d * cubic_q0 f b c d).

Lemma cubic_remainder_zeroP (f : monic_sextic) (b c d : int) :
  reflect
    (f`_2 = b * cubic_q0 f b c d + c * cubic_q1 f b c +
        d * cubic_q2 f b /\
     f`_1 = c * cubic_q0 f b c d + d * cubic_q1 f b c /\
     f`_0 = d * cubic_q0 f b c d)
    (cubic_remainder_zerob f b c d).
Proof.
rewrite /cubic_remainder_zerob.
apply: (iffP andP).
- move=> [/andP [/eqP h2 /eqP h1] /eqP h0].
  by split=> //; split.
- move=> [h2 [h1 h0]].
  split; last exact/eqP.
  by apply/andP; split; exact/eqP.
Qed.

(** Polynomial meaning of the synthetic recurrences. *)
Definition monic_polynomial (f : monic_sextic) : {poly int} :=
  'X^6 + (f`_5)%:P * 'X^5 + (f`_4)%:P * 'X^4 +
    (f`_3)%:P * 'X^3 + (f`_2)%:P * 'X^2 +
    (f`_1)%:P * 'X + (f`_0)%:P.

Definition linear_factor (c : int) : {poly int} := 'X + c%:P.
Definition linear_quotient (f : monic_sextic) (c : int) : {poly int} :=
  'X^5 + (linear_q4 f c)%:P * 'X^4 + (linear_q3 f c)%:P * 'X^3 +
    (linear_q2 f c)%:P * 'X^2 + (linear_q1 f c)%:P * 'X +
    (linear_q0 f c)%:P.

Definition quadratic_factor (b c : int) : {poly int} :=
  'X^2 + b%:P * 'X + c%:P.
Definition quadratic_quotient
    (f : monic_sextic) (b c : int) : {poly int} :=
  'X^4 + (quadratic_q3 f b)%:P * 'X^3 +
    (quadratic_q2 f b c)%:P * 'X^2 +
    (quadratic_q1 f b c)%:P * 'X + (quadratic_q0 f b c)%:P.
Definition quadratic_remainder
    (f : monic_sextic) (b c : int) : {poly int} :=
  (f`_1 - b * quadratic_q0 f b c - c * quadratic_q1 f b c)%:P * 'X +
  (f`_0 - c * quadratic_q0 f b c)%:P.

Definition cubic_factor (b c d : int) : {poly int} :=
  'X^3 + b%:P * 'X^2 + c%:P * 'X + d%:P.
Definition cubic_quotient
    (f : monic_sextic) (b c d : int) : {poly int} :=
  'X^3 + (cubic_q2 f b)%:P * 'X^2 + (cubic_q1 f b c)%:P * 'X +
    (cubic_q0 f b c d)%:P.
Definition cubic_remainder
    (f : monic_sextic) (b c d : int) : {poly int} :=
  (f`_2 - b * cubic_q0 f b c d - c * cubic_q1 f b c -
      d * cubic_q2 f b)%:P * 'X^2 +
  (f`_1 - c * cubic_q0 f b c d - d * cubic_q1 f b c)%:P * 'X +
  (f`_0 - d * cubic_q0 f b c d)%:P.

Lemma size_poly_from_top_coefficient (p : {poly int}) (n : nat)
    (hnz : p`_n != 0) (habove : forall j : nat, (n < j)%N -> p`_j = 0) :
  size p = n.+1.
Proof.
have hle : (size p <= n.+1)%N.
  apply/leq_sizeP=> j hj.
  exact: habove j hj.
have hnotle : ~~ (size p <= n)%N.
  apply/negP=> hlen.
  have hz : p`_n = 0 := (elimT (leq_sizeP p n) hlen n (leqnn n)).
  by move: hnz; rewrite hz eqxx.
have hlt : (n < size p)%N by rewrite ltnNge hnotle.
apply/eqP; rewrite eqn_leq.
exact/andP.
Qed.

Lemma size_linear_factor c : size (linear_factor c) = 2%N.
Proof. exact: size_XaddC. Qed.

Lemma size_quadratic_factor b c : size (quadratic_factor b c) = 3%N.
Proof.
apply: (size_poly_from_top_coefficient (n := 2%N)).
- by rewrite /quadratic_factor !coefD coefXn coefCM ?coefXn ?coefX coefC /=
    ?mulr0 ?addr0 ?oner_eq0.
- move=> j; case: j => [|[|[|j]]] // _.
  by rewrite /quadratic_factor !coefD coefXn coefCM ?coefXn ?coefX coefC /=
    ?mulr0 ?addr0.
Qed.

Lemma size_cubic_factor b c d : size (cubic_factor b c d) = 4%N.
Proof.
apply: (size_poly_from_top_coefficient (n := 3%N)).
- by rewrite /cubic_factor !coefD coefXn coefCM ?coefCM ?coefXn
    ?coefX coefC /= ?mulr0 ?addr0 ?oner_eq0.
- move=> j; case: j => [|[|[|[|j]]]] // _.
  by rewrite /cubic_factor !coefD coefXn coefCM ?coefCM ?coefXn ?coefX coefC /=
    ?mulr0 ?addr0.
Qed.

Lemma size_monic_polynomial f : size (monic_polynomial f) = 7%N.
Proof.
apply: (size_poly_from_top_coefficient (n := 6%N)).
- by rewrite /monic_polynomial !coefD coefXn coefCM ?coefCM ?coefXn
    ?coefX coefC /=
    ?mulr0 ?addr0 ?oner_eq0.
- move=> j; case: j => [|[|[|[|[|[|[|j]]]]]]] // _.
  by rewrite /monic_polynomial !coefD coefXn coefCM ?coefCM ?coefXn
    ?coefX coefC /=
    ?mulr0 ?addr0.
Qed.

(** Reading the first seven coefficients and rebuilding a monic sextic is
    extensionally the identity on monic polynomials of size seven. *)
Lemma monic_polynomial_monicize_coefficients_of_poly (p : {poly int})
    (hp_size : size p = 7%N) (hp_monic : p`_6 = 1) :
  monic_polynomial (monicize (coefficients_of_poly p)) = p.
Proof.
apply/polyP=> i.
case: i => [|[|[|[|[|[|[|i]]]]]]].
all: rewrite /monic_polynomial.
all: repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite addr0 | rewrite add0r ]).
- exact: monicize_coefficients_of_poly_monic_nth.
- exact: monicize_coefficients_of_poly_monic_nth.
- exact: monicize_coefficients_of_poly_monic_nth.
- exact: monicize_coefficients_of_poly_monic_nth.
- exact: monicize_coefficients_of_poly_monic_nth.
- exact: monicize_coefficients_of_poly_monic_nth.
- by rewrite hp_monic.
- rewrite nth_default // hp_size.
  by [] .
Qed.

Lemma add_add_sub_sub (x y z : int) : y + z + (x - y - z) = x.
Proof. by rewrite -addrA !subrKC. Qed.

Lemma sub_sub_add_add (x y z : int) : x - y - z + y + z = x.
Proof. by rewrite addrAC !subrK. Qed.

Lemma add_add_add_sub_sub_sub (x a b c : int) :
  a + b + c + (x - a - b - c) = x.
Proof.
rewrite -[a + b + c + _]addrA -[a + b + _]addrA.
by rewrite !subrKC.
Qed.

Lemma linear_division_identity (f : monic_sextic) (c : int) :
  monic_polynomial f =
    linear_factor c * linear_quotient f c +
      (f`_0 - c * linear_q0 f c)%:P.
Proof.
apply/polyP=> i.
rewrite /monic_polynomial /linear_factor /linear_quotient.
rewrite mulrDl !coefD coefXM coefCM.
case: i => [|[|[|[|[|[|i]]]]]].
all: repeat (first
  [ rewrite coefD | rewrite coefXM | rewrite coefCM
  | rewrite coefXn | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ]).
all: rewrite /linear_q0 /linear_q1 /linear_q2 /linear_q3 /linear_q4.
all: by rewrite ?subrKC ?subrK.
Qed.

Lemma quadratic_division_identity (f : monic_sextic) (b c : int) :
  monic_polynomial f =
    quadratic_factor b c * quadratic_quotient f b c +
      quadratic_remainder f b c.
Proof.
apply/polyP=> i.
rewrite /monic_polynomial /quadratic_factor /quadratic_quotient
  /quadratic_remainder.
rewrite !mulrDl -[b%:P * 'X * _]mulrA !coefD.
case: i => [|[|[|[|[|[|i]]]]]].
all: repeat (first
  [ rewrite coefD | rewrite coefXnM | rewrite coefXM
  | rewrite coefCM | rewrite coefXn | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ]).
all: rewrite /quadratic_q0 /quadratic_q1 /quadratic_q2 /quadratic_q3.
all: by rewrite ?add_add_sub_sub ?sub_sub_add_add ?subrKC ?subrK.
Qed.

Lemma cubic_division_identity (f : monic_sextic) (b c d : int) :
  monic_polynomial f =
    cubic_factor b c d * cubic_quotient f b c d +
      cubic_remainder f b c d.
Proof.
apply/polyP=> i.
rewrite /monic_polynomial /cubic_factor /cubic_quotient /cubic_remainder.
rewrite !mulrDl -[b%:P * 'X^2 * _]mulrA
  -[c%:P * 'X * _]mulrA !coefD.
case: i => [|[|[|[|[|[|i]]]]]].
all: repeat (first
  [ rewrite coefD | rewrite coefXnM | rewrite coefXM
  | rewrite coefCM | rewrite coefXn | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0 ]).
all: rewrite /cubic_q0 /cubic_q1 /cubic_q2.
all: by rewrite ?add_add_add_sub_sub_sub ?add_add_sub_sub
  ?sub_sub_add_add ?subrKC ?subrK.
Qed.

Definition has_bounded_linear_factor (f : monic_sextic) : bool :=
  has (fun c => linear_factor c %| monic_polynomial f)
    (symmetric_interval (root_bound f)).

Definition has_bounded_quadratic_factor (f : monic_sextic) : bool :=
  has (fun b => has (fun c => quadratic_factor b c %| monic_polynomial f)
    (symmetric_interval (root_bound f ^ 2)))
    (symmetric_interval (2 * root_bound f)).

Definition has_bounded_cubic_factor (f : monic_sextic) : bool :=
  has (fun b => has (fun c => has
      (fun d => cubic_factor b c d %| monic_polynomial f)
      (symmetric_interval (root_bound f ^ 3)))
    (symmetric_interval (3 * root_bound f ^ 2)))
    (symmetric_interval (3 * root_bound f)).

Definition has_bounded_nonlinear_factor (f : monic_sextic) : bool :=
  has_bounded_quadratic_factor f || has_bounded_cubic_factor f.

Definition has_bounded_proper_factor (f : monic_sextic) : bool :=
  has_bounded_linear_factor f || has_bounded_nonlinear_factor f.

Lemma has_bounded_linear_factorP (f : monic_sextic) :
  reflect
    (exists c, c \in symmetric_interval (root_bound f) /\
      linear_factor c %| monic_polynomial f)
    (has_bounded_linear_factor f).
Proof.
apply: (iffP hasP).
- move=> [c hc hd]; by exists c.
- by move=> [c [hc hd]]; exists c.
Qed.

Lemma has_bounded_quadratic_factorP (f : monic_sextic) :
  reflect
    (exists b, b \in symmetric_interval (2 * root_bound f) /\
     exists c, c \in symmetric_interval (root_bound f ^ 2) /\
       quadratic_factor b c %| monic_polynomial f)
    (has_bounded_quadratic_factor f).
Proof.
apply: (iffP hasP).
- move=> [b hb /hasP [c hc hd]].
  by exists b; split=> //; exists c.
- by move=> [b [hb [c [hc hd]]]]; exists b => //; apply/hasP; exists c.
Qed.

Lemma has_bounded_cubic_factorP (f : monic_sextic) :
  reflect
    (exists b, b \in symmetric_interval (3 * root_bound f) /\
     exists c, c \in symmetric_interval (3 * root_bound f ^ 2) /\
     exists d, d \in symmetric_interval (root_bound f ^ 3) /\
       cubic_factor b c d %| monic_polynomial f)
    (has_bounded_cubic_factor f).
Proof.
apply: (iffP hasP).
- move=> [b hb /hasP [c hc /hasP [d hd hdiv]]].
  by exists b; split=> //; exists c; split=> //; exists d.
- by move=> [b [hb [c [hc [d [hd hdiv]]]]]];
    exists b => //; apply/hasP; exists c => //; apply/hasP; exists d.
Qed.

(** Every accepted search witness is a genuinely proper divisor. *)
Lemma proper_divisor_not_irreducible (p q : {poly int})
    (hq_gt1 : (1 < size q)%N) (hq_lt_p : (size q < size p)%N)
    (hdiv : q %| p) : ~ irreducible_poly p.
Proof.
move=> hp.
have hq_ne1 : size q != 1%N.
  apply/eqP=> hq1.
  by move: hq_gt1; rewrite hq1 ltnn.
have heqp := hp.2 q hq_ne1 hdiv.
by move: hq_lt_p; rewrite (eqp_size heqp) ltnn.
Qed.

Lemma bounded_linear_factor_not_irreducible (f : monic_sextic) :
  has_bounded_linear_factor f -> ~ irreducible_poly (monic_polynomial f).
Proof.
move/has_bounded_linear_factorP=> [c [_ hdiv]].
apply: (proper_divisor_not_irreducible
  (p := monic_polynomial f) (q := linear_factor c)).
- by rewrite size_linear_factor.
- by rewrite size_linear_factor size_monic_polynomial.
- exact: hdiv.
Qed.

Lemma bounded_quadratic_factor_not_irreducible (f : monic_sextic) :
  has_bounded_quadratic_factor f ->
  ~ irreducible_poly (monic_polynomial f).
Proof.
move/has_bounded_quadratic_factorP=> [b [_ [c [_ hdiv]]]].
apply: (proper_divisor_not_irreducible
  (p := monic_polynomial f) (q := quadratic_factor b c)).
- by rewrite size_quadratic_factor.
- by rewrite size_quadratic_factor size_monic_polynomial.
- exact: hdiv.
Qed.

Lemma bounded_cubic_factor_not_irreducible (f : monic_sextic) :
  has_bounded_cubic_factor f -> ~ irreducible_poly (monic_polynomial f).
Proof.
move/has_bounded_cubic_factorP=> [b [_ [c [_ [d [_ hdiv]]]]]].
apply: (proper_divisor_not_irreducible
  (p := monic_polynomial f) (q := cubic_factor b c d)).
- by rewrite size_cubic_factor.
- by rewrite size_cubic_factor size_monic_polynomial.
- exact: hdiv.
Qed.

Lemma bounded_proper_factor_not_irreducible (f : monic_sextic) :
  has_bounded_proper_factor f -> ~ irreducible_poly (monic_polynomial f).
Proof.
rewrite /has_bounded_proper_factor /has_bounded_nonlinear_factor.
move/orP=> [hlin | /orP [hquad | hcubic]].
- exact: bounded_linear_factor_not_irreducible hlin.
- exact: bounded_quadratic_factor_not_irreducible hquad.
- exact: bounded_cubic_factor_not_irreducible hcubic.
Qed.

End PolynomialFormulasSexticRecursiveCore.
