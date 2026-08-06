From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From Stdlib Require Import Classical_Prop.
From PolynomialFormulas Require Import
  SexticRecursiveCore SexticFactorCompleteness.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** A coefficient-recursive reducibility test for monic integer quintics.

    A monic quintic is stored by its five lower coefficients, in ascending
    order.  Every Boolean below is a transparent Gallina program: it uses
    fixed tuples, integer arithmetic, polynomial pseudo-division, and finite
    list search only.  In particular, no semantic [numfield] decision enters
    this module.

    For completeness of the finite bounds, [p] is embedded as the sextic
    [X * p].  This lets us reuse the already proved sextic Cauchy/Vieta bounds
    without changing the executable quintic search. *)
Module PolynomialFormulasQuinticRecursiveFactor.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticFactorCompleteness.

Definition monic_quintic := 5.-tuple int.

(** The sextic coefficient tuple for [X * p]. *)
Definition quintic_sextic_embedding
    (f : monic_quintic) : monic_sextic :=
  [tuple nth 0 (0 :: f) i | i < 6].

Lemma quintic_sextic_embeddingE (f : monic_quintic) (i : 'I_6) :
  tnth (quintic_sextic_embedding f) i = nth 0 (0 :: f) i.
Proof. by rewrite /quintic_sextic_embedding tnth_mktuple. Qed.

Lemma quintic_sextic_embedding_nthE (f : monic_quintic) i
    (hi : (i < 6)%N) :
  nth 0 (quintic_sextic_embedding f) i = nth 0 (0 :: f) i.
Proof.
rewrite -(inordK hi).
exact: nth_mktuple.
Qed.

Lemma quintic_sextic_embedding0 (f : monic_quintic) :
  (quintic_sextic_embedding f)`_0 = 0.
Proof. exact: quintic_sextic_embedding_nthE. Qed.

(** Reuse synthetic division by [X + 0] to obtain the polynomial
    [X^5 + f_4 X^4 + ... + f_0]. *)
Definition quintic_polynomial (f : monic_quintic) : {poly int} :=
  linear_quotient (quintic_sextic_embedding f) 0.

Lemma quintic_embedding_identity (f : monic_quintic) :
  monic_polynomial (quintic_sextic_embedding f) =
    'X * quintic_polynomial f.
Proof.
move: (linear_division_identity (quintic_sextic_embedding f) 0).
rewrite /linear_factor /quintic_polynomial quintic_sextic_embedding0.
by rewrite !mul0r !subr0 !rmorph0 !addr0.
Qed.

Lemma size_quintic_polynomial (f : monic_quintic) :
  size (quintic_polynomial f) = 6%N.
Proof.
apply: (size_poly_from_top_coefficient (n := 5%N)).
- rewrite /quintic_polynomial /linear_quotient.
  repeat (first
    [ rewrite coefD | rewrite coefXn | rewrite coefCM
    | rewrite coefX | rewrite coefC ]).
  simpl.
  by rewrite ?mulr0 ?addr0 ?oner_eq0.
- move=> j; case: j => [|[|[|[|[|[|j]]]]]] // _.
  rewrite /quintic_polynomial /linear_quotient.
  repeat (first
    [ rewrite coefD | rewrite coefXn | rewrite coefCM
    | rewrite coefX | rewrite coefC ]).
  simpl.
  by rewrite ?mulr0 ?addr0.
Qed.

Lemma quintic_polynomial_monic (f : monic_quintic) :
  quintic_polynomial f \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_quintic_polynomial.
rewrite /quintic_polynomial /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
simpl.
by rewrite ?mulr0 ?addr0.
Qed.

(** Reading the five lower coefficients of a polynomial.  This is the
    conversion used for the quintic quotient of a sextic linear factor. *)
Definition monic_quintic_of_poly (p : {poly int}) : monic_quintic :=
  [tuple p`_i | i < 5].

Lemma monic_quintic_of_polyE (p : {poly int}) (i : 'I_5) :
  tnth (monic_quintic_of_poly p) i = p`_i.
Proof. by rewrite /monic_quintic_of_poly tnth_mktuple. Qed.

Lemma monic_quintic_of_poly_nthE (p : {poly int}) i
    (hi : (i < 5)%N) :
  nth 0 (monic_quintic_of_poly p) i = p`_i.
Proof.
rewrite /monic_quintic_of_poly -(inordK hi).
exact: nth_mktuple.
Qed.

Lemma size_linear_quotient (f : monic_sextic) (c : int) :
  size (linear_quotient f c) = 6%N.
Proof.
apply: (size_poly_from_top_coefficient (n := 5%N)).
- rewrite /linear_quotient.
  repeat (first
    [ rewrite coefD | rewrite coefXn | rewrite coefCM
    | rewrite coefX | rewrite coefC ]).
  simpl.
  by rewrite ?mulr0 ?addr0 ?oner_eq0.
- move=> j; case: j => [|[|[|[|[|[|j]]]]]] // _.
  rewrite /linear_quotient.
  repeat (first
    [ rewrite coefD | rewrite coefXn | rewrite coefCM
    | rewrite coefX | rewrite coefC ]).
  simpl.
  by rewrite ?mulr0 ?addr0.
Qed.

Lemma linear_quotient_monic (f : monic_sextic) (c : int) :
  linear_quotient f c \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_linear_quotient /linear_quotient.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
simpl.
by rewrite ?mulr0 ?addr0.
Qed.

(** A fixed-tuple reconstruction theorem: on monic size-six polynomials,
    reading the lower coefficients and rebuilding the quintic is exact. *)
Lemma quintic_polynomial_of_poly (p : {poly int}) :
  size p = 6%N -> p \is monic ->
  quintic_polynomial (monic_quintic_of_poly p) = p.
Proof.
move=> hp_size hp_monic.
apply/polyP=> i.
case: i => [|[|[|[|[|[|i]]]]]].
all: rewrite /quintic_polynomial /linear_quotient.
all: repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite add0r | rewrite addr0
  | rewrite subr0 ]).
- rewrite /linear_q0 /linear_q1 /linear_q2 /linear_q3 /linear_q4.
  rewrite !mul0r !subr0.
  rewrite (quintic_sextic_embedding_nthE
    (monic_quintic_of_poly p) (i := 1%N) isT) /=.
  exact: monic_quintic_of_poly_nthE.
- rewrite /linear_q1 /linear_q2 /linear_q3 /linear_q4.
  rewrite !mul0r !subr0.
  rewrite (quintic_sextic_embedding_nthE
    (monic_quintic_of_poly p) (i := 2%N) isT) /=.
  exact: monic_quintic_of_poly_nthE.
- rewrite /linear_q2 /linear_q3 /linear_q4.
  rewrite !mul0r !subr0.
  rewrite (quintic_sextic_embedding_nthE
    (monic_quintic_of_poly p) (i := 3%N) isT) /=.
  exact: monic_quintic_of_poly_nthE.
- rewrite /linear_q3 /linear_q4.
  rewrite !mul0r !subr0.
  rewrite (quintic_sextic_embedding_nthE
    (monic_quintic_of_poly p) (i := 4%N) isT) /=.
  exact: monic_quintic_of_poly_nthE.
- rewrite /linear_q4 subr0.
  rewrite (quintic_sextic_embedding_nthE
    (monic_quintic_of_poly p) (i := 5%N) isT) /=.
  exact: monic_quintic_of_poly_nthE.
- have hlead := elimT monicP hp_monic.
  by move: hlead; rewrite lead_coefE hp_size.
- rewrite nth_default; last by rewrite hp_size.
  by [] .
Qed.

Definition sextic_linear_quotient_quintic
    (f : monic_sextic) (c : int) : monic_quintic :=
  monic_quintic_of_poly (linear_quotient f c).

Theorem sextic_linear_quotient_quintic_correct
    (f : monic_sextic) (c : int) :
  quintic_polynomial (sextic_linear_quotient_quintic f c) =
  linear_quotient f c.
Proof.
apply: quintic_polynomial_of_poly.
- exact: size_linear_quotient.
- exact: linear_quotient_monic.
Qed.

Theorem sextic_linear_factorization_quintic
    (f : monic_sextic) (c : int) :
  linear_remainder_zerob f c ->
  monic_polynomial f = linear_factor c *
    quintic_polynomial (sextic_linear_quotient_quintic f c).
Proof.
move/linear_remainder_zeroP=> hrem.
rewrite sextic_linear_quotient_quintic_correct.
move: (linear_division_identity f c).
by rewrite hrem subrr rmorph0 addr0.
Qed.

(** The bound is an explicit coefficient expression through the embedding.
    It is deliberately a little larger than necessary; finiteness and
    completeness, rather than tightness, are what the recursive decision
    needs. *)
Definition quintic_root_bound (f : monic_quintic) : nat :=
  root_bound (quintic_sextic_embedding f).

Definition has_bounded_linear_factor (f : monic_quintic) : bool :=
  has (fun c => linear_factor c %| quintic_polynomial f)
    (symmetric_interval (quintic_root_bound f)).

Definition has_bounded_quadratic_factor (f : monic_quintic) : bool :=
  has (fun b => has (fun c =>
      quadratic_factor b c %| quintic_polynomial f)
    (symmetric_interval (quintic_root_bound f ^ 2)))
    (symmetric_interval (2 * quintic_root_bound f)).

Definition has_bounded_proper_factor (f : monic_quintic) : bool :=
  has_bounded_linear_factor f || has_bounded_quadratic_factor f.

Lemma has_bounded_linear_factorP (f : monic_quintic) :
  reflect
    (exists c, c \in symmetric_interval (quintic_root_bound f) /\
      linear_factor c %| quintic_polynomial f)
    (has_bounded_linear_factor f).
Proof.
apply: (iffP hasP).
- move=> [c hc hd]; by exists c.
- by move=> [c [hc hd]]; exists c.
Qed.

Lemma has_bounded_quadratic_factorP (f : monic_quintic) :
  reflect
    (exists b, b \in symmetric_interval (2 * quintic_root_bound f) /\
     exists c, c \in symmetric_interval (quintic_root_bound f ^ 2) /\
       quadratic_factor b c %| quintic_polynomial f)
    (has_bounded_quadratic_factor f).
Proof.
apply: (iffP hasP).
- move=> [b hb /hasP [c hc hd]].
  by exists b; split=> //; exists c.
- by move=> [b [hb [c [hc hd]]]]; exists b => //;
    apply/hasP; exists c.
Qed.

Lemma bounded_linear_factor_not_irreducible (f : monic_quintic) :
  has_bounded_linear_factor f ->
  ~ irreducible_poly (quintic_polynomial f).
Proof.
move/has_bounded_linear_factorP=> [c [_ hdiv]].
apply: (proper_divisor_not_irreducible
  (p := quintic_polynomial f) (q := linear_factor c)).
- by rewrite size_linear_factor.
- by rewrite size_linear_factor size_quintic_polynomial.
- exact: hdiv.
Qed.

Lemma bounded_quadratic_factor_not_irreducible (f : monic_quintic) :
  has_bounded_quadratic_factor f ->
  ~ irreducible_poly (quintic_polynomial f).
Proof.
move/has_bounded_quadratic_factorP=> [b [_ [c [_ hdiv]]]].
apply: (proper_divisor_not_irreducible
  (p := quintic_polynomial f) (q := quadratic_factor b c)).
- by rewrite size_quadratic_factor.
- by rewrite size_quadratic_factor size_quintic_polynomial.
- exact: hdiv.
Qed.

Lemma bounded_proper_factor_not_irreducible (f : monic_quintic) :
  has_bounded_proper_factor f ->
  ~ irreducible_poly (quintic_polynomial f).
Proof.
rewrite /has_bounded_proper_factor.
move/orP=> [hlin | hquad].
- exact: bounded_linear_factor_not_irreducible hlin.
- exact: bounded_quadratic_factor_not_irreducible hquad.
Qed.

(** Any divisor of the quintic remains a divisor after multiplication by
    [X].  Consequently the sextic root bounds apply to exactly the quintic
    candidates searched above. *)
Lemma quintic_divisor_divides_embedding (f : monic_quintic)
    (q : {poly int}) :
  q %| quintic_polynomial f ->
  q %| monic_polynomial (quintic_sextic_embedding f).
Proof.
move=> hdiv; rewrite quintic_embedding_identity.
exact: (dvdp_trans hdiv (dvdp_mulIr 'X (quintic_polynomial f))).
Qed.

Lemma linear_factor_bounded_of_dvdp (f : monic_quintic) (c : int) :
  linear_factor c %| quintic_polynomial f ->
  c \in symmetric_interval (quintic_root_bound f).
Proof.
move/quintic_divisor_divides_embedding.
exact: linear_factor_mem_symmetric_interval_of_dvdp.
Qed.

Lemma quadratic_factor_bounded_of_dvdp
    (f : monic_quintic) (b c : int) :
  quadratic_factor b c %| quintic_polynomial f ->
  b \in symmetric_interval (2 * quintic_root_bound f) /\
  c \in symmetric_interval (quintic_root_bound f ^ 2).
Proof.
move/quintic_divisor_divides_embedding.
exact: quadratic_factor_coefficients_bounded_of_dvdp.
Qed.

(** Negating MathComp's propositional irreducibility criterion yields a
    proper divisor.  For degree five, one of a factor and its cofactor has
    degree at most two, hence polynomial [size] at most three. *)
Lemma reducible_size6_has_small_factor (p : {poly rat}) :
  size p = 6%N -> ~ irreducible_poly p ->
  exists q : {poly rat}, (1 < size q <= 3)%N /\ q %| p.
Proof.
move=> hp6 hnot.
have hex : exists q : {poly rat},
    size q != 1%N /\ q %| p /\ ~ q %= p.
  apply: NNPP=> hnex.
  apply: hnot; split; first by rewrite hp6.
  move=> q hq1 hdiv.
  case heq: (q %= p); first by [] .
  exfalso; apply: hnex; exists q; split=> //; split=> //.
  by rewrite heq.
have [q [hq1 [hqdiv hqneqp]]] := hex.
have hp0 : p != 0 by rewrite -size_poly_gt0 hp6.
have hq0 : q != 0.
  apply: contraTneq hqdiv=> ->.
  by rewrite dvd0p (negPf hp0).
have hqgt1 : (1 < size q)%N.
  by rewrite ltn_neqAle eq_sym hq1 size_poly_gt0 hq0.
have hqsize_ne : size q != size p.
  apply/eqP=> hsize.
  apply: hqneqp.
  move: (dvdp_size_eqp hqdiv).
  by rewrite hsize eqxx => <-.
have hqlt : (size q < size p)%N.
  rewrite ltn_neqAle hqsize_ne.
  exact: dvdp_leq hp0 hqdiv.
case/dvdpP/sig_eqW: hqdiv => r hproduct.
have hr0 : r != 0.
  apply/negP=> /eqP hrzero.
  by move: hp0; rewrite hproduct hrzero mul0r eqxx.
have hrdiv : r %| p.
  by rewrite hproduct; exact: dvdp_mulIl.
have hqdiv' : q %| p.
  by rewrite hproduct; exact: dvdp_mulIr.
have hsize_product : size p = (size r + size q).-1.
  by rewrite hproduct size_mul.
case hqle3: (size q <= 3)%N.
- have hqle3P : (size q <= 3)%N by rewrite hqle3.
  exists q; split; last exact: hqdiv'.
  by apply/andP; split.
- have hqgt3 : (3 < size q)%N by rewrite ltnNge hqle3.
  have hrpos : (0 < size r)%N by rewrite size_poly_gt0 hr0.
  have hsumpos : (0 < size r + size q)%N :=
    leq_trans hrpos (leq_addr (size q) (size r)).
  have hsum_eq : (size p).+1 = size r + size q.
    rewrite hsize_product.
    exact: prednK hsumpos.
  have /orP [/eqP hq4 | /eqP hq5] :
      (size q == 4%N) || (size q == 5%N).
    move: hqgt3 hqlt; rewrite hp6.
    by case: (size q) => [|[|[|[|[|[|n]]]]]] //.
  + have hr3 : size r = 3%N.
      move: hsum_eq; rewrite hp6 hq4 /=.
      move=> heq.
      apply/eqP; rewrite -(eqn_add2r 4%N); apply/eqP.
      exact: esym heq.
    exists r; split; last exact: hrdiv.
    by rewrite hr3.
  + have hr2 : size r = 2%N.
      move: hsum_eq; rewrite hp6 hq5 /=.
      move=> heq.
      apply/eqP; rewrite -(eqn_add2r 5%N); apply/eqP.
      exact: esym heq.
    exists r; split; last exact: hrdiv.
    by rewrite hr2.
Qed.

(** Gauss's lemma, specialized to the monic quintic target, clears a
    rational factor's denominators and normalizes its sign. *)
Lemma lift_monic_rational_quintic_factor
    (f : monic_quintic) (q : {poly rat}) :
  (1 < size q)%N ->
  q %| map_poly (intr : int -> rat) (quintic_polynomial f) ->
  exists qz : {poly int},
    qz \is monic /\ size qz = size q /\
    qz %| quintic_polynomial f.
Proof.
move=> hqgt1.
case/dvdpP_rat_int=> qz [a ha hscale] [r hproduct].
have hsize : size qz = size q.
  have h := congr1 (fun u : {poly rat} => size u) hscale.
  rewrite size_scale // size_rat_int_poly in h.
  exact: esym h.
have hqzdiv : qz %| quintic_polynomial f.
  by rewrite hproduct; exact: dvdp_mulIl.
have hleadprod : lead_coef qz * lead_coef r = 1.
  rewrite -lead_coefM -hproduct.
  exact: elimT monicP (quintic_polynomial_monic f).
have hunit : lead_coef qz \is a intUnitRing.unitz.
  apply: (intUnitRing.unitzPl (n := lead_coef r)).
  by rewrite mulrC hleadprod.
move: hunit; rewrite qualifE => /orP [/eqP hlead | /eqP hlead].
- exists qz; split; first exact/monicP.
  by split.
- exists (- qz); split.
  + apply/monicP.
    by rewrite lead_coefN hlead opprK.
  + rewrite size_polyN hsize; split=> //.
    by rewrite dvdpNl.
Qed.

Lemma not_irreducible_bounded_proper_factor (f : monic_quintic) :
  ~ irreducible_poly (quintic_polynomial f) ->
  has_bounded_proper_factor f.
Proof.
move=> hnot.
pose pQ := map_poly (intr : int -> rat) (quintic_polynomial f).
have hpQsize : size pQ = 6%N.
  by rewrite /pQ size_rat_int_poly size_quintic_polynomial.
have hnotQ : ~ irreducible_poly pQ.
  move=> hirrQ; apply: hnot.
  exact: (proj1 (irreducible_rat_int (quintic_polynomial f))) hirrQ.
have [q [hqsmall hqdiv]] :=
  reducible_size6_has_small_factor hpQsize hnotQ.
have hqgt1 : (1 < size q)%N := (andP hqsmall).1.
have [qm [hqmonic [hqsize hqmdiv]]] :=
  lift_monic_rational_quintic_factor hqgt1 hqdiv.
have /orP [/eqP hsize2 | /eqP hsize3] :
    (size qm == 2%N) || (size qm == 3%N).
  move: hqsmall; rewrite -hqsize.
  by case: (size qm) => [|[|[|[|n]]]] //.
- have hform := monic_size2_linear_factor hqmonic hsize2.
  rewrite hform in hqmdiv.
  have hc := linear_factor_bounded_of_dvdp hqmdiv.
  rewrite /has_bounded_proper_factor.
  apply/orP; left; apply/has_bounded_linear_factorP.
  by exists qm`_0.
- have hform := monic_size3_quadratic_factor hqmonic hsize3.
  rewrite hform in hqmdiv.
  have [hb hc] := quadratic_factor_bounded_of_dvdp hqmdiv.
  rewrite /has_bounded_proper_factor.
  apply/orP; right; apply/has_bounded_quadratic_factorP.
  by exists qm`_1; split=> //; exists qm`_0.
Qed.

Theorem has_bounded_proper_factor_iff_not_irreducible
    (f : monic_quintic) :
  has_bounded_proper_factor f <->
  ~ irreducible_poly (quintic_polynomial f).
Proof.
split.
- exact: bounded_proper_factor_not_irreducible.
- exact: not_irreducible_bounded_proper_factor.
Qed.

Theorem has_bounded_proper_factorP (f : monic_quintic) :
  reflect (~ irreducible_poly (quintic_polynomial f))
    (has_bounded_proper_factor f).
Proof.
apply: (iffP idP).
- exact: bounded_proper_factor_not_irreducible.
- exact: not_irreducible_bounded_proper_factor.
Qed.

(** Gauss's lemma transfers the same executable Boolean to the rational
    quintic used by the Galois-theoretic criterion. *)
Theorem has_bounded_proper_factor_ratP (f : monic_quintic) :
  reflect
    (~ irreducible_poly
      (map_poly (intr : int -> rat) (quintic_polynomial f)))
    (has_bounded_proper_factor f).
Proof.
apply: (iffP (has_bounded_proper_factorP f)).
- move=> hnotZ hirrQ; apply: hnotZ.
  exact: (proj1 (irreducible_rat_int (quintic_polynomial f))) hirrQ.
- move=> hnotQ hirrZ; apply: hnotQ.
  exact: (proj2 (irreducible_rat_int (quintic_polynomial f))) hirrZ.
Qed.

(** The complementary Boolean is the directly usable irreducibility branch
    of a recursive quintic decision. *)
Definition quintic_irreducibleb (f : monic_quintic) : bool :=
  ~~ has_bounded_proper_factor f.

Theorem quintic_irreducibleP (f : monic_quintic) :
  reflect (irreducible_poly (quintic_polynomial f))
    (quintic_irreducibleb f).
Proof.
rewrite /quintic_irreducibleb.
apply: (iffP negP).
- move=> hfalse.
  apply: NNPP=> hnot.
  have htrue := introT (has_bounded_proper_factorP f) hnot.
  by move: hfalse; rewrite htrue.
- move=> hirr htrue.
  exact: (elimT (has_bounded_proper_factorP f) htrue) hirr.
Qed.

Theorem quintic_irreducible_ratP (f : monic_quintic) :
  reflect
    (irreducible_poly
      (map_poly (intr : int -> rat) (quintic_polynomial f)))
    (quintic_irreducibleb f).
Proof.
rewrite /quintic_irreducibleb.
apply: (iffP negP).
- move=> hfalse.
  apply: NNPP=> hnot.
  have htrue := introT (has_bounded_proper_factor_ratP f) hnot.
  by move: hfalse; rewrite htrue.
- move=> hirr htrue.
  exact: (elimT (has_bounded_proper_factor_ratP f) htrue) hirr.
Qed.

End PolynomialFormulasQuinticRecursiveFactor.
