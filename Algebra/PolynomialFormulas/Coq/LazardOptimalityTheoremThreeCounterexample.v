From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import char0 cyclotomic_ext abel.
From PolynomialFormulas Require Import
  LazardOptimality
  LazardOptimalityCyclicQuinticCounterexample.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The field-degree part of the cyclic-quintic counterexample to Lazard's
    Theorem 3.

    This file proves, inside the concrete fifty-fifth cyclotomic ambient
    field from [LazardOptimalityCyclicQuinticCounterexample], that

      Q(zeta11 + zeta11^-1, zeta5)

    has degree twenty, whereas Q(zeta11) has degree ten.  It also isolates
    the exact Kummer argument by which a genuine one-root Lazard formula
    field contains [zeta5].  The last package is deliberately parameterized
    by a formula-field profile: the present Coq root-origin development does
    not yet construct that profile from the raw Lazard branch data.  Thus no
    branch, descent, or formula fact is hidden as an axiom. *)
Module PolynomialFormulasLazardOptimalityTheoremThreeCounterexample.

Import GRing.Theory.
Local Open Scope ring_scope.

Module T4 :=
  PolynomialFormulasLazardOptimalityCyclicQuinticCounterexample.
Module O := PolynomialFormulasLazardOptimality.

(* -------------------------------------------------------------------- *)
(** * Explicit fifth and eleventh cyclotomic polynomials *)

Section ExplicitPolynomialShape.

Variable R : comNzRingType.

Lemma size_polyD_lt_bound n (p q : {poly R}) :
  (size p < n)%N -> (size q < n)%N -> (size (p + q)%R < n)%N.
Proof.
move=> hp hq.
have hle :
    (size (p + q)%R <= maxn (size p) (size q))%N := size_polyD p q.
have hmax : (maxn (size p) (size q) < n)%N.
  by rewrite gtn_max hp hq.
exact: leq_ltn_trans hle hmax.
Qed.

Lemma size_Xn_lt_bound n bound :
  (n.+1 < bound)%N -> (size ('X^n : {poly R}) < bound)%N.
Proof. by move=> hn; rewrite size_polyXn. Qed.

Lemma size_scale_Xn_lt_bound (c : R) n bound :
  (n.+1 < bound)%N ->
  (size (c *: ('X^n : {poly R})) < bound)%N.
Proof.
move=> hn.
have hle :
    (size (c *: ('X^n : {poly R})) <= size ('X^n : {poly R}))%N :=
  size_scale_leq c 'X^n.
exact: leq_ltn_trans hle (size_Xn_lt_bound hn).
Qed.

Lemma size_X_lt_bound bound :
  (2 < bound)%N -> (size ('X : {poly R}) < bound)%N.
Proof. by move=> hbound; rewrite size_polyX. Qed.

Lemma size_scale_X_lt_bound (c : R) bound :
  (2 < bound)%N -> (size (c *: ('X : {poly R})) < bound)%N.
Proof.
move=> hbound.
have hle :
    (size (c *: ('X : {poly R})) <= size ('X : {poly R}))%N :=
  size_scale_leq c 'X.
exact: leq_ltn_trans hle (size_X_lt_bound hbound).
Qed.

Lemma size_polyC_lt_bound (c : R) bound :
  (1 < bound)%N -> (size c%:P < bound)%N.
Proof.
move=> hbound.
exact: leq_ltn_trans (size_polyC_leq1 c) hbound.
Qed.

Lemma size_Xn_add_lower n (p : {poly R}) :
  (size p < n.+1)%N -> size ('X^n + p) = n.+1.
Proof. by move=> hp; rewrite size_polyDl ?size_polyXn. Qed.

Lemma monic_Xn_add_lower n (p : {poly R}) :
  (size p < n.+1)%N -> 'X^n + p \is monic.
Proof.
move=> hp; apply/eqP.
by rewrite lead_coefDl ?size_polyXn ?lead_coefXn.
Qed.

End ExplicitPolynomialShape.

Definition fifth_cyclotomic_lower_Z : {poly int} :=
  'X^3 + ('X^2 + ('X + 1)).

Definition fifth_cyclotomic_Z : {poly int} :=
  'X^4 + fifth_cyclotomic_lower_Z.

Definition shifted_fifth_cyclotomic_lower_Z : {poly int} :=
  (5 : int) *: 'X^3 +
    ((10 : int) *: 'X^2 + ((10 : int) *: 'X + 5%:P)).

Definition shifted_fifth_cyclotomic_Z : {poly int} :=
  'X^4 + shifted_fifth_cyclotomic_lower_Z.

Definition fifth_cyclotomic_Q : {poly rat} :=
  map_poly (intr : int -> rat) fifth_cyclotomic_Z.

Definition shifted_fifth_cyclotomic_Q : {poly rat} :=
  map_poly (intr : int -> rat) shifted_fifth_cyclotomic_Z.

Lemma fifth_cyclotomic_lower_Z_size_lt :
  (size fifth_cyclotomic_lower_Z < 5)%N.
Proof.
rewrite /fifth_cyclotomic_lower_Z.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first exact: size_X_lt_bound (isT : (2 < 5)%N).
exact: size_polyC_lt_bound (isT : (1 < 5)%N).
Qed.

Lemma shifted_fifth_cyclotomic_lower_Z_size_lt :
  (size shifted_fifth_cyclotomic_lower_Z < 5)%N.
Proof.
rewrite /shifted_fifth_cyclotomic_lower_Z.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first exact: size_scale_X_lt_bound (isT : (2 < 5)%N).
exact: size_polyC_lt_bound (isT : (1 < 5)%N).
Qed.

Lemma fifth_cyclotomic_Z_size : size fifth_cyclotomic_Z = 5%N.
Proof.
rewrite /fifth_cyclotomic_Z.
exact: size_Xn_add_lower fifth_cyclotomic_lower_Z_size_lt.
Qed.

Lemma fifth_cyclotomic_Z_monic : fifth_cyclotomic_Z \is monic.
Proof.
rewrite /fifth_cyclotomic_Z.
exact: monic_Xn_add_lower fifth_cyclotomic_lower_Z_size_lt.
Qed.

Lemma fifth_cyclotomic_Q_size : size fifth_cyclotomic_Q = 5%N.
Proof.
by rewrite /fifth_cyclotomic_Q size_rat_int_poly fifth_cyclotomic_Z_size.
Qed.

Lemma fifth_cyclotomic_Q_monic : fifth_cyclotomic_Q \is monic.
Proof.
rewrite /fifth_cyclotomic_Q.
exact: monic_map fifth_cyclotomic_Z_monic.
Qed.

Lemma shifted_fifth_cyclotomic_Z_size :
  size shifted_fifth_cyclotomic_Z = 5%N.
Proof.
rewrite /shifted_fifth_cyclotomic_Z.
exact: size_Xn_add_lower shifted_fifth_cyclotomic_lower_Z_size_lt.
Qed.

Lemma shifted_fifth_cyclotomic_Z_monic :
  shifted_fifth_cyclotomic_Z \is monic.
Proof.
rewrite /shifted_fifth_cyclotomic_Z.
exact: monic_Xn_add_lower shifted_fifth_cyclotomic_lower_Z_size_lt.
Qed.

Lemma shifted_fifth_cyclotomic_Z_coef0 :
  shifted_fifth_cyclotomic_Z`_0 = 5.
Proof.
rewrite /shifted_fifth_cyclotomic_Z
  /shifted_fifth_cyclotomic_lower_Z
  !coefD !coefZ !coefXn !coefX !coefC.
by rewrite !mulr0 !add0r.
Qed.

Lemma shifted_fifth_cyclotomic_Z_irreducible :
  irreducible_poly shifted_fifth_cyclotomic_Z.
Proof.
apply: (eisenstein_crit (p := 5)).
- by vm_compute.
- by rewrite shifted_fifth_cyclotomic_Z_size.
- rewrite (eqP shifted_fifth_cyclotomic_Z_monic).
  by vm_compute.
- rewrite shifted_fifth_cyclotomic_Z_coef0.
  by vm_compute.
- move=> i hi.
  rewrite /shifted_fifth_cyclotomic_Z
    /shifted_fifth_cyclotomic_lower_Z
    !coefD !coefZ !coefXn !coefX !coefC.
  have hi4 : (i < 4)%N.
    by move: hi; rewrite shifted_fifth_cyclotomic_Z_size.
  clear hi.
  move: i hi4 => [|[|[|[|i]]]] hi4.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by move: hi4; rewrite !ltnS.
Qed.

Lemma shifted_fifth_cyclotomic_Q_irreducible :
  irreducible_poly shifted_fifth_cyclotomic_Q.
Proof.
rewrite /shifted_fifth_cyclotomic_Q irreducible_rat_int.
exact: shifted_fifth_cyclotomic_Z_irreducible.
Qed.

(** The translation is proved over the integers.  Rather than expanding a
    composition sum, we translate the geometric-factor identity and cancel
    [X]; each shifted factor coefficient contains a single binomial term. *)
Lemma fifth_cyclotomic_Z_factor :
  ('X - (1 : int)%:P) * fifth_cyclotomic_Z =
    'X^5 - (1 : int)%:P.
Proof.
apply/polyP=> i.
rewrite mulrBl mul1r coefB coefXM.
rewrite /fifth_cyclotomic_Z /fifth_cyclotomic_lower_Z
  !coefD !coefN !coefXn !coefX !coefC.
case: i => [|[|[|[|[|[|i]]]]]];
  rewrite /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?subr0 ?sub0r ?subrr;
  reflexivity.
Qed.

Lemma shifted_fifth_cyclotomic_Z_factor :
  'X * shifted_fifth_cyclotomic_Z =
    ('X + (1 : int)%:P)^5 - (1 : int)%:P.
Proof.
apply/polyP=> i.
rewrite coefB coefXM T4.cyclic_coef_XaddC_exp.
rewrite /shifted_fifth_cyclotomic_Z /shifted_fifth_cyclotomic_lower_Z
  !coefD !coefZ !coefXn !coefX !coefC.
case: i => [|[|[|[|[|[|i]]]]]];
  rewrite /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?subr0 ?sub0r ?subrr ?mulr0n ?mul0rn ?expr0 ?expr1;
  reflexivity.
Qed.

(** A reusable translation/cancellation bridge for finite geometric sums.
    It is stated over the integer polynomial ring because that is the common
    source of both explicit cyclotomic computations below. *)
Lemma translate_geometric_factor n (p q : {poly int}) :
  ('X - (1 : int)%:P) * p = 'X^n - (1 : int)%:P ->
  'X * q = ('X + (1 : int)%:P)^n - (1 : int)%:P ->
  p \Po ('X + (1 : int)%:P) = q.
Proof.
move=> hp hq.
have hcomp := congr1
  (fun r : {poly int} => r \Po ('X + (1 : int)%:P)) hp.
rewrite comp_polyM !comp_polyB !comp_Xn_poly !comp_polyX !comp_polyC
  addrK in hcomp.
have hXnonzero : ('X : {poly int}) != 0.
  by rewrite -size_poly_eq0 size_polyX.
apply: (mulfI hXnonzero).
by rewrite hq hcomp.
Qed.

Lemma fifth_cyclotomic_Z_translate :
  fifth_cyclotomic_Z \Po ('X + (1 : int)%:P) =
    shifted_fifth_cyclotomic_Z.
Proof.
exact: translate_geometric_factor fifth_cyclotomic_Z_factor
  shifted_fifth_cyclotomic_Z_factor.
Qed.

Lemma map_poly_int_Xadd1 :
  map_poly (intr : int -> rat) ('X + (1 : int)%:P) =
    'X + (1 : rat)%:P.
Proof.
rewrite rmorphD.
change (map_poly (intr : int -> rat) 'X +
  map_poly (intr : int -> rat) (1 : int)%:P =
    'X + (1 : rat)%:P).
rewrite map_polyX map_polyC.
reflexivity.
Qed.

Lemma fifth_cyclotomic_Q_translate :
  fifth_cyclotomic_Q \Po ('X + (1 : rat)%:P) =
    shifted_fifth_cyclotomic_Q.
Proof.
rewrite /fifth_cyclotomic_Q /shifted_fifth_cyclotomic_Q.
rewrite -map_poly_int_Xadd1 -map_comp_poly fifth_cyclotomic_Z_translate.
reflexivity.
Qed.

Lemma fifth_cyclotomic_Q_irreducible :
  irreducible_poly fifth_cyclotomic_Q.
Proof.
apply: (T4.irreducible_of_comp_XaddC (c := (1 : rat))).
rewrite fifth_cyclotomic_Q_translate.
exact: shifted_fifth_cyclotomic_Q_irreducible.
Qed.

Lemma cyclotomic_one_Z : 'Phi_1 = ('X - (1 : int)%:P).
Proof.
have h := prod_Cyclotomic (n := 1) (isT : (0 < 1)%N).
have hdiv : divisors 1 = [:: 1] by vm_compute.
move: h.
by rewrite hdiv big_cons big_nil mulr1 expr1.
Qed.

Lemma fifth_cyclotomic_Z_eq_Cyclotomic :
  fifth_cyclotomic_Z = 'Phi_5.
Proof.
have hprod := prod_Cyclotomic (n := 5) (isT : (0 < 5)%N).
have hdiv : divisors 5 = [:: 1; 5] by vm_compute.
move: hprod; rewrite hdiv !big_cons big_nil mulr1 cyclotomic_one_Z
  => hprod.
have hnonzero : ('X - (1 : int)%:P : {poly int}) != 0.
  by rewrite -size_poly_eq0 size_XsubC.
apply: (mulfI hnonzero).
by rewrite fifth_cyclotomic_Z_factor hprod.
Qed.

Lemma fifth_cyclotomic_Q_eq_cyclotomic_rat :
  fifth_cyclotomic_Q = T4.cyclotomic_rat 5.
Proof.
by rewrite /fifth_cyclotomic_Q /T4.cyclotomic_rat
  fifth_cyclotomic_Z_eq_Cyclotomic.
Qed.

Definition eleventh_cyclotomic_lower_Z : {poly int} :=
  'X^9 + ('X^8 + ('X^7 + ('X^6 + ('X^5 +
    ('X^4 + ('X^3 + ('X^2 + ('X + 1)))))))).

Definition eleventh_cyclotomic_Z : {poly int} :=
  'X^10 + eleventh_cyclotomic_lower_Z.

Definition shifted_eleventh_cyclotomic_lower_Z : {poly int} :=
  (11 : int) *: 'X^9 + ((55 : int) *: 'X^8 +
    ((165 : int) *: 'X^7 + ((330 : int) *: 'X^6 +
    ((462 : int) *: 'X^5 + ((462 : int) *: 'X^4 +
    ((330 : int) *: 'X^3 + ((165 : int) *: 'X^2 +
    ((55 : int) *: 'X + 11%:P)))))))).

Definition shifted_eleventh_cyclotomic_Z : {poly int} :=
  'X^10 + shifted_eleventh_cyclotomic_lower_Z.

Definition eleventh_cyclotomic_Q : {poly rat} :=
  map_poly (intr : int -> rat) eleventh_cyclotomic_Z.

Definition shifted_eleventh_cyclotomic_Q : {poly rat} :=
  map_poly (intr : int -> rat) shifted_eleventh_cyclotomic_Z.

Lemma eleventh_cyclotomic_lower_Z_size_lt :
  (size eleventh_cyclotomic_lower_Z < 11)%N.
Proof.
rewrite /eleventh_cyclotomic_lower_Z.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_Xn_lt_bound.
apply: size_polyD_lt_bound; first exact: size_X_lt_bound (isT : (2 < 11)%N).
exact: size_polyC_lt_bound (isT : (1 < 11)%N).
Qed.

Lemma shifted_eleventh_cyclotomic_lower_Z_size_lt :
  (size shifted_eleventh_cyclotomic_lower_Z < 11)%N.
Proof.
rewrite /shifted_eleventh_cyclotomic_lower_Z.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first by apply: size_scale_Xn_lt_bound.
apply: size_polyD_lt_bound; first exact: size_scale_X_lt_bound (isT : (2 < 11)%N).
exact: size_polyC_lt_bound (isT : (1 < 11)%N).
Qed.

Lemma eleventh_cyclotomic_Z_size : size eleventh_cyclotomic_Z = 11%N.
Proof.
rewrite /eleventh_cyclotomic_Z.
exact: size_Xn_add_lower eleventh_cyclotomic_lower_Z_size_lt.
Qed.

Lemma eleventh_cyclotomic_Z_monic : eleventh_cyclotomic_Z \is monic.
Proof.
rewrite /eleventh_cyclotomic_Z.
exact: monic_Xn_add_lower eleventh_cyclotomic_lower_Z_size_lt.
Qed.

Lemma eleventh_cyclotomic_Q_size : size eleventh_cyclotomic_Q = 11%N.
Proof.
by rewrite /eleventh_cyclotomic_Q size_rat_int_poly
  eleventh_cyclotomic_Z_size.
Qed.

Lemma eleventh_cyclotomic_Q_monic : eleventh_cyclotomic_Q \is monic.
Proof.
rewrite /eleventh_cyclotomic_Q.
exact: monic_map eleventh_cyclotomic_Z_monic.
Qed.

Lemma shifted_eleventh_cyclotomic_Z_size :
  size shifted_eleventh_cyclotomic_Z = 11%N.
Proof.
rewrite /shifted_eleventh_cyclotomic_Z.
exact: size_Xn_add_lower shifted_eleventh_cyclotomic_lower_Z_size_lt.
Qed.

Lemma shifted_eleventh_cyclotomic_Z_monic :
  shifted_eleventh_cyclotomic_Z \is monic.
Proof.
rewrite /shifted_eleventh_cyclotomic_Z.
exact: monic_Xn_add_lower shifted_eleventh_cyclotomic_lower_Z_size_lt.
Qed.

Lemma shifted_eleventh_cyclotomic_Z_coef0 :
  shifted_eleventh_cyclotomic_Z`_0 = 11.
Proof.
rewrite /shifted_eleventh_cyclotomic_Z
  /shifted_eleventh_cyclotomic_lower_Z
  !coefD !coefZ !coefXn !coefX !coefC.
by rewrite !mulr0 !add0r.
Qed.

Lemma shifted_eleventh_cyclotomic_Z_irreducible :
  irreducible_poly shifted_eleventh_cyclotomic_Z.
Proof.
apply: (eisenstein_crit (p := 11)).
- by vm_compute.
- by rewrite shifted_eleventh_cyclotomic_Z_size.
- rewrite (eqP shifted_eleventh_cyclotomic_Z_monic).
  by vm_compute.
- rewrite shifted_eleventh_cyclotomic_Z_coef0.
  by vm_compute.
- move=> i hi.
  rewrite /shifted_eleventh_cyclotomic_Z
    /shifted_eleventh_cyclotomic_lower_Z
    !coefD !coefZ !coefXn !coefX !coefC.
  have hi10 : (i < 10)%N.
    by move: hi; rewrite shifted_eleventh_cyclotomic_Z_size.
  clear hi.
  move: i hi10 => [|[|[|[|[|[|[|[|[|[|i]]]]]]]]]] hi10.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by move: hi10; rewrite !ltnS.
Qed.

Lemma shifted_eleventh_cyclotomic_Q_irreducible :
  irreducible_poly shifted_eleventh_cyclotomic_Q.
Proof.
rewrite /shifted_eleventh_cyclotomic_Q irreducible_rat_int.
exact: shifted_eleventh_cyclotomic_Z_irreducible.
Qed.

(** The two geometric-factor identities below give an efficient translation
    proof.  The shifted identity has only one binomial term per coefficient,
    rather than the eleven summands produced by expanding composition. *)
Lemma eleventh_cyclotomic_Z_factor :
  ('X - (1 : int)%:P) * eleventh_cyclotomic_Z =
    'X^11 - (1 : int)%:P.
Proof.
apply/polyP=> i.
rewrite mulrBl mul1r coefB coefXM.
rewrite /eleventh_cyclotomic_Z /eleventh_cyclotomic_lower_Z
  !coefD !coefN !coefXn !coefX !coefC.
case: i => [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]];
  rewrite /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?subr0 ?sub0r ?subrr;
  reflexivity.
Qed.

Lemma shifted_eleventh_cyclotomic_Z_factor :
  'X * shifted_eleventh_cyclotomic_Z =
    ('X + (1 : int)%:P)^11 - (1 : int)%:P.
Proof.
apply/polyP=> i.
rewrite coefB coefXM T4.cyclic_coef_XaddC_exp.
rewrite /shifted_eleventh_cyclotomic_Z
  /shifted_eleventh_cyclotomic_lower_Z
  !coefD !coefZ !coefXn !coefX !coefC.
case: i => [|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]];
  rewrite /= ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?subr0 ?sub0r ?subrr ?mulr0n ?mul0rn ?expr0 ?expr1;
  reflexivity.
Qed.

Lemma eleventh_cyclotomic_Z_translate :
  eleventh_cyclotomic_Z \Po ('X + (1 : int)%:P) =
    shifted_eleventh_cyclotomic_Z.
Proof.
exact: translate_geometric_factor eleventh_cyclotomic_Z_factor
  shifted_eleventh_cyclotomic_Z_factor.
Qed.

Lemma eleventh_cyclotomic_Q_translate :
  eleventh_cyclotomic_Q \Po ('X + (1 : rat)%:P) =
    shifted_eleventh_cyclotomic_Q.
Proof.
rewrite /eleventh_cyclotomic_Q /shifted_eleventh_cyclotomic_Q.
rewrite -map_poly_int_Xadd1 -map_comp_poly
  eleventh_cyclotomic_Z_translate.
reflexivity.
Qed.

Lemma eleventh_cyclotomic_Q_irreducible :
  irreducible_poly eleventh_cyclotomic_Q.
Proof.
apply: (T4.irreducible_of_comp_XaddC (c := (1 : rat))).
rewrite eleventh_cyclotomic_Q_translate.
exact: shifted_eleventh_cyclotomic_Q_irreducible.
Qed.

Lemma eleventh_cyclotomic_Z_eq_Cyclotomic :
  eleventh_cyclotomic_Z = 'Phi_11.
Proof.
have hprod := prod_Cyclotomic (n := 11) (isT : (0 < 11)%N).
have hdiv : divisors 11 = [:: 1; 11] by vm_compute.
move: hprod; rewrite hdiv !big_cons big_nil mulr1 cyclotomic_one_Z
  => hprod.
have hnonzero : ('X - (1 : int)%:P : {poly int}) != 0.
  by rewrite -size_poly_eq0 size_XsubC.
apply: (mulfI hnonzero).
by rewrite eleventh_cyclotomic_Z_factor hprod.
Qed.

Lemma eleventh_cyclotomic_Q_eq_cyclotomic_rat :
  eleventh_cyclotomic_Q = T4.cyclotomic_rat 11.
Proof.
by rewrite /eleventh_cyclotomic_Q /T4.cyclotomic_rat
  eleventh_cyclotomic_Z_eq_Cyclotomic.
Qed.

(** The mapped rational cyclotomic polynomial vanishes at any primitive
    root in the fixed ambient field. *)
Lemma primitive_root_is_root_cyclotomic_rat n (z : T4.Ambient) :
  n.-primitive_root z ->
  root (map_poly (in_alg T4.Ambient) (T4.cyclotomic_rat n)) z.
Proof.
move=> z_primitive.
rewrite /T4.cyclotomic_rat -map_poly_comp.
have hmap :
    (in_alg T4.Ambient) \o (intr : int -> rat) =1
      (intr : int -> T4.Ambient).
  by move=> a /=; rewrite scaler_int.
rewrite (eq_map_poly hmap) (Phi_cyclotomic z_primitive).
by rewrite root_cyclotomic.
Qed.

Lemma zeta5_root_fifth_cyclotomic :
  root (map_poly (in_alg T4.Ambient) fifth_cyclotomic_Q) T4.zeta5.
Proof.
rewrite fifth_cyclotomic_Q_eq_cyclotomic_rat.
exact: primitive_root_is_root_cyclotomic_rat T4.zeta5_primitive.
Qed.

Lemma zeta11_root_eleventh_cyclotomic :
  root (map_poly (in_alg T4.Ambient) eleventh_cyclotomic_Q) T4.zeta11.
Proof.
rewrite eleventh_cyclotomic_Q_eq_cyclotomic_rat.
exact: primitive_root_is_root_cyclotomic_rat T4.zeta11_primitive.
Qed.

Lemma fifth_cyclotomic_eq_minPoly :
  map_poly (in_alg T4.Ambient) fifth_cyclotomic_Q =
    minPoly 1 T4.zeta5.
Proof.
exact: T4.irreducible_monic_root_eq_minPoly
  fifth_cyclotomic_Q_irreducible fifth_cyclotomic_Q_monic
  zeta5_root_fifth_cyclotomic.
Qed.

Lemma eleventh_cyclotomic_eq_minPoly :
  map_poly (in_alg T4.Ambient) eleventh_cyclotomic_Q =
    minPoly 1 T4.zeta11.
Proof.
exact: T4.irreducible_monic_root_eq_minPoly
  eleventh_cyclotomic_Q_irreducible eleventh_cyclotomic_Q_monic
  zeta11_root_eleventh_cyclotomic.
Qed.

(* -------------------------------------------------------------------- *)
(** * The three concrete subfields and their degrees *)

Definition CyclicQuinticField : {subfield T4.Ambient} :=
  <<1; T4.cyclic_quintic_root>>%AS.

Definition FifthCyclotomicField : {subfield T4.Ambient} :=
  <<1; T4.zeta5>>%AS.

Definition CyclicQuinticCompositum : {subfield T4.Ambient} :=
  <<CyclicQuinticField; T4.zeta5>>%AS.

Lemma cyclicQuinticField_dim : \dim CyclicQuinticField = 5%N.
Proof.
rewrite /CyclicQuinticField dim_Fadjoin dimv1 muln1.
apply: succn_inj.
rewrite -size_minPoly -T4.cyclic_quintic_eq_minPoly.
by rewrite size_map_poly T4.cyclic_quintic_Q_size.
Qed.

Lemma fifthCyclotomicField_dim : \dim FifthCyclotomicField = 4%N.
Proof.
rewrite /FifthCyclotomicField dim_Fadjoin dimv1 muln1.
apply: succn_inj.
rewrite -size_minPoly -fifth_cyclotomic_eq_minPoly.
by rewrite size_map_poly fifth_cyclotomic_Q_size.
Qed.

Lemma elevenField_dim : \dim T4.ElevenField = 10%N.
Proof.
rewrite /T4.ElevenField dim_Fadjoin dimv1 muln1.
apply: succn_inj.
rewrite -size_minPoly -eleventh_cyclotomic_eq_minPoly.
by rewrite size_map_poly eleventh_cyclotomic_Q_size.
Qed.

Lemma cyclicQuinticField_le_compositum :
  (CyclicQuinticField <= CyclicQuinticCompositum)%VS.
Proof. exact: subv_adjoin. Qed.

Lemma fifthCyclotomicField_le_compositum :
  (FifthCyclotomicField <= CyclicQuinticCompositum)%VS.
Proof.
exact: adjoinSl (sub1v CyclicQuinticField).
Qed.

(** The elementary upper bound: adjoining [zeta5] to any rational
    subfield has degree at most four because its fourth-degree cyclotomic
    polynomial is still available over that subfield. *)
Lemma zeta5_adjoin_degree_over_cyclic_le_four :
  (adjoin_degree CyclicQuinticField T4.zeta5 <= 4)%N.
Proof.
have hp_over :
    map_poly (in_alg T4.Ambient) fifth_cyclotomic_Q
      \is a polyOver CyclicQuinticField :=
  alg_polyOver CyclicQuinticField fifth_cyclotomic_Q.
have hdiv :
    minPoly CyclicQuinticField T4.zeta5 %|
      map_poly (in_alg T4.Ambient) fifth_cyclotomic_Q :=
  minPoly_dvdp hp_over zeta5_root_fifth_cyclotomic.
have hp_monic :
    map_poly (in_alg T4.Ambient) fifth_cyclotomic_Q \is monic.
  by rewrite map_monic fifth_cyclotomic_Q_monic.
have hsize := dvdp_leq (monic_neq0 hp_monic) hdiv.
move: hsize.
by rewrite size_minPoly size_map_poly fifth_cyclotomic_Q_size.
Qed.

Lemma cyclicQuinticCompositum_dim_le_twenty :
  (\dim CyclicQuinticCompositum <= 20)%N.
Proof.
rewrite /CyclicQuinticCompositum dim_Fadjoin cyclicQuinticField_dim.
move: zeta5_adjoin_degree_over_cyclic_le_four.
by rewrite -[20%N]/(4 * 5)%N leq_pmul2r.
Qed.

Lemma twenty_dvd_cyclicQuinticCompositum_dim :
  (20 %| \dim CyclicQuinticCompositum)%N.
Proof.
have h5 : (5 %| \dim CyclicQuinticCompositum)%N.
  move: (field_dimS cyclicQuinticField_le_compositum).
  by rewrite cyclicQuinticField_dim.
have h4 : (4 %| \dim CyclicQuinticCompositum)%N.
  move: (field_dimS fifthCyclotomicField_le_compositum).
  by rewrite fifthCyclotomicField_dim.
rewrite -[20%N]/(5 * 4)%N Gauss_dvd //.
by rewrite h5 h4.
Qed.

Theorem cyclicQuinticCompositum_dim :
  \dim CyclicQuinticCompositum = 20%N.
Proof.
apply/eqP.
rewrite eqn_leq cyclicQuinticCompositum_dim_le_twenty andTb.
exact: dvdn_leq (adim_gt0 CyclicQuinticCompositum)
  twenty_dvd_cyclicQuinticCompositum_dim.
Qed.

(** This is the unconditional degree obstruction needed in Theorem 3. *)
Theorem cyclicQuinticCompositum_not_sub_elevenField :
  ~ (CyclicQuinticCompositum <= T4.ElevenField)%VS.
Proof.
move=> hsub.
have hdim := dimvS hsub.
move: hdim.
by rewrite cyclicQuinticCompositum_dim elevenField_dim.
Qed.

Lemma cyclic_quintic_root_mem_elevenField :
  T4.cyclic_quintic_root \in T4.ElevenField.
Proof.
rewrite /T4.cyclic_quintic_root /T4.ElevenField.
apply: rpredD; first exact: memv_adjoin.
by rewrite memvV memv_adjoin.
Qed.

(** Reusable prime-order lemma used by the Kummer argument below. *)
Lemma nontrivial_fifth_root_is_primitive
    (F : fieldType) (x : F) :
  x ^+ 5 = 1 -> x != 1 -> 5.-primitive_root x.
Proof.
move=> x_pow_five x_neq1.
have [m m_primitive m_dvd_five] :=
  prim_order_exists (n := 5) (z := x)
    (isT : 0 < 5)%N x_pow_five.
have prime_five : prime 5 by [].
have [_ five_divisors] := (elimT primeP prime_five).
have /orP[/eqP m_eq1 | /eqP m_eq5] :=
  five_divisors m m_dvd_five.
- exfalso.
  have x_eq1 : x = 1.
    move: (prim_expr_order m_primitive).
    by rewrite m_eq1 expr1.
  move: x_neq1.
  by rewrite x_eq1 eqxx.
- by rewrite -m_eq5.
Qed.

(* -------------------------------------------------------------------- *)
(** * Formula-field profile and the Kummer ratio *)

(** Exact field facts consumed by the degree contradiction.  This is a
    proof-carrying interface, not an asserted witness.  In particular the
    profile records the formula-specific containment in the degree-twenty
    compositum and the nontrivial cyclic action on its selected fifth
    radical. *)
Record cyclic_lazard_formula_field_profile
    (K0 E : {subfield T4.Ambient}) := CyclicLazardFormulaFieldProfile {
  profile_p1 : T4.Ambient;
  profile_base_le_formula : (K0 <= E)%VS;
  profile_cyclicQuintic_le_formula : (CyclicQuinticField <= E)%VS;
  profile_formula_le_compositum : (E <= CyclicQuinticCompositum)%VS;
  profile_p1_mem : profile_p1 \in E;
  profile_p1_nonzero : profile_p1 != 0;
  profile_p1_fifth_mem : profile_p1 ^+ 5 \in K0;
  profile_formula_generated :
    (E : {vspace T4.Ambient}) =
      agenv (((K0 : {vspace T4.Ambient}) + <[profile_p1]>)%VS);
  (** An actual algebra endomorphism is required here: mere linearity does
      not justify the fifth-power step in the Kummer ratio argument. *)
  profile_conjugation : 'AEnd(T4.Ambient);
  profile_conjugation_stable :
    forall x, x \in E -> profile_conjugation x \in E;
  profile_conjugation_fixes_base :
    forall x, x \in K0 -> profile_conjugation x = x;
  profile_conjugation_moves_p1 :
    profile_conjugation profile_p1 != profile_p1
}.

Section FormulaProfile.

Variables (K0 E : {subfield T4.Ambient}).
Variable P : cyclic_lazard_formula_field_profile K0 E.

Definition profile_fifth_root_ratio : T4.Ambient :=
  profile_conjugation P (profile_p1 P) / profile_p1 P.

Lemma profile_fifth_root_ratio_mem : profile_fifth_root_ratio \in E.
Proof.
apply: rpred_div.
- exact: @profile_conjugation_stable K0 E P
    (profile_p1 P) (profile_p1_mem P).
- exact: profile_p1_mem P.
Qed.

Lemma profile_fifth_root_ratio_pow_five :
  profile_fifth_root_ratio ^+ 5 = 1.
Proof.
rewrite /profile_fifth_root_ratio expr_div_n.
have hpow :
    profile_conjugation P (profile_p1 P) ^+ 5 =
      profile_conjugation P (profile_p1 P ^+ 5).
  by rewrite rmorphXn.
have hfix :
    profile_conjugation P (profile_p1 P ^+ 5) = profile_p1 P ^+ 5 :=
  @profile_conjugation_fixes_base K0 E P
    (profile_p1 P ^+ 5) (profile_p1_fifth_mem P).
rewrite hpow hfix.
have hp1_fifth_nonzero : profile_p1 P ^+ 5 != 0 :=
  expf_neq0 5 (profile_p1_nonzero P).
exact: divff hp1_fifth_nonzero.
Qed.

Lemma profile_fifth_root_ratio_nontrivial :
  profile_fifth_root_ratio != 1.
Proof.
apply/negP=> /eqP hratio.
apply: (negP (profile_conjugation_moves_p1 P)).
apply/eqP.
exact: divr1_eq hratio.
Qed.

(** Since five is prime, a nontrivial fifth root of unity is primitive. *)
Lemma profile_fifth_root_ratio_primitive :
  5.-primitive_root profile_fifth_root_ratio.
Proof.
exact: nontrivial_fifth_root_is_primitive
  profile_fifth_root_ratio_pow_five
  profile_fifth_root_ratio_nontrivial.
Qed.

(** The Kummer ratio is an element of [E], and every primitive fifth root
    is a power of it.  Hence the displayed [zeta5] itself belongs to [E]. *)
Lemma profile_zeta5_mem_formula : T4.zeta5 \in E.
Proof.
have [k _ zeta5E] :=
  @primitive_root_pow T4.Ambient 5 T4.zeta5
    profile_fifth_root_ratio profile_fifth_root_ratio_primitive
    T4.zeta5_primitive.
rewrite zeta5E.
exact: rpredX profile_fifth_root_ratio_mem.
Qed.

Lemma profile_compositum_le_formula :
  (CyclicQuinticCompositum <= E)%VS.
Proof.
apply/FadjoinP; split.
- exact: profile_cyclicQuintic_le_formula P.
- exact: profile_zeta5_mem_formula.
Qed.

Theorem profile_formula_eq_compositum : E = CyclicQuinticCompositum.
Proof.
apply: val_inj; apply: subv_anti; apply/andP; split.
- exact: profile_formula_le_compositum P.
- exact: profile_compositum_le_formula.
Qed.

Theorem profile_formula_dim : \dim E = 20%N.
Proof. by rewrite profile_formula_eq_compositum cyclicQuinticCompositum_dim. Qed.

Theorem profile_formula_not_sub_elevenField :
  ~ (E <= T4.ElevenField)%VS.
Proof.
move=> hsub.
apply: cyclicQuinticCompositum_not_sub_elevenField.
exact: subv_trans profile_compositum_le_formula hsub.
Qed.

(** Conditional field-theoretic form of the Theorem 3 contradiction. *)
Theorem theoremThree_formula_degree_obstruction :
  [/\
    E = CyclicQuinticCompositum,
    \dim E = 20%N
  & ~ (E <= T4.ElevenField)%VS].
Proof.
split.
- exact: profile_formula_eq_compositum.
- exact: profile_formula_dim.
- exact: profile_formula_not_sub_elevenField.
Qed.

End FormulaProfile.

(** All unconditional arithmetic and competing-field facts, together with
    the precise formula-field profile still to be constructed from a Coq
    root-origin Lazard branch. *)
Theorem lazard_theorem3_conditional_counterexample
    (K0 E : {subfield T4.Ambient})
    (P : cyclic_lazard_formula_field_profile K0 E) :
  [/\
    size T4.cyclic_quintic_Q = 6%N,
    T4.cyclic_quintic_Q \is monic,
    irreducible_poly T4.cyclic_quintic_Q
  & [/\
      root (map_poly (in_alg T4.Ambient) T4.cyclic_quintic_Q)
        T4.cyclic_quintic_root,
      T4.cyclic_quintic_root \in T4.ElevenField,
      O.radical_extension (L := T4.Ambient) 1 T4.ElevenField
    & [/\
        \dim T4.ElevenField = 10%N,
        E = CyclicQuinticCompositum,
        \dim E = 20%N
      & ~ (E <= T4.ElevenField)%VS]]].
Proof.
split.
- exact: T4.cyclic_quintic_Q_size.
- exact: T4.cyclic_quintic_Q_monic.
- exact: T4.cyclic_quintic_Q_irreducible.
- split.
  + exact: T4.cyclic_quintic_root_is_root.
  + exact: cyclic_quintic_root_mem_elevenField.
  + exact: T4.ElevenField_radical_extension.
  + split.
    * exact: elevenField_dim.
    * exact: profile_formula_eq_compositum P.
    * exact: profile_formula_dim P.
    * exact: profile_formula_not_sub_elevenField P.
Qed.

End PolynomialFormulasLazardOptimalityTheoremThreeCounterexample.
