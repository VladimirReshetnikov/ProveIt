From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantMultinomials LazardInvariantMpolyUnivariate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The honest monic reduction step for the last ordered root.

    The symmetric coefficient ring is represented by a fresh copy of the
    multivariate polynomial ring and embedded by elementary-symmetric
    substitution.  We first lift the Vieta polynomial to that coefficient
    ring, prove that it maps to the product of the linear root factors, and
    hence that the last root annihilates it.  Ordinary monic polynomial
    division then supplies a canonical remainder of degree below the number
    of roots, together with uniqueness among all such remainders.

    No coordinate, freeness, or kernel-of-evaluation hypothesis occurs in
    this file.  The later Artin successor proof must combine this canonical
    power reduction with the [muni]/[mmulti] equivalence and the inductive
    coordinates for the first [n] variables. *)
Module PolynomialFormulasLazardInvariantVietaReduction.

Import GRing.Theory.
Import Pdiv.RingMonic.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module MU := PolynomialFormulasLazardInvariantMpolyUnivariate.

(** Coefficient change leaves elementary symmetric polynomials unchanged. *)
Lemma map_mpoly_mesym (A B : ringType) n
    (f : {rmorphism A -> B}) k :
  map_mpoly f (mesym n A k) = mesym n B k.
Proof.
rewrite !mesymE raddf_sum.
apply: eq_bigr => h _.
exact: map_mpolyX.
Qed.

(** Lazard needs Vieta over an arbitrary commutative coefficient ring,
    whereas multinomials 2.4 states its universal identity over [int]. *)
Theorem lazard_viete (R : comRingType) n :
  \prod_(i < n) ('X - (('X_i : {mpoly R[n]}))%:P) =
  \sum_(k < n.+1)
    ((-1 : {mpoly R[n]}) ^+ k) *:
      (mesym n R k *: 'X^(n-k)).
Proof.
pose LF (i : 'I_n) : {poly {mpoly R[n]}} :=
  'X - (('X_i : {mpoly R[n]}))%:P.
pose RF (k : 'I_n.+1) : {poly {mpoly R[n]}} :=
  ((-1 : {mpoly R[n]}) ^+ k) *:
    (mesym n R k *: 'X^(n-k)).
move: (Viete n) =>
  /(congr1 (map_poly (@map_mpoly n int R intr))).
rewrite rmorph_prod /= (eq_bigr LF); last first.
  move=> i _; rewrite /LF map_polyXsubC.
  change ('X - ((@map_mpoly n int R intr)
    ('X_i : {mpoly int[n]}))%:P =
    'X - (('X_i : {mpoly R[n]}))%:P).
  by rewrite map_mpolyX.
rewrite raddf_sum /= (eq_bigr RF); last first.
  by move=> k _; rewrite /RF !map_polyZ rmorphXn /=
    rmorphN rmorph1 map_mpoly_mesym map_polyXn.
by move=> ->.
Qed.

Section LastVariableReduction.

Variables (R : comRingType) (n : nat).
Local Notation m := n.+1.
Local Notation Sym := {mpoly R[m]}.
Local Notation Ambient := {mpoly R[m]}.
Local Notation lastX := ('X_(ord_max) : Ambient).

(** A canonical coordinate preimage of an elementary symmetric polynomial.
    Existence is the fundamental theorem of symmetric polynomials; uniqueness
    follows from injectivity of [sym_eval]. *)
Definition lazard_esymm_coordinate (k : nat) : Sym :=
  sval (IM.symmetric_coordinates
    (p := mesym m R k) (mesym_sym m R k)).

Lemma lazard_esymm_coordinateE k :
  IM.sym_eval (lazard_esymm_coordinate k) = mesym m R k.
Proof.
rewrite /lazard_esymm_coordinate.
case: (IM.symmetric_coordinates
  (p := mesym m R k) (mesym_sym m R k)) => t [ht _] /=.
exact: ht.
Qed.

(** The monic Vieta polynomial, but with every symmetric coefficient living
    in the source copy of the symmetric ring. *)
Definition lazard_last_vieta_polynomial : {poly Sym} :=
  \sum_(k < m.+1)
    ((-1 : Sym) ^+ k) *:
      (lazard_esymm_coordinate k *: 'X^(m-k)).

(** Realize formal symmetric coefficients in the root polynomial ring. *)
Definition lazard_last_variable_realize (q : {poly Sym}) : Ambient :=
  (map_poly (@IM.sym_eval R m) q).[lastX].

Lemma lazard_last_variable_realize0 :
  lazard_last_variable_realize 0 = 0.
Proof.
by rewrite /lazard_last_variable_realize map_poly0 horner0.
Qed.

Lemma lazard_last_variable_realize1 :
  lazard_last_variable_realize 1 = 1.
Proof.
by rewrite /lazard_last_variable_realize rmorph1 hornerC.
Qed.

Lemma lazard_last_variable_realizeD :
  {morph lazard_last_variable_realize : q r / q + r}.
Proof.
by move=> q r; rewrite /lazard_last_variable_realize raddfD /= hornerD.
Qed.

Lemma lazard_last_variable_realizeN :
  {morph lazard_last_variable_realize : q / - q}.
Proof.
by move=> q; rewrite /lazard_last_variable_realize raddfN /= hornerN.
Qed.

Lemma lazard_last_variable_realizeB :
  {morph lazard_last_variable_realize : q r / q - r}.
Proof.
move=> q r.
change (lazard_last_variable_realize (q + (- r)) =
  lazard_last_variable_realize q +
    (- lazard_last_variable_realize r)).
by rewrite lazard_last_variable_realizeD lazard_last_variable_realizeN.
Qed.

Lemma lazard_last_variable_realizeM :
  {morph lazard_last_variable_realize : q r / q * r}.
Proof.
by move=> q r; rewrite /lazard_last_variable_realize rmorphM /= hornerM.
Qed.

Lemma lazard_last_variable_realizeC c :
  lazard_last_variable_realize c%:P = IM.sym_eval c.
Proof.
rewrite /lazard_last_variable_realize.
change ((map_poly
  (IM.PolynomialFormulasLazardInvariantMultinomials_sym_eval__canonical__Algebra_Additive
    R m) c%:P).[lastX] =
  IM.sym_eval c).
by rewrite map_polyC hornerC.
Qed.

Lemma lazard_last_variable_realizeX :
  lazard_last_variable_realize 'X = lastX.
Proof.
rewrite /lazard_last_variable_realize.
change ((map_poly
  (IM.PolynomialFormulasLazardInvariantMultinomials_sym_eval__canonical__GRing_RMorphism
    R m) 'X).[lastX] = lastX).
by rewrite map_polyX hornerX.
Qed.

Lemma lazard_last_vieta_polynomial_map :
  map_poly (@IM.sym_eval R m) lazard_last_vieta_polynomial =
    \prod_(i < m) ('X - (('X_i : Ambient))%:P).
Proof.
rewrite /lazard_last_vieta_polynomial raddf_sum /=.
transitivity (\sum_(k < m.+1)
  ((-1 : Ambient) ^+ k) *:
    (mesym m R k *: 'X^(m-k))).
- apply: eq_bigr => k _.
  rewrite !map_polyZ rmorphXn /= rmorphN rmorph1 map_polyXn.
  change (((-1 : Ambient) ^+ k) *:
    (IM.sym_eval (lazard_esymm_coordinate k) *: 'X^(m-k)) =
    ((-1 : Ambient) ^+ k) *:
      (mesym m R k *: 'X^(m-k))).
  by rewrite lazard_esymm_coordinateE.
- exact/esym/lazard_viete.
Qed.

Lemma lazard_last_vieta_polynomial_monic :
  lazard_last_vieta_polynomial \is monic.
Proof.
apply/monicP.
apply: IM.sym_eval_injective.
rewrite IM.sym_eval1.
rewrite -(lead_coef_map_inj (@IM.sym_eval_injective R m)
  (@IM.sym_eval0 R m)).
rewrite lazard_last_vieta_polynomial_map.
exact: lead_coef_prod_XsubC.
Qed.

Lemma lazard_last_vieta_polynomial_size :
  size lazard_last_vieta_polynomial = m.+1.
Proof.
rewrite -(size_map_inj_poly (@IM.sym_eval_injective R m)
  (@IM.sym_eval0 R m) lazard_last_vieta_polynomial).
rewrite lazard_last_vieta_polynomial_map size_prod_XsubC.
by rewrite /index_enum unlock -enumT size_enum_ord.
Qed.

(** The last root kills the realized Vieta polynomial because its own linear
    factor occurs in the product. *)
Lemma lazard_last_vieta_polynomial_realize0 :
  lazard_last_variable_realize lazard_last_vieta_polynomial = 0.
Proof.
rewrite /lazard_last_variable_realize
  lazard_last_vieta_polynomial_map (bigD1 ord_max) //=.
by rewrite hornerM hornerXsubC subrr mul0r.
Qed.

(** Canonical bounded power reduction. *)
Definition lazard_last_vieta_remainder (q : {poly Sym}) : {poly Sym} :=
  Pdiv.CommonRing.rmodp q lazard_last_vieta_polynomial.

Definition lazard_last_vieta_quotient (q : {poly Sym}) : {poly Sym} :=
  Pdiv.CommonRing.rdivp q lazard_last_vieta_polynomial.

Theorem lazard_last_vieta_division q :
  q = lazard_last_vieta_quotient q * lazard_last_vieta_polynomial +
      lazard_last_vieta_remainder q.
Proof.
exact: (Pdiv.RingMonic.rdivp_eq lazard_last_vieta_polynomial_monic q).
Qed.

Theorem lazard_last_vieta_remainder_size q :
  (size (lazard_last_vieta_remainder q) < m.+1)%N.
Proof.
rewrite -lazard_last_vieta_polynomial_size.
apply: Pdiv.CommonRing.ltn_rmodpN0.
exact: monic_neq0 lazard_last_vieta_polynomial_monic.
Qed.

(** Reduction does not change the realized polynomial value. *)
Theorem lazard_last_vieta_remainder_realize q :
  lazard_last_variable_realize (lazard_last_vieta_remainder q) =
    lazard_last_variable_realize q.
Proof.
rewrite {2}(lazard_last_vieta_division q)
  lazard_last_variable_realizeD lazard_last_variable_realizeM
  lazard_last_vieta_polynomial_realize0.
by rewrite mulr0 add0r.
Qed.

(** The canonical remainder is the unique small remainder in a division
    decomposition. *)
Theorem lazard_last_vieta_remainder_unique
    (q a r : {poly Sym}) :
  (size r < m.+1)%N ->
  q = a * lazard_last_vieta_polynomial + r ->
  r = lazard_last_vieta_remainder q.
Proof.
move=> hr hq.
rewrite /lazard_last_vieta_remainder hq.
apply/esym.
apply: (Pdiv.RingMonic.rmodp_addl_mul_small
  lazard_last_vieta_polynomial_monic).
by rewrite lazard_last_vieta_polynomial_size.
Qed.

Corollary lazard_last_vieta_small_remainders_unique
    (q a b r s : {poly Sym}) :
  (size r < m.+1)%N -> (size s < m.+1)%N ->
  q = a * lazard_last_vieta_polynomial + r ->
  q = b * lazard_last_vieta_polynomial + s ->
  r = s.
Proof.
move=> hr hs hqr hqs.
rewrite (lazard_last_vieta_remainder_unique hr hqr)
  (lazard_last_vieta_remainder_unique hs hqs).
exact: erefl.
Qed.

(** A remainder is zero exactly when the original polynomial is a multiple
    of the Vieta relation.  This is the kernel statement for the canonical
    quotient normal form; it does not assume that realization is injective. *)
Theorem lazard_last_vieta_remainder_eq0_iff_multiple q :
  lazard_last_vieta_remainder q = 0 <->
  exists a, q = a * lazard_last_vieta_polynomial.
Proof.
split.
- move=> hzero.
  exists (lazard_last_vieta_quotient q).
  have hdiv := lazard_last_vieta_division q.
  by rewrite hzero addr0 in hdiv.
- move=> [a ->].
  apply/esym.
  apply: (lazard_last_vieta_remainder_unique
    (q := a * lazard_last_vieta_polynomial) (a := a) (r := 0)).
  + by rewrite size_poly0.
  + by rewrite addr0.
Qed.

(** The degree-bounded representative attached to a coefficient sequence. *)
Definition lazard_last_vieta_bounded_polynomial
    (c : nat -> Sym) : {poly Sym} :=
  \poly_(i < m) c i.

Lemma lazard_last_vieta_bounded_polynomial_size c :
  (size (lazard_last_vieta_bounded_polynomial c) <= m)%N.
Proof. exact: size_poly. Qed.

(** Coefficients of the canonical remainder, indexed by ordinary naturals;
    only indices below [m] occur in reconstruction. *)
Definition lazard_last_vieta_coordinate q (i : nat) : Sym :=
  (lazard_last_vieta_remainder q)`_i.

Theorem lazard_last_vieta_remainder_coordinates q :
  lazard_last_vieta_remainder q =
    lazard_last_vieta_bounded_polynomial
      (lazard_last_vieta_coordinate q).
Proof.
have hsize : (size (lazard_last_vieta_remainder q) <= m)%N.
  by move: (lazard_last_vieta_remainder_size q); rewrite ltnS.
apply/esym.
change (take_poly m (lazard_last_vieta_remainder q) =
  lazard_last_vieta_remainder q).
exact: take_poly_id hsize.
Qed.

(** Canonical quotient coordinates reconstruct every polynomial modulo the
    monic relation. *)
Theorem lazard_last_vieta_coordinates_reconstruct q :
  q = lazard_last_vieta_quotient q * lazard_last_vieta_polynomial +
      lazard_last_vieta_bounded_polynomial
        (lazard_last_vieta_coordinate q).
Proof.
rewrite -lazard_last_vieta_remainder_coordinates.
exact: lazard_last_vieta_division.
Qed.

(** Any other bounded coefficient presentation has the same coordinates. *)
Theorem lazard_last_vieta_coordinates_unique q a c :
  q = a * lazard_last_vieta_polynomial +
      lazard_last_vieta_bounded_polynomial c ->
  forall i, (i < m)%N ->
    c i = lazard_last_vieta_coordinate q i.
Proof.
move=> hq i hi.
have hb : (size (lazard_last_vieta_bounded_polynomial c) < m.+1)%N.
  by rewrite ltnS; exact: lazard_last_vieta_bounded_polynomial_size.
have hrem := lazard_last_vieta_remainder_unique hb hq.
move: (congr1 (fun p : {poly Sym} => p`_i) hrem).
by rewrite /lazard_last_vieta_bounded_polynomial
  /lazard_last_vieta_coordinate coef_poly hi.
Qed.

End LastVariableReduction.

End PolynomialFormulasLazardInvariantVietaReduction.
