From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import abel.
From PolynomialFormulas Require Import
  AbelRuffini QuinticRecursiveFactor QuinticCanonicalDecision
  QuinticThetaValues QuinticF20Data QuinticRadicalDecidability
  SexticHomogeneousRootSearch
  LazardQuinticCoherentAlternateConcreteCompositum.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The arbitrary-rational-coefficient adapter for the integer Lazard
    pipeline.

    The executable Coq development stores a monic quintic as five *integer*
    lower coefficients.  If

             p(X) = X^5 + a4 X^4 + ... + a0

    has rational coefficients, let [D] be the product of the five positive
    denominators.  This file constructs, without a divisibility oracle, the
    integer coefficients of

             pD(Y) = D^5 p(Y / D)
                   = Y^5 + a4 D Y^4 + ... + a0 D^5.

    For [i < 5] the stored integer is

      numq(a_i) * (product of denq(a_j), j != i) * D^(4-i).

    Its cast to [rat] is exactly [a_i * D^(5-i)].  The remainder of the
    file records the transports needed by the Lazard front end: roots,
    depressedness, irreducibility, degree-four theta values, rational
    resolvent witnesses, and division of the integer-pipeline output by
    [D].

    This adapter is registered in both project manifests, but remains a
    source-level completion gate until the public Coq build accepts it.  It
    contains no [Axiom] and no [Admitted]. *)
Module PolynomialFormulasLazardQuinticRationalScalingAdapter.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Notation ratrC := (@ratr algC).

Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QC := PolynomialFormulasQuinticCanonicalDecision.
Module TV := PolynomialFormulasQuinticThetaValues.
Module F20 := PolynomialFormulasQuinticF20Data.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module TGB := PolynomialFormulasQuinticThetaGaloisBridge.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module SCV := PolynomialFormulasSexticComputedResolvents.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module HRS := PolynomialFormulasSexticHomogeneousRootSearch.
Module QRD := PolynomialFormulasQuinticRadicalDecidability.
Module AR := LeanProofs.PolynomialFormulasAbelRuffini.
Module CC :=
  PolynomialFormulasLazardQuinticCoherentAlternateConcreteCompositum.
Module RCT := PolynomialFormulasLazardQuinticRootCompleteAlternateTower.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module ACT :=
  PolynomialFormulasLazardQuinticAlternateCertificateRadicalTower.
Module O := PolynomialFormulasLazardOptimality.

(** The positive-Fourier convention reverses the four nonzero coordinates.
    Recording the involutive index map once avoids repeating a five-by-five
    case split whenever distinctness of the reconstructed outputs is needed. *)
Definition lazard_quintic_fourier_reverse_index (k : 'I_5) : 'I_5 :=
  nth o0 [:: o0; o4; o3; o2; o1] (nat_of_ord k).

Lemma lazard_quintic_fourier_reverse_indexK :
  involutive lazard_quintic_fourier_reverse_index.
Proof.
case=> [[|[|[|[|[|k]]]]] hk] //=; by apply: val_inj.
Qed.

Lemma lazard_reversed_root_tupleE
    (K : fieldType) (roots : 5.-tuple K) k :
  RFR.lazard_reversed_root_tuple roots k =
    tnth roots (lazard_quintic_fourier_reverse_index k).
Proof.
case: k=> [[|[|[|[|[|k]]]]] hk] //=.
Qed.

Lemma lazard_reversed_root_tuple_injective
    (K : fieldType) (roots : 5.-tuple K)
    (hroots : injective (tnth roots)) :
  injective (RFR.lazard_reversed_root_tuple roots).
Proof.
move=> i j hij.
rewrite !lazard_reversed_root_tupleE in hij.
exact: (can_inj lazard_quintic_fourier_reverse_indexK) (hroots hij).
Qed.

(* -------------------------------------------------------------------- *)
(** * Product-denominator construction *)

Definition lazard_quintic_common_denominator (p : {poly rat}) : int :=
  \prod_(i : 'I_5) denq p`_i.

Definition lazard_quintic_denominator_complement
    (p : {poly rat}) (i : 'I_5) : int :=
  \prod_(j : 'I_5 | j != i) denq p`_j.

Definition lazard_quintic_integral_lower_coefficient
    (p : {poly rat}) (i : 'I_5) : int :=
  numq p`_i * lazard_quintic_denominator_complement p i *
    lazard_quintic_common_denominator p ^+ (4 - i).

Definition lazard_quintic_integer_data
    (p : {poly rat}) : QRF.monic_quintic :=
  [tuple lazard_quintic_integral_lower_coefficient p i | i < 5].

Definition lazard_quintic_integer_polynomial (p : {poly rat}) :
    {poly int} :=
  QRF.quintic_polynomial (lazard_quintic_integer_data p).

Definition lazard_quintic_scaled_polynomial (p : {poly rat}) :
    {poly rat} :=
  QC.rational_monic_quintic (lazard_quintic_integer_data p).

Lemma lazard_quintic_common_denominator_gt0 p :
  0 < lazard_quintic_common_denominator p.
Proof.
apply: prodr_gt0=> i _.
exact: denq_gt0.
Qed.

Lemma lazard_quintic_common_denominator_neq0 p :
  lazard_quintic_common_denominator p != 0.
Proof.
apply/prodf_neq0=> i _.
exact: denq_neq0.
Qed.

Lemma lazard_quintic_common_denominator_cast_neq0 p :
  (lazard_quintic_common_denominator p)%:~R != 0 :> rat.
Proof.
by rewrite intr_eq0 lazard_quintic_common_denominator_neq0.
Qed.

Lemma lazard_quintic_common_denominator_castE p (i : 'I_5) :
  (lazard_quintic_common_denominator p)%:~R =
    (denq p`_i)%:~R *
      (lazard_quintic_denominator_complement p i)%:~R :> rat.
Proof.
by rewrite /lazard_quintic_common_denominator
  /lazard_quintic_denominator_complement (bigD1 i) //= rmorphM.
Qed.

(** The central arithmetic identity.  Notice that no quotient in [int]
    occurs in the definition; integrality is visible syntactically. *)
Theorem lazard_quintic_integral_lower_coefficient_castE
    p (i : 'I_5) :
  (lazard_quintic_integral_lower_coefficient p i)%:~R =
    p`_i *
      (lazard_quintic_common_denominator p)%:~R ^+ (5 - i) :> rat.
Proof.
rewrite /lazard_quintic_integral_lower_coefficient
  !rmorphM rmorphXn numqE.
rewrite subSn ?leq_ord // exprS.
rewrite lazard_quintic_common_denominator_castE.
by rewrite !mulrA.
Qed.

Lemma lazard_quintic_integer_dataE p (i : 'I_5) :
  tnth (lazard_quintic_integer_data p) i =
    lazard_quintic_integral_lower_coefficient p i.
Proof. by rewrite /lazard_quintic_integer_data tnth_mktuple. Qed.

(* -------------------------------------------------------------------- *)
(** * A reusable list model of [QRF.quintic_polynomial] *)

Definition lazard_monic_tuple_polynomial
    (f : QRF.monic_quintic) : {poly int} :=
  Poly (rcons f 1).

Lemma size_lazard_monic_tuple_polynomial f :
  size (lazard_monic_tuple_polynomial f) = 6%N.
Proof.
have hlast : last 0 (rcons f 1) != 0.
  by rewrite last_rcons oner_neq0.
by rewrite /lazard_monic_tuple_polynomial (@PolyK _ 0) //
  size_rcons size_tuple.
Qed.

Lemma lazard_monic_tuple_polynomial_monic f :
  lazard_monic_tuple_polynomial f \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_lazard_monic_tuple_polynomial
  /lazard_monic_tuple_polynomial coef_Poly nth_rcons size_tuple.
by rewrite ltnn eqxx.
Qed.

Lemma lazard_monic_tuple_polynomial_coef_lower
    f (i : 'I_5) :
  (lazard_monic_tuple_polynomial f)`_i = tnth f i.
Proof.
rewrite /lazard_monic_tuple_polynomial coef_Poly nth_rcons
  size_tuple ltn_ord.
by rewrite -(tnth_nth 0).
Qed.

Lemma lazard_monic_tuple_polynomial_coef_top f :
  (lazard_monic_tuple_polynomial f)`_5 = 1.
Proof.
by rewrite /lazard_monic_tuple_polynomial coef_Poly nth_rcons
  size_tuple ltnn eqxx.
Qed.

Lemma lazard_monic_quintic_of_tuple_polynomialE f :
  QRF.monic_quintic_of_poly (lazard_monic_tuple_polynomial f) = f.
Proof.
apply: eq_from_tnth=> i.
rewrite QRF.monic_quintic_of_polyE
  lazard_monic_tuple_polynomial_coef_lower.
by [].
Qed.

Lemma lazard_quintic_polynomial_tupleE f :
  QRF.quintic_polynomial f = lazard_monic_tuple_polynomial f.
Proof.
rewrite -(lazard_monic_quintic_of_tuple_polynomialE f).
exact: QRF.quintic_polynomial_of_poly
  (size_lazard_monic_tuple_polynomial f)
  (lazard_monic_tuple_polynomial_monic f).
Qed.

Lemma lazard_quintic_scaled_polynomial_coef_lower
    p (i : 'I_5) :
  (lazard_quintic_scaled_polynomial p)`_i =
    (lazard_quintic_integral_lower_coefficient p i)%:~R.
Proof.
rewrite /lazard_quintic_scaled_polynomial
  /QC.rational_monic_quintic coef_map
  lazard_quintic_polynomial_tupleE
  lazard_monic_tuple_polynomial_coef_lower.
by rewrite lazard_quintic_integer_dataE.
Qed.

Lemma lazard_quintic_scaled_polynomial_coef_top p :
  (lazard_quintic_scaled_polynomial p)`_5 = 1.
Proof.
by rewrite /lazard_quintic_scaled_polynomial
  /QC.rational_monic_quintic coef_map
  lazard_quintic_polynomial_tupleE
  lazard_monic_tuple_polynomial_coef_top rmorph1.
Qed.

Lemma size_lazard_quintic_scaled_polynomial p :
  size (lazard_quintic_scaled_polynomial p) = 6%N.
Proof. exact: QC.size_rational_monic_quintic. Qed.

Lemma lazard_quintic_scaled_polynomial_monic p :
  lazard_quintic_scaled_polynomial p \is monic.
Proof. exact: QC.rational_monic_quintic_monic. Qed.

Section MonicRationalQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let pD := lazard_quintic_scaled_polynomial p.
Let D : rat := (lazard_quintic_common_denominator p)%:~R.

Lemma lazard_rational_quintic_leading_coefficient : p`_5 = 1.
Proof.
have := elimT monicP p_monic.
by rewrite lead_coefE p_size.
Qed.

(** Coefficient form of [pD(Y) = D^5 p(Y/D)]. *)
Theorem lazard_quintic_scaled_coefficient_identity (i : 'I_6) :
  pD`_i = p`_i * D ^+ (5 - i).
Proof.
have [hi5 | hi5] := ltnP i 5.
- pose j : 'I_5 := Ordinal hi5.
  change pD`_j = p`_j * D ^+ (5 - j).
  rewrite /pD lazard_quintic_scaled_polynomial_coef_lower.
  exact: lazard_quintic_integral_lower_coefficient_castE.
- have hi_le5 : (i <= 5)%N by exact: ltnS (valP i).
  have h5_le_i : (5 <= i)%N := hi5.
  have hi_val : (i : nat) = 5%N := anti_leq hi_le5 h5_le_i.
  have hi_ord : i = @Ordinal 6 5 isT.
    apply: val_inj.
    exact: hi_val.
  subst i.
  by rewrite /pD lazard_quintic_scaled_polynomial_coef_top
    lazard_rational_quintic_leading_coefficient subnn expr0 mulr1.
Qed.

(** Evaluation form, valid after embedding into every field extension of
    [rat].  This is stronger than merely transporting rational roots. *)
Theorem lazard_quintic_scaled_horner
    (K : fieldType) (phi : {rmorphism rat -> K}) (x : K) :
  (map_poly phi pD).[phi D * x] =
    phi D ^+ 5 * (map_poly phi p).[x].
Proof.
rewrite -[map_poly phi pD]coefK size_map_poly
  size_lazard_quintic_scaled_polynomial horner_poly.
rewrite -[map_poly phi p]coefK size_map_poly p_size horner_poly.
rewrite mulr_sumr.
apply: eq_bigr=> i _.
rewrite !coef_map lazard_quintic_scaled_coefficient_identity
  rmorphM rmorphXn exprMn.
have hi5 : (i <= 5)%N := ltnS (valP i).
have hpow : phi D ^+ (5 - i) * phi D ^+ i = phi D ^+ 5.
  by rewrite -exprD (subnK hi5).
rewrite -mulrA [phi D ^+ (5 - i) *
    (phi D ^+ i * x ^+ i)]mulrA hpow.
by rewrite mulrCA.
Qed.

Lemma lazard_quintic_scaled_root_forward
    (K : fieldType) (phi : {rmorphism rat -> K}) (x : K) :
  root (map_poly phi pD) (phi D * x) =
    root (map_poly phi p) x.
Proof.
have hD : phi D != 0.
  by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
rewrite !rootE lazard_quintic_scaled_horner.
by rewrite mulf_eq0 (negPf (expf_neq0 5 hD)) orFb.
Qed.

Lemma lazard_quintic_scaled_root_backward
    (K : fieldType) (phi : {rmorphism rat -> K}) (y : K) :
  root (map_poly phi p) ((phi D)^-1 * y) =
    root (map_poly phi pD) y.
Proof.
have hD : phi D != 0.
  by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
symmetry.
move: (lazard_quintic_scaled_root_forward
  (phi := phi) ((phi D)^-1 * y)).
by rewrite mulrA mulfV // mul1r.
Qed.

Theorem lazard_quintic_root_bijection
    (K : fieldType) (phi : {rmorphism rat -> K}) :
  (forall x : K,
    root (map_poly phi p) x =
      root (map_poly phi pD) (phi D * x)) /\
  (forall y : K,
    root (map_poly phi pD) y =
      root (map_poly phi p) ((phi D)^-1 * y)).
Proof.
split=> z.
- exact: esym (lazard_quintic_scaled_root_forward phi z).
- exact: esym (lazard_quintic_scaled_root_backward phi z).
Qed.

(* -------------------------------------------------------------------- *)
(** * Exact polynomial dilation and irreducibility *)

Definition lazard_polynomial_dilation
    (K : fieldType) (q : {poly K}) (d : K) : {poly K} :=
  d ^+ 5 *: (q \Po (d^-1 *: 'X)).

Lemma lazard_quintic_scaled_polynomial_dilationE :
  pD = lazard_polynomial_dilation p D.
Proof.
rewrite -[pD]coefK size_lazard_quintic_scaled_polynomial poly_def.
rewrite /lazard_polynomial_dilation comp_polyE p_size scaler_sumr.
apply: eq_bigr=> i _.
rewrite lazard_quintic_scaled_coefficient_identity exprZn !scalerA.
congr (_ *: 'X^i).
have hi5 : (i <= 5)%N := ltnS (valP i).
have hD : D != 0 :=
  lazard_quintic_common_denominator_cast_neq0 p.
rewrite exprB ?unitfE // exprVn.
by rewrite !mulrA mulrCA.
Qed.

Lemma irreducible_poly_eqp_iff
    (K : fieldType) (q r : {poly K}) :
  q %= r -> (irreducible_poly q <-> irreducible_poly r).
Proof.
move=> hqr; split=> [[hqsize hqirr] | [hrsize hrirr]]; split.
- by rewrite -(eqp_size hqr).
- move=> s hs1 hsdiv.
  have hsdivq : s %| q.
    by move: hsdiv; rewrite (eqp_dvdr _ hqr).
  exact: eqp_trans (hqirr s hs1 hsdivq) hqr.
- by rewrite (eqp_size hqr).
- move=> s hs1 hsdiv.
  have hsdivr : s %| r.
    by move: hsdiv; rewrite -(eqp_dvdr _ hqr).
  exact: eqp_trans (hrirr s hs1 hsdivr) (eqp_sym hqr).
Qed.

Lemma irreducible_poly_scale_iff
    (K : fieldType) (a : K) (q : {poly K}) :
  a != 0 ->
  (irreducible_poly (a *: q) <-> irreducible_poly q).
Proof.
move=> ha.
exact: irreducible_poly_eqp_iff (eqp_scale q ha).
Qed.

Lemma comp_poly_scaleX_inverse
    (K : fieldType) (q : {poly K}) (c : K) :
  c != 0 ->
  (q \Po (c *: 'X)) \Po (c^-1 *: 'X) = q.
Proof.
move=> hc.
rewrite -comp_polyA comp_polyZ comp_polyX scalerA mulfV //
  scale1r comp_polyXr.
by [].
Qed.

Lemma irreducible_of_comp_scaleX
    (K : fieldType) (q : {poly K}) (c : K) :
  c != 0 ->
  irreducible_poly (q \Po (c *: 'X)) -> irreducible_poly q.
Proof.
move=> hc [qcomp_gt1 qcomp_irred]; split.
- move: qcomp_gt1.
  have hcX : size (c *: 'X : {poly K}) = 2%N.
    by rewrite size_scale // size_polyX.
  by rewrite (size_comp_poly2 q hcX).
- move=> r r_size1 r_dvd_q.
  have rcomp_size1 : size (r \Po (c *: 'X)) != 1%N.
    have hcX : size (c *: 'X : {poly K}) = 2%N.
      by rewrite size_scale // size_polyX.
    by rewrite (size_comp_poly2 r hcX).
  have rcomp_dvd :
      r \Po (c *: 'X) %| q \Po (c *: 'X) :=
    dvdp_comp_poly _ r_dvd_q.
  have rcomp_eq := qcomp_irred _ rcomp_size1 rcomp_dvd.
  apply/andP; case/andP: rcomp_eq=> rcq qcr; split.
  + move/(dvdp_comp_poly (c^-1 *: 'X)): rcq.
    by rewrite (@comp_poly_scaleX_inverse K r c hc)
      (@comp_poly_scaleX_inverse K q c hc).
  + move/(dvdp_comp_poly (c^-1 *: 'X)): qcr.
    by rewrite (@comp_poly_scaleX_inverse K q c hc)
      (@comp_poly_scaleX_inverse K r c hc).
Qed.

Lemma irreducible_poly_comp_scaleX_iff
    (K : fieldType) (q : {poly K}) (c : K) :
  c != 0 ->
  (irreducible_poly (q \Po (c *: 'X)) <-> irreducible_poly q).
Proof.
move=> hc; split.
- exact: irreducible_of_comp_scaleX hc.
- move=> hq.
  have hcV : c^-1 != 0 by rewrite invr_eq0.
  apply: (irreducible_of_comp_scaleX hcV).
  by rewrite comp_poly_scaleX_inverse.
Qed.

Lemma irreducible_poly_dilation_iff
    (K : fieldType) (q : {poly K}) (d : K) :
  d != 0 ->
  (irreducible_poly (lazard_polynomial_dilation q d) <->
    irreducible_poly q).
Proof.
move=> hd.
rewrite /lazard_polynomial_dilation
  (irreducible_poly_scale_iff (expf_neq0 5 hd)).
have hdV : d^-1 != 0 by rewrite invr_eq0.
exact: irreducible_poly_comp_scaleX_iff hdV.
Qed.

Theorem lazard_quintic_scaled_irreducible_iff :
  irreducible_poly pD <-> irreducible_poly p.
Proof.
rewrite lazard_quintic_scaled_polynomial_dilationE.
exact: irreducible_poly_dilation_iff
  (lazard_quintic_common_denominator_cast_neq0 p).
Qed.

(* -------------------------------------------------------------------- *)
(** * Depressedness *)

Definition lazard_rational_quintic_depressed (q : {poly rat}) : Prop :=
  q`_4 = 0.

Theorem lazard_quintic_scaled_depressed_iff :
  lazard_rational_quintic_depressed pD <->
    lazard_rational_quintic_depressed p.
Proof.
rewrite /lazard_rational_quintic_depressed.
have hcoef := lazard_quintic_scaled_coefficient_identity
  (@Ordinal 6 4 isT).
change pD`_4 = p`_4 * D ^+ 1 in hcoef.
rewrite expr1 in hcoef.
rewrite hcoef; split.
- move/eqP.
  rewrite mulf_eq0
    (negPf (lazard_quintic_common_denominator_cast_neq0 p)) orbF.
  exact/eqP.
- by move=> ->; rewrite mul0r.
Qed.

End MonicRationalQuintic.

(* -------------------------------------------------------------------- *)
(** * Explicit radical-expression transport under rational dilation *)

Section RadicalFormulaScaling.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let pD := lazard_quintic_scaled_polynomial p.
Let D : rat := (lazard_quintic_common_denominator p)%:~R.

(** Multiplication by the rational dilation and its inverse are genuine
    constructors of MathComp--Abel's explicit radical-expression syntax. *)
Definition lazard_quintic_scale_algterm
    (c : rat) (t : algterm rat) : algterm rat :=
  BinOp Mul (Base c) t.

Definition lazard_quintic_inverse_scale_algterm
    (c : rat) (t : algterm rat) : algterm rat :=
  BinOp Mul (Base c^-1) t.

Lemma lazard_quintic_scale_algterm_eval c t :
  algT_eval ratrC (lazard_quintic_scale_algterm c t) =
    ratrC c * algT_eval ratrC t.
Proof. by []. Qed.

Lemma lazard_quintic_inverse_scale_algterm_eval c t :
  algT_eval ratrC (lazard_quintic_inverse_scale_algterm c t) =
    (ratrC c)^-1 * algT_eval ratrC t.
Proof. by rewrite /= fmorphV. Qed.

(** The condition is stated directly on the original polynomial, not by
    redefining it through [pD].  The proof transports each complex root and
    its explicit [algterm rat] expression along [y = D x]. *)
Theorem lazard_quintic_scaled_radical_formula_iff :
  AR.radical_formula_solves pD <-> AR.radical_formula_solves p.
Proof.
rewrite /AR.radical_formula_solves; split.
- move=> hpD x hx.
  pose y := ratrC D * x.
  have hy : y \in root (map_poly ratrC pD).
    rewrite /y.
    by rewrite (@lazard_quintic_scaled_root_forward
      p p_size p_monic algC ratrC x).
  have [t ht] := hpD y hy.
  exists (lazard_quintic_inverse_scale_algterm D t).
  rewrite lazard_quintic_inverse_scale_algterm_eval ht /y.
  have hD : ratrC D != 0.
    by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
  by rewrite mulrA mulVf // mul1r.
- move=> hp y hy.
  pose x := (ratrC D)^-1 * y.
  have hx : x \in root (map_poly ratrC p).
    rewrite /x.
    by rewrite (@lazard_quintic_scaled_root_backward
      p p_size p_monic algC ratrC y).
  have [t ht] := hp x hx.
  exists (lazard_quintic_scale_algterm D t).
  rewrite lazard_quintic_scale_algterm_eval ht /x.
  have hD : ratrC D != 0.
    by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
  by rewrite mulrA mulfV // mul1r.
Qed.

End RadicalFormulaScaling.

(* -------------------------------------------------------------------- *)
(** * Homogeneity of Lazard's theta invariant *)

Section ThetaScaling.

Variable R : comRingType.

Definition lazard_scale_quintic_roots
    (c : R) (roots : 5.-tuple R) : 5.-tuple R :=
  [tuple c * tnth roots i | i < 5].

Definition lazard_quintic_exponent_total
    (d : F20.quintic_exponent) : nat :=
  \sum_(i : 'I_5) tnth d i.

Lemma lazard_quintic_monomial_scale
    c roots (d : F20.quintic_exponent) :
  TV.quintic_monomial_value (lazard_scale_quintic_roots c roots) d =
    c ^+ lazard_quintic_exponent_total d *
      TV.quintic_monomial_value roots d.
Proof.
rewrite /TV.quintic_monomial_value /lazard_scale_quintic_roots
  /lazard_quintic_exponent_total.
under [LHS]eq_bigr=> i _ do rewrite tnth_mktuple exprMn.
by rewrite big_split prodrXr.
Qed.

Lemma lazard_quintic_exponent_total_action
    (s : F20.S5) (d : F20.quintic_exponent) :
  lazard_quintic_exponent_total (F20.act_exponent s d) =
    lazard_quintic_exponent_total d.
Proof.
rewrite /lazard_quintic_exponent_total /F20.act_exponent.
rewrite (reindex_inj (@perm_inj _ s)) /=.
apply: eq_bigr=> i _.
by rewrite tnth_mktuple permK.
Qed.

Lemma lazard_theta_exponent_table_total_four :
  all (fun d => lazard_quintic_exponent_total d == 4%N)
    F20.theta_exponent_table.
Proof.
by rewrite /F20.theta_exponent_table
  /lazard_quintic_exponent_total !big_ord_recl /=.
Qed.

Lemma lazard_theta_table_image_total_four
    (s : F20.S5) d :
  d \in F20.theta_table_image s ->
  lazard_quintic_exponent_total d = 4%N.
Proof.
move=> /mapP[e he ->].
rewrite lazard_quintic_exponent_total_action.
have /allP hall := lazard_theta_exponent_table_total_four.
move/eqP: (hall e he).
by [].
Qed.

Lemma lazard_quintic_table_value_scale_four
    c roots table
    (hall : forall d, d \in table ->
      lazard_quintic_exponent_total d = 4%N) :
  TV.quintic_table_value (lazard_scale_quintic_roots c roots) table =
    c ^+ 4 * TV.quintic_table_value roots table.
Proof.
rewrite /TV.quintic_table_value.
under [LHS]eq_bigr=> d hd do
  rewrite lazard_quintic_monomial_scale (hall d hd).
by rewrite -mulr_sumr.
Qed.

(** Lazard/Dummit's scalar theta value is homogeneous of total degree four.
    This is the exact [D^4] used to transport a rational resolvent root. *)
Theorem lazard_quintic_theta_scale_four
    c roots (i : 'I_6) :
  TV.quintic_theta_value (lazard_scale_quintic_roots c roots) i =
    c ^+ 4 * TV.quintic_theta_value roots i.
Proof.
rewrite /TV.quintic_theta_value.
apply: lazard_quintic_table_value_scale_four=> d hd.
exact: lazard_theta_table_image_total_four hd.
Qed.

End ThetaScaling.

(* -------------------------------------------------------------------- *)
(** * Rational scalar-resolvent witness transport *)

Section ResolventWitnessScaling.

Variable K : fieldType.
Variable phi : {rmorphism rat -> K}.

Lemma lazard_scale_quintic_roots_cancel
    (d : rat) (hd : d != 0) (roots : 5.-tuple K) :
  lazard_scale_quintic_roots (phi d^-1)
      (lazard_scale_quintic_roots (phi d) roots) = roots.
Proof.
apply: eq_from_tnth=> i.
rewrite !tnth_mktuple -mulrA -rmorphM mulVf // rmorph1 mul1r.
by [].
Qed.

Lemma lazard_quintic_semantic_rational_root_scale_forward
    (d : rat) (roots : 5.-tuple K) :
  QC.quintic_semantic_has_rational_root phi roots ->
  QC.quintic_semantic_has_rational_root phi
    (lazard_scale_quintic_roots (phi d) roots).
Proof.
move=> [q hq].
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff roots (phi q))) hq.
exists (d ^+ 4 * q).
apply: (proj2 (TV.quintic_scalar_resolvent_root_iff
  (lazard_scale_quintic_roots (phi d) roots)
  (phi (d ^+ 4 * q)))).
exists i.
by rewrite lazard_quintic_theta_scale_four hi rmorphM rmorphXn.
Qed.

(** A rational resolvent witness exists before scaling iff one exists after
    scaling.  The forward witness is [D^4 q]; the reverse implication uses
    the inverse dilation. *)
Theorem lazard_quintic_semantic_rational_root_scale_iff
    (d : rat) (hd : d != 0) (roots : 5.-tuple K) :
  QC.quintic_semantic_has_rational_root phi
      (lazard_scale_quintic_roots (phi d) roots) <->
    QC.quintic_semantic_has_rational_root phi roots.
Proof.
split.
- move=> hscaled.
  have hback := lazard_quintic_semantic_rational_root_scale_forward
    (phi := phi) d^-1 hscaled.
  by rewrite lazard_scale_quintic_roots_cancel in hback.
- exact: lazard_quintic_semantic_rational_root_scale_forward.
Qed.

End ResolventWitnessScaling.

(* -------------------------------------------------------------------- *)
(** * Descending a semantic witness from a common overfield *)

Section SemanticWitnessDescent.

Variables (K E : fieldType).
Variables (ratrK : {rmorphism rat -> K})
  (ratrE : {rmorphism rat -> E}).
Variable h : {rmorphism K -> E}.
Hypothesis h_rational : forall q : rat, h (ratrK q) = ratrE q.

(** No root-ordering claim is hidden here: the input tuple is mapped
    componentwise, and the conclusion follows only from injectivity of the
    field morphism and naturality of the six theta values. *)
Lemma lazard_quintic_semantic_rational_root_map_descend
    (roots : 5.-tuple K) :
  QC.quintic_semantic_has_rational_root ratrE (map_tuple h roots) ->
  QC.quintic_semantic_has_rational_root ratrK roots.
Proof.
move=> [q hq].
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff
    (map_tuple h roots) (ratrE q))) hq.
exists q.
apply: (proj2 (TV.quintic_scalar_resolvent_root_iff roots (ratrK q))).
exists i.
apply: (fmorph_inj h).
by rewrite TGB.quintic_theta_value_map hi h_rational.
Qed.

End SemanticWitnessDescent.

(* -------------------------------------------------------------------- *)
(** * From an original semantic witness to the executable integer test *)

Section ExecutableWitnessFromCommonRoots.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let f : QRF.monic_quintic := lazard_quintic_integer_data p.
Let pD : {poly rat} := lazard_quintic_scaled_polynomial p.
Let pD_size : size pD = 6%N :=
  QC.size_rational_monic_quintic f.
Let D : rat := (lazard_quintic_common_denominator p)%:~R.
Let Canonical : splittingFieldType rat := numfield pD.
Let canonical_rootsD : 5.-tuple Canonical :=
  @GA.quintic_root_tuple pD pD_size.

(** A canonical complete root tuple for the original polynomial, living in
    the splitting field already constructed for its integer dilation. *)
Definition lazard_quintic_rescaled_canonical_roots : 5.-tuple Canonical :=
  lazard_scale_quintic_roots
    ((in_alg Canonical D)^-1) canonical_rootsD.

Lemma lazard_quintic_scale_rescaled_canonical_rootsE :
  lazard_scale_quintic_roots (in_alg Canonical D)
      lazard_quintic_rescaled_canonical_roots = canonical_rootsD.
Proof.
have hD : in_alg Canonical D != 0.
  by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
apply: eq_from_tnth=> i.
rewrite /lazard_quintic_rescaled_canonical_roots !tnth_mktuple
  mulrA mulfV // mul1r.
by [].
Qed.

Lemma lazard_quintic_rescaled_canonical_roots_sound k :
  root (map_poly (in_alg Canonical) p)
    (tnth lazard_quintic_rescaled_canonical_roots k).
Proof.
rewrite /lazard_quintic_rescaled_canonical_roots tnth_mktuple.
rewrite (@lazard_quintic_scaled_root_backward
  p p_size p_monic Canonical (in_alg Canonical)
  (tnth canonical_rootsD k)).
by rewrite QC.canonical_quintic_numfield_factorization
  root_prod_XsubC mem_tnth.
Qed.

Lemma lazard_quintic_rescaled_canonical_roots_complete z :
  root (map_poly (in_alg Canonical) p) z ->
  exists k : 'I_5,
    z = tnth lazard_quintic_rescaled_canonical_roots k.
Proof.
move=> hz.
have hzD : root (map_poly (in_alg Canonical) pD)
    (in_alg Canonical D * z).
  move: (@lazard_quintic_scaled_root_forward
    p p_size p_monic Canonical (in_alg Canonical) z).
  by rewrite hz.
move: hzD.
rewrite QC.canonical_quintic_numfield_factorization root_prod_XsubC.
move=> /tnthP[k hk].
exists k.
rewrite /lazard_quintic_rescaled_canonical_roots tnth_mktuple -hk.
have hD : in_alg Canonical D != 0.
  by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
by rewrite mulrA mulVf // mul1r.
Qed.

(** A genuine arbitrary-rational solvability front end.  Its premise is the
    existing rootwise radical-expression condition on [p] itself.  The
    preceding dilation theorem transports that condition to [pD], where the
    canonical coefficient-only theorem yields the executable rational-root
    search result. *)
Theorem lazard_quintic_executable_resolvent_of_radical_formula
    (p_irr : irreducible_poly p) :
  AR.radical_formula_solves p ->
  RRS.has_rational_root (QPS.quintic_scaled_resolvent f).
Proof.
move=> hradical.
have hpDirr : irreducible_poly pD.
  exact: (proj2 (@lazard_quintic_scaled_irreducible_iff
    p p_size p_monic)) p_irr.
have hpDradical : AR.radical_formula_solves pD.
  exact: (proj2 (@lazard_quintic_scaled_radical_formula_iff
    p p_size p_monic)) hradical.
have hsearch :
    HRS.bounded_homogeneous_rootb
      (QPS.quintic_scaled_resolvent f).
  exact: introT
    (@QC.canonical_irreducible_quintic_scaled_resolvent_radicalP
      f hpDirr) hpDradical.
exact: elimT
  (HRS.homogeneous_rational_rootP
    (QPS.quintic_scaled_resolvent f)) hsearch.
Qed.

(** Equivalent Galois-theoretic spelling of the same input condition.  The
    group is the Galois group of the original [numfield p], not of [pD]. *)
Theorem lazard_quintic_executable_resolvent_of_galois_solvable
    (p_irr : irreducible_poly p) :
  solvable 'Gal({:numfield p} / 1%AS) ->
  RRS.has_rational_root (QPS.quintic_scaled_resolvent f).
Proof.
move=> hsolvable.
apply: lazard_quintic_executable_resolvent_of_radical_formula p_irr.
exact: elimT (QRD.quintic_every_root_has_radical_expressionP p_size)
  hsolvable.
Qed.

(** The same bridge stated at the semantic scalar-resolvent layer requested
    by the formula construction.  The witness first lives on the canonical
    roots of [pD] and is then transported back to the already proved complete
    tuple [D^-1 * canonical_rootsD]. *)
Theorem
    lazard_quintic_rescaled_canonical_semantic_witness_of_radical_formula
    (p_irr : irreducible_poly p) :
  AR.radical_formula_solves p ->
  QC.quintic_semantic_has_rational_root (in_alg Canonical)
    lazard_quintic_rescaled_canonical_roots.
Proof.
move=> hradical.
have hpDirr : irreducible_poly pD.
  exact: (proj2 (@lazard_quintic_scaled_irreducible_iff
    p p_size p_monic)) p_irr.
have hq : RRS.has_rational_root (QPS.quintic_scaled_resolvent f).
  exact: lazard_quintic_executable_resolvent_of_radical_formula
    p_irr hradical.
have hcanonical :
    QC.quintic_semantic_has_rational_root (in_alg Canonical)
      canonical_rootsD.
  exact: (proj1 (@QC.quintic_scaled_resolvent_has_rational_root_correct
    Canonical (in_alg Canonical) canonical_rootsD f
    QC.canonical_quintic_padded_vieta
    (QC.canonical_quintic_resolvent_scale_nonzero hpDirr))) hq.
have hscaled :
    QC.quintic_semantic_has_rational_root (in_alg Canonical)
      (lazard_scale_quintic_roots (in_alg Canonical D)
        lazard_quintic_rescaled_canonical_roots).
  by rewrite lazard_quintic_scale_rescaled_canonical_rootsE.
exact: (proj1 (@lazard_quintic_semantic_rational_root_scale_iff
  Canonical (in_alg Canonical) D
  (lazard_quintic_common_denominator_cast_neq0 p)
  lazard_quintic_rescaled_canonical_roots)) hscaled.
Qed.

Theorem
    lazard_quintic_rescaled_canonical_semantic_witness_of_galois_solvable
    (p_irr : irreducible_poly p) :
  solvable 'Gal({:numfield p} / 1%AS) ->
  QC.quintic_semantic_has_rational_root (in_alg Canonical)
    lazard_quintic_rescaled_canonical_roots.
Proof.
move=> hsolvable.
apply: lazard_quintic_rescaled_canonical_semantic_witness_of_radical_formula
  p_irr.
exact: elimT (QRD.quintic_every_root_has_radical_expressionP p_size)
  hsolvable.
Qed.

(** Preferred executable bridge: no cross-splitting-field identification is
    assumed.  The semantic witness is stated on the concrete complete tuple
    just constructed for [p]. *)
Theorem
    lazard_quintic_executable_resolvent_of_rescaled_canonical_semantic_witness
    (p_irr : irreducible_poly p) :
  QC.quintic_semantic_has_rational_root (in_alg Canonical)
      lazard_quintic_rescaled_canonical_roots ->
  RRS.has_rational_root (QPS.quintic_scaled_resolvent f).
Proof.
move=> horiginal.
have hpDirr : irreducible_poly pD.
  exact: (proj2 (@lazard_quintic_scaled_irreducible_iff
    p p_size p_monic)) p_irr.
have hcanonical :
    QC.quintic_semantic_has_rational_root (in_alg Canonical)
      canonical_rootsD.
  have hscaled :=
    lazard_quintic_semantic_rational_root_scale_forward
      D horiginal.
  by rewrite lazard_quintic_scale_rescaled_canonical_rootsE in hscaled.
exact: (proj2 (@QC.quintic_scaled_resolvent_has_rational_root_correct
  Canonical (in_alg Canonical) canonical_rootsD f
  QC.canonical_quintic_padded_vieta
  (QC.canonical_quintic_resolvent_scale_nonzero hpDirr))) hcanonical.
Qed.

Variable W : fieldExtType rat.
Variable h : 'AHom(Canonical, W).
Variable original_roots : 5.-tuple W.
Variable root_permutation : F20.S5.

(** This equality is the one genuinely non-canonical interface datum.  It
    explicitly says, up to the displayed permutation, that the image of
    the canonical roots of [pD] is obtained by multiplying the supplied
    roots of [p] by [D].  It is intentionally a theorem hypothesis, not an
    opaque "root-equivalence certificate" record. *)
Hypothesis canonical_scaled_rootsE :
  map_tuple h canonical_rootsD =
    TV.permute_quintic_roots root_permutation
      (lazard_scale_quintic_roots (in_alg W D) original_roots).

(** The [D^4] theta transport, the explicit common-field root equality,
    and the canonical Vieta theorem together turn a semantic rational root
    for the original root tuple into the Boolean/executable premise used by
    the integer common-compositum theorem. *)
Theorem lazard_quintic_executable_resolvent_of_semantic_witness
    (p_irr : irreducible_poly p) :
  QC.quintic_semantic_has_rational_root (in_alg W) original_roots ->
  RRS.has_rational_root (QPS.quintic_scaled_resolvent f).
Proof.
move=> horiginal.
have hpDirr : irreducible_poly pD.
  exact: (proj2 (@lazard_quintic_scaled_irreducible_iff
    p p_size p_monic)) p_irr.
have hscaled :
    QC.quintic_semantic_has_rational_root (in_alg W)
      (lazard_scale_quintic_roots (in_alg W D) original_roots).
  exact: lazard_quintic_semantic_rational_root_scale_forward
    D horiginal.
have hpermuted :
    QC.quintic_semantic_has_rational_root (in_alg W)
      (TV.permute_quintic_roots root_permutation
        (lazard_scale_quintic_roots (in_alg W D) original_roots)).
  case: hscaled=> q hq; exists q.
  by rewrite TV.quintic_scalar_resolvent_permute.
have hmapped :
    QC.quintic_semantic_has_rational_root (in_alg W)
      (map_tuple h canonical_rootsD).
  rewrite canonical_scaled_rootsE.
  exact: hpermuted.
have h_rational q :
    h (in_alg Canonical q) = in_alg W q.
  by rewrite !in_algE !alg_num_field (fmorph_eq_rat h).
have hcanonical :
    QC.quintic_semantic_has_rational_root (in_alg Canonical)
      canonical_rootsD.
  exact: (@lazard_quintic_semantic_rational_root_map_descend
    Canonical W (in_alg Canonical) (in_alg W) h h_rational
    canonical_rootsD hmapped).
exact: (proj2 (@QC.quintic_scaled_resolvent_has_rational_root_correct
  Canonical (in_alg Canonical) canonical_rootsD f
  QC.canonical_quintic_padded_vieta
  (QC.canonical_quintic_resolvent_scale_nonzero hpDirr))) hcanonical.
Qed.

End ExecutableWitnessFromCommonRoots.

(* -------------------------------------------------------------------- *)
(** * Divide the integer-pipeline output by [D] *)

Section OutputTransport.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let pD := lazard_quintic_scaled_polynomial p.
Let D : rat := (lazard_quintic_common_denominator p)%:~R.

Variable K : fieldType.
Variable phi : {rmorphism rat -> K}.

Definition lazard_quintic_rescaled_output
    (output : 'I_5 -> K) (k : 'I_5) : K :=
  (phi D)^-1 * output k.

Lemma lazard_quintic_rescaled_output_mem
    (S : {subfield K}) (output : 'I_5 -> K)
    (hD : phi D \in S)
    (houtput : forall k, output k \in S) k :
  lazard_quintic_rescaled_output output k \in S.
Proof.
by rewrite /lazard_quintic_rescaled_output rpredM ?rpredV.
Qed.

(** Division by the nonzero rational denominator preserves the five-way
    distinctness supplied by the root-origin common-compositum theorem. *)
Lemma lazard_quintic_rescaled_output_injective
    (output : 'I_5 -> K) (houtput : injective output) :
  injective (lazard_quintic_rescaled_output output).
Proof.
move=> i j hij.
apply: houtput.
have hDinv : (phi D)^-1 != 0.
  by rewrite invr_eq0 fmorph_eq0
    lazard_quintic_common_denominator_cast_neq0.
exact: (mulfI hDinv) hij.
Qed.

(** Soundness: every root returned for the integral dilation becomes a root
    of the original rational quintic after division by [D]. *)
Theorem lazard_quintic_rescaled_output_sound
    (output : 'I_5 -> K)
    (hsound : forall k,
      root (map_poly phi pD) (output k)) k :
  root (map_poly phi p) (lazard_quintic_rescaled_output output k).
Proof.
rewrite /lazard_quintic_rescaled_output.
rewrite (@lazard_quintic_scaled_root_backward
  p p_size p_monic K phi (output k)).
exact: hsound k.
Qed.

(** Completeness: if the integral pipeline lists every root of [pD], the
    divided output lists every root of [p]. *)
Theorem lazard_quintic_rescaled_output_complete
    (output : 'I_5 -> K)
    (hcomplete : forall y : K,
      root (map_poly phi pD) y -> exists k, y = output k)
    (x : K) :
  root (map_poly phi p) x ->
  exists k, x = lazard_quintic_rescaled_output output k.
Proof.
move=> hx.
have hxD : root (map_poly phi pD) (phi D * x).
  move: (@lazard_quintic_scaled_root_forward
    p p_size p_monic K phi x).
  by rewrite hx.
have [k hk] := hcomplete _ hxD.
exists k; rewrite /lazard_quintic_rescaled_output -hk.
have hD : phi D != 0.
  by rewrite fmorph_eq0 lazard_quintic_common_denominator_cast_neq0.
by rewrite mulrA mulVf // mul1r.
Qed.

Theorem lazard_quintic_rescaled_output_correct
    (output : 'I_5 -> K)
    (hsound : forall k,
      root (map_poly phi pD) (output k))
    (hcomplete : forall y : K,
      root (map_poly phi pD) y -> exists k, y = output k) :
  (forall k,
    root (map_poly phi p) (lazard_quintic_rescaled_output output k)) /\
  (forall x : K,
    root (map_poly phi p) x ->
      exists k, x = lazard_quintic_rescaled_output output k).
Proof.
split.
- exact: lazard_quintic_rescaled_output_sound hsound.
- exact: lazard_quintic_rescaled_output_complete hcomplete.
Qed.

End OutputTransport.

(* -------------------------------------------------------------------- *)
(** * Composition with the concrete common-compositum theorem *)

Section ConcreteCommonCompositumAdapter.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let f : QRF.monic_quintic := lazard_quintic_integer_data p.
Let pD : {poly rat} := lazard_quintic_scaled_polynomial p.
Let pD_size : size pD = 6%N :=
  QC.size_rational_monic_quintic f.
Let D : rat := (lazard_quintic_common_denominator p)%:~R.

Let Ambient : splittingFieldType rat :=
  CC.lazard_quintic_cyclotomic_ambient pD.
Let Canonical : splittingFieldType rat := numfield pD.
Let FullField : fieldExtType rat :=
  subvs_of ({:Ambient} : {subfield Ambient}).
Let canonical_rootsD : 5.-tuple Canonical :=
  @GA.quintic_root_tuple pD pD_size.
Let canonical_original_roots : 5.-tuple Canonical :=
  lazard_scale_quintic_roots
    ((in_alg Canonical D)^-1) canonical_rootsD.

Definition lazard_rational_common_alternate_field
    (h : 'AHom(Canonical, FullField)) (omega : FullField)
    (i : 'I_6) : {subfield FullField} :=
  @CC.lazard_common_alternate_field f h omega i.

Definition lazard_rational_common_alternate_output
    (h : 'AHom(Canonical, FullField)) (omega : FullField)
    (i : 'I_6) (k : 'I_5) : FullField :=
  (in_alg FullField D)^-1 *
    @CC.lazard_common_alternate_output f h omega i k.

(** The coefficient definition of depressedness is exactly the executable
    canonical premise required by the integer theorem. *)
Lemma lazard_quintic_integer_data_canonical_depressed :
  lazard_rational_quintic_depressed p ->
  @CE.lazard_canonical_quintic_depressed f.
Proof.
move=> hpdepressed.
have hpDdepressed :
    lazard_rational_quintic_depressed pD.
  exact: (proj2 (@lazard_quintic_scaled_depressed_iff
    p p_size p_monic)) hpdepressed.
have hpD4 : pD`_4 = 0 := hpDdepressed.
have hf4cast :
    ((tnth f (@Ordinal 5 4 isT))%:~R : rat) = 0.
  rewrite /f lazard_quintic_integer_dataE.
  rewrite -lazard_quintic_scaled_polynomial_coef_lower.
  exact: hpD4.
have hf4 : tnth f (@Ordinal 5 4 isT) = 0.
  apply/eqP.
  move/eqP: hf4cast.
  by rewrite intr_eq0.
rewrite /CE.lazard_canonical_quintic_depressed
  /SCV.monic_elementary_values tnth_mktuple.
rewrite (QRF.quintic_sextic_embedding_nthE
  f (i := 5%N) isT) /=.
by rewrite -(tnth_nth 0) hf4 oppr0.
Qed.

Lemma lazard_rational_common_bottom_mem
    (h : 'AHom(Canonical, FullField)) (omega : FullField)
    (i : 'I_6) (q : rat) :
  in_alg FullField q \in
    lazard_rational_common_alternate_field h omega i.
Proof.
have hqbot : in_alg FullField q \in
    (1%AS : {subfield FullField}).
  apply/vlineP; exists q.
  by rewrite in_algE.
rewrite /lazard_rational_common_alternate_field
  /CC.lazard_common_alternate_field
  /RCT.lazard_root_complete_alternate_field
  /RCT.lazard_root_complete_alternate_square_field.
apply: subvP_adjoin.
apply: ACT.lazard_four_fifth_base_mem_generated.
exact: ACT.lazard_three_square_base_mem_third hqbot.
Qed.

Definition lazard_rational_common_compositum_output_package : Prop :=
  exists (h : 'AHom(Canonical, FullField))
      (omega : FullField) (q : rat) (i : 'I_6),
    5.-primitive_root omega /\
    @O.radical_extension rat FullField
      (1%AS : {subfield FullField})
      (lazard_rational_common_alternate_field h omega i) /\
    (forall k : 'I_5,
      lazard_rational_common_alternate_output h omega i k \in
        lazard_rational_common_alternate_field h omega i) /\
    injective (lazard_rational_common_alternate_output h omega i) /\
    (forall k : 'I_5,
      root (map_poly (in_alg FullField) p)
        (lazard_rational_common_alternate_output h omega i k)) /\
    (forall z : FullField,
      root (map_poly (in_alg FullField) p) z ->
      exists k : 'I_5,
        z = lazard_rational_common_alternate_output h omega i k).

(** Focused arbitrary-rational front end for the concrete theorem.

    The hypotheses are now stated on [p], except for [hq], which is the
    executable rational-root certificate for the integer dilation [f].
    The conclusion deliberately retains only the pieces changed or needed
    by scaling: the same radical field, membership of the divided outputs,
    distinctness, and root soundness/completeness for the original rational
    polynomial.
    The large theta/order/reconstruction package remains available from the
    theorem consumed in the proof and is not duplicated here. *)
Theorem
    exists_lazard_rational_common_compositum_coherent_alternate_radical_tower
    (p_irr : irreducible_poly p)
    (p_depressed : lazard_rational_quintic_depressed p)
    (hq : RRS.has_rational_root (QPS.quintic_scaled_resolvent f)) :
  lazard_rational_common_compositum_output_package.
Proof.
rewrite /lazard_rational_common_compositum_output_package.
have hpDirr : irreducible_poly pD.
  exact: (proj2 (@lazard_quintic_scaled_irreducible_iff
    p p_size p_monic)) p_irr.
have hfdepressed : @CE.lazard_canonical_quintic_depressed f :=
  lazard_quintic_integer_data_canonical_depressed p_depressed.
have [h [omega [q [i
    [homega [_ [hselected_injective
      [hradical [hmem [hreconstruct [hsound hcomplete]]]]]]]]]]]] :=
  @CC.exists_lazard_common_compositum_coherent_alternate_radical_tower
    f hpDirr hfdepressed hq.
have hDfield : in_alg FullField D \in
    lazard_rational_common_alternate_field h omega i :=
  lazard_rational_common_bottom_mem h omega i D.
have hmem_scaled : forall k : 'I_5,
    lazard_rational_common_alternate_output h omega i k \in
      lazard_rational_common_alternate_field h omega i.
  move=> k.
  rewrite /lazard_rational_common_alternate_output.
  exact: rpredM (rpredV hDfield) (hmem k).
have hunscaled_injective :
    injective (fun k : 'I_5 =>
      @CC.lazard_common_alternate_output f h omega i k).
  move=> j k hjk.
  rewrite !hreconstruct in hjk.
  exact: lazard_reversed_root_tuple_injective
    hselected_injective hjk.
have hscaled_injective :
    injective (lazard_rational_common_alternate_output h omega i).
  exact: (@lazard_quintic_rescaled_output_injective
    p p_size p_monic FullField (in_alg FullField)
    (fun k => @CC.lazard_common_alternate_output f h omega i k)
    hunscaled_injective).
have hsound_scaled : forall k : 'I_5,
    root (map_poly (in_alg FullField) p)
      (lazard_rational_common_alternate_output h omega i k).
  move=> k.
  rewrite /lazard_rational_common_alternate_output.
  exact: (@lazard_quintic_rescaled_output_sound
    p p_size p_monic FullField (in_alg FullField)
    (fun j => @CC.lazard_common_alternate_output f h omega i j)
    hsound k).
have hcomplete_scaled : forall z : FullField,
    root (map_poly (in_alg FullField) p) z ->
    exists k : 'I_5,
      z = lazard_rational_common_alternate_output h omega i k.
  move=> z hz.
  rewrite /lazard_rational_common_alternate_output.
  exact: (@lazard_quintic_rescaled_output_complete
    p p_size p_monic FullField (in_alg FullField)
    (fun j => @CC.lazard_common_alternate_output f h omega i j)
    hcomplete z hz).
exists h, omega, q, i.
repeat split.
- exact: homega.
- exact: hradical.
- exact: hmem_scaled.
- exact: hscaled_injective.
- exact: hsound_scaled.
- exact: hcomplete_scaled.
Qed.

(** Fully composed arbitrary-rational entry point.  Solvability is the
    existing explicit radical-expression property of the original [p]; no
    predicate is redefined through the integer dilation, and no equality of
    root tuples in unrelated splitting fields is assumed. *)
Theorem exists_lazard_rational_common_compositum_of_radical_formula
    (p_irr : irreducible_poly p)
    (p_depressed : lazard_rational_quintic_depressed p)
    (p_radical : AR.radical_formula_solves p) :
  lazard_rational_common_compositum_output_package.
Proof.
apply: exists_lazard_rational_common_compositum_coherent_alternate_radical_tower
  p_irr p_depressed.
exact: (@lazard_quintic_executable_resolvent_of_radical_formula
  p p_size p_monic p_irr p_radical).
Qed.

(** Equivalent entry point using solvability of the actual Galois group of
    [p]. *)
Theorem exists_lazard_rational_common_compositum_of_galois_solvable
    (p_irr : irreducible_poly p)
    (p_depressed : lazard_rational_quintic_depressed p)
    (p_solvable : solvable 'Gal({:numfield p} / 1%AS)) :
  lazard_rational_common_compositum_output_package.
Proof.
apply: exists_lazard_rational_common_compositum_coherent_alternate_radical_tower
  p_irr p_depressed.
exact: (@lazard_quintic_executable_resolvent_of_galois_solvable
  p p_size p_monic p_irr p_solvable).
Qed.

(** Preferred fully composed semantic-witness entry point.  Its tuple is
    definitionally [D^-1] times the canonical roots of [pD]; the preceding
    bridge proves separately that this is a sound and complete root tuple
    for [p].  No cross-splitting-field equality is assumed. *)
Theorem
    exists_lazard_rational_common_compositum_of_semantic_witness
    (p_irr : irreducible_poly p)
    (p_depressed : lazard_rational_quintic_depressed p)
    (hsemantic : QC.quintic_semantic_has_rational_root
      (in_alg Canonical) canonical_original_roots) :
  lazard_rational_common_compositum_output_package.
Proof.
apply: exists_lazard_rational_common_compositum_coherent_alternate_radical_tower
  p_irr p_depressed.
exact:
  (@lazard_quintic_executable_resolvent_of_rescaled_canonical_semantic_witness
    p p_size p_monic p_irr hsemantic).
Qed.

(** More general common-overfield variant.  Unlike the preferred theorem,
    this version exposes the exact root identification it needs, including
    the permutation; the equality is not hidden in a certificate record. *)
Theorem
    exists_lazard_rational_common_compositum_of_explicit_root_identification
    (p_irr : irreducible_poly p)
    (p_depressed : lazard_rational_quintic_depressed p)
    (W : fieldExtType rat)
    (hW : 'AHom(Canonical, W))
    (original_roots : 5.-tuple W)
    (root_permutation : F20.S5)
    (canonical_scaled_rootsE :
      map_tuple hW canonical_rootsD =
        TV.permute_quintic_roots root_permutation
          (lazard_scale_quintic_roots (in_alg W D) original_roots))
    (hsemantic : QC.quintic_semantic_has_rational_root
      (in_alg W) original_roots) :
  lazard_rational_common_compositum_output_package.
Proof.
apply: exists_lazard_rational_common_compositum_coherent_alternate_radical_tower
  p_irr p_depressed.
exact: (@lazard_quintic_executable_resolvent_of_semantic_witness
  p p_size p_monic W hW original_roots root_permutation
  canonical_scaled_rootsE p_irr hsemantic).
Qed.

End ConcreteCommonCompositumAdapter.

End PolynomialFormulasLazardQuinticRationalScalingAdapter.
