(** PAUSED DRAFT CHECKPOINT (not registered in the committed Coq manifests).

    This coefficientwise numerator development has not yet been kernel
    checked and depends on the unfinished Molien-coefficient draft. *)
From Stdlib Require Import Lia Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticF20Molien LazardInvariantMolienCoefficients.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A finite formal-series step in the Section-6 Molien calculation.

    [LazardInvariantMolienCoefficients] identifies every finite Reynolds-rank
    coefficient with the corresponding weighted-assignment count for the
    four geometric class terms.
    A separate rational-function calculation simplifies their class sum.
    The two facts do not by themselves say that the coefficient sequence has
    Lazard's numerator.  This file supplies that statement without an
    analytic power-series library: for each requested coefficient [d] it
    uses finite geometric polynomials truncated at [d].  A further bridge is
    still required to identify the finite row spaces with an encoded
    polynomial invariant space. *)
Module PolynomialFormulasLazardInvariantMolienNumeratorSeries.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Module MQ := PolynomialFormulasLazardQuinticF20Molien.
Module MC := PolynomialFormulasLazardInvariantMolienCoefficients.

Local Notation Poly := {poly rat}.

(** * Finite geometric products *)

Definition finite_geometric_factor (w d : nat) : Poly :=
  \sum_(q < d.+1) ('X : Poly) ^+ (w * q).

Definition weighted_geometric_truncation n
    (w : n.-tuple nat) (d : nat) : Poly :=
  \prod_(i < n) finite_geometric_factor (tnth w i) d.

Definition weighted_denominator_poly n (w : n.-tuple nat) : Poly :=
  \prod_(i < n) (1 - ('X : Poly) ^+ (tnth w i)).

Definition bounded_weighted_assignment n (w : n.-tuple nat)
    (bound degree : nat) :=
  {q : n.-tuple 'I_bound.+1 | MC.weighted_total w q == degree}.

Lemma finfun_of_tuple_bijective (T : finType) n :
  @bijective (n.-tuple T) (T ^ n) finfun_of_tuple.
Proof.
exists tuple_of_finfun; split.
- exact: finfun_of_tupleK.
- exact: tuple_of_finfunK.
Qed.

Lemma weighted_geometric_truncationE n (w : n.-tuple nat) d :
  weighted_geometric_truncation w d =
    \sum_(q : n.-tuple 'I_d.+1)
      ('X : Poly) ^+ (MC.weighted_total w q).
Proof.
rewrite /weighted_geometric_truncation /finite_geometric_factor.
rewrite bigA_distr_bigA.
rewrite (reindex (@finfun_of_tuple 'I_d.+1 n)
  (onW_bij predT (finfun_of_tuple_bijective 'I_d.+1 n))) /=.
apply: eq_bigr => q _.
rewrite -expr_sum /MC.weighted_total.
apply: eq_bigr => i _.
by rewrite ffunE.
Qed.

Lemma weighted_geometric_truncation_bounded_coefficient n
    (w : n.-tuple nat) d k :
  (weighted_geometric_truncation w d)`_k =
    (#|bounded_weighted_assignment w d k|%:R : rat).
Proof.
rewrite weighted_geometric_truncationE coef_sum
  /bounded_weighted_assignment card_sub -sum1_card natr_sum
  [RHS]big_mkcond.
apply: eq_bigr => q _.
rewrite coefXn eq_sym.
by case: (MC.weighted_total w q == k).
Qed.

Lemma weighted_coordinate_le_total n bound (w : n.-tuple nat)
    (hpos : forall i, 0 < tnth w i)
    (q : n.-tuple 'I_bound.+1) i :
  (tnth q i : nat) <= MC.weighted_total w q.
Proof.
apply: leq_trans
  (@leq_pmull (tnth q i : nat) (tnth w i) (hpos i)) _.
rewrite /MC.weighted_total (bigD1 i) //=.
exact: leq_addr.
Qed.

Definition widen_weighted_tuple n (w : n.-tuple nat) k d
    (hkd : k <= d) (q : n.-tuple 'I_k.+1) :
    n.-tuple 'I_d.+1 :=
  [tuple widen_ord (by rewrite leqSS) (tnth q i) | i < n].

Lemma weighted_total_widen n (w : n.-tuple nat) k d
    (hkd : k <= d) (q : n.-tuple 'I_k.+1) :
  MC.weighted_total w (widen_weighted_tuple w hkd q) =
    MC.weighted_total w q.
Proof.
rewrite /MC.weighted_total.
apply: eq_bigr => i _.
by rewrite /widen_weighted_tuple tnth_mktuple.
Qed.

Definition narrow_weighted_tuple n (w : n.-tuple nat)
    (hpos : forall i, 0 < tnth w i) bound k
    (q : n.-tuple 'I_bound.+1)
    (hq : MC.weighted_total w q = k) : n.-tuple 'I_k.+1 :=
  [tuple @Ordinal k.+1 (tnth q i)
    (leq_ltn_trans (weighted_coordinate_le_total hpos q i)
      (by rewrite hq)) | i < n].

Lemma weighted_total_narrow n (w : n.-tuple nat)
    (hpos : forall i, 0 < tnth w i) bound k
    (q : n.-tuple 'I_bound.+1)
    (hq : MC.weighted_total w q = k) :
  MC.weighted_total w (narrow_weighted_tuple hpos hq) =
    MC.weighted_total w q.
Proof.
rewrite /MC.weighted_total.
apply: eq_bigr => i _.
by rewrite /narrow_weighted_tuple tnth_mktuple.
Qed.

Definition widen_weighted_assignment n (w : n.-tuple nat) k d
    (hkd : k <= d) (q : MC.weighted_assignment w k) :
    bounded_weighted_assignment w d k.
Proof.
refine (Sub (widen_weighted_tuple w hkd (val q)) _).
by rewrite weighted_total_widen; exact: valP q.
Defined.

Definition narrow_weighted_assignment n (w : n.-tuple nat)
    (hpos : forall i, 0 < tnth w i) d k
    (q : bounded_weighted_assignment w d k) :
    MC.weighted_assignment w k.
Proof.
refine (Sub (narrow_weighted_tuple hpos (eqP (valP q))) _).
by rewrite weighted_total_narrow; exact: valP q.
Defined.

Lemma widen_narrow_weighted_assignmentK n (w : n.-tuple nat)
    (hpos : forall i, 0 < tnth w i) d k (hkd : k <= d) :
  cancel (widen_weighted_assignment w hkd)
    (narrow_weighted_assignment w hpos (d := d)).
Proof.
move=> q; apply/val_inj/eq_from_tnth => i.
apply/val_inj.
by rewrite /widen_weighted_assignment /narrow_weighted_assignment
  /widen_weighted_tuple /narrow_weighted_tuple !tnth_mktuple.
Qed.

Lemma narrow_widen_weighted_assignmentK n (w : n.-tuple nat)
    (hpos : forall i, 0 < tnth w i) d k (hkd : k <= d) :
  cancel (narrow_weighted_assignment w hpos (d := d))
    (widen_weighted_assignment w hkd).
Proof.
move=> q; apply/val_inj/eq_from_tnth => i.
apply/val_inj.
by rewrite /widen_weighted_assignment /narrow_weighted_assignment
  /widen_weighted_tuple /narrow_weighted_tuple !tnth_mktuple.
Qed.

Lemma weighted_geometric_truncation_coefficient n
    (w : n.-tuple nat) (hpos : forall i, 0 < tnth w i)
    d k (hkd : k <= d) :
  (weighted_geometric_truncation w d)`_k =
    MC.weighted_geometric_coefficient w k.
Proof.
rewrite weighted_geometric_truncation_bounded_coefficient
  /MC.weighted_geometric_coefficient.
congr (_%:R : rat).
symmetry.
apply: bij_eq_card.
exact: (Bijective (widen_weighted_assignment w hkd)
  (widen_narrow_weighted_assignmentK hpos hkd)
  (narrow_widen_weighted_assignmentK hpos hkd)).
Qed.

(** * Cancellation below the truncation bound *)

Lemma finite_geometric_factor_cancellation w d :
  (1 - ('X : Poly) ^+ w) * finite_geometric_factor w d =
    1 - ('X : Poly) ^+ (w * d.+1).
Proof.
rewrite /finite_geometric_factor.
under eq_bigr => i _ do rewrite exprM.
rewrite -[1 - ('X : Poly) ^+ w]opprB mulNr -subrX1 opprB.
by rewrite -exprM.
Qed.

Definition agrees_with_one_through (p : Poly) (d : nat) : Prop :=
  forall k, k <= d -> p`_k = (k == 0%N)%:R.

Lemma agrees_with_one_through_one d :
  agrees_with_one_through (1 : Poly) d.
Proof. by move=> k _; rewrite coefC. Qed.

Lemma agrees_with_one_through_mul p q d :
  agrees_with_one_through p d ->
  agrees_with_one_through q d ->
  agrees_with_one_through (p * q) d.
Proof.
move=> hp hq k hkd; rewrite coefM.
case: k hkd => [|k] hkd.
- by rewrite big_ord1 subn0 hp // hq //= eqxx mul1r.
- apply: big1 => i _.
  case: i => [[|i] hi] /=.
  + rewrite hp ?hq //= ?subn0 ?mul1r.
    exact: leq_trans (leq0n _) hkd.
  + rewrite hp ?mul0r //.
    exact: leq_trans (ltnW hi) hkd.
Qed.

Lemma agrees_with_one_through_prod n (F : 'I_n -> Poly) d
    (hF : forall i, agrees_with_one_through (F i) d) :
  agrees_with_one_through (\prod_(i < n) F i) d.
Proof.
elim/big_ind: _ => [|p q hp hq|i _].
- exact: agrees_with_one_through_one.
- exact: agrees_with_one_through_mul hp hq.
- exact: hF i.
Qed.

Lemma high_geometric_factor_agrees_with_one w d
    (hw : 0 < w) :
  agrees_with_one_through
    (1 - ('X : Poly) ^+ (w * d.+1)) d.
Proof.
move=> k hkd.
have hdw : d < w * d.+1 :=
  ltn_leq_trans (ltnSn d) (@leq_pmull d.+1 w hw).
have hkw : k < w * d.+1 := leq_ltn_trans hkd hdw.
by rewrite coefB coefC coefXn (ltn_eqF hkw).
Qed.

Lemma weighted_denominator_mul_truncation n (w : n.-tuple nat) d :
  weighted_denominator_poly w * weighted_geometric_truncation w d =
    \prod_(i < n) (1 - ('X : Poly) ^+ (tnth w i * d.+1)).
Proof.
rewrite /weighted_denominator_poly /weighted_geometric_truncation
  -big_split /=.
apply: eq_bigr => i _.
exact: finite_geometric_factor_cancellation.
Qed.

Lemma weighted_denominator_mul_truncation_agrees n
    (w : n.-tuple nat) (hpos : forall i, 0 < tnth w i) d :
  agrees_with_one_through
    (weighted_denominator_poly w * weighted_geometric_truncation w d) d.
Proof.
rewrite weighted_denominator_mul_truncation.
apply: agrees_with_one_through_prod => i.
exact: high_geometric_factor_agrees_with_one (hpos i).
Qed.

Lemma coef_mul_agrees_with_one p u d :
  agrees_with_one_through u d -> (p * u)`_d = p`_d.
Proof.
move=> hu; rewrite coefMr (bigD1 ord0) //= subn0.
rewrite hu // eqxx mulr1.
rewrite big1 ?addr0 // => i hi.
case: i hi => [[|i] hi] //= _.
rewrite hu ?mulr0 //.
exact: ltnW hi.
Qed.

Definition polynomial_series_action
    (p : Poly) (a : MC.rational_series) (d : nat) : rat :=
  \sum_(j < d.+1) p`_j * a (d - j).

Theorem weighted_geometric_denominator_series n
    (w : n.-tuple nat) (hpos : forall i, 0 < tnth w i) d :
  polynomial_series_action (weighted_denominator_poly w)
      (MC.weighted_geometric_coefficient w) d =
    (d == 0%N)%:R.
Proof.
rewrite /polynomial_series_action.
transitivity
  ((weighted_denominator_poly w *
      weighted_geometric_truncation w d)`_d).
- rewrite coefM.
  apply: eq_bigr => j _.
  congr (_ * _).
  exact: weighted_geometric_truncation_coefficient hpos (leq_subr d j).
- exact: weighted_denominator_mul_truncation_agrees hpos d (leqnn d).
Qed.

Theorem polynomial_action_weighted_geometric_of_factorization n
    (w : n.-tuple nat) (hpos : forall i, 0 < tnth w i)
    (S Q : Poly)
    (hfactor : S = Q * weighted_denominator_poly w) d :
  polynomial_series_action S (MC.weighted_geometric_coefficient w) d =
    Q`_d.
Proof.
rewrite /polynomial_series_action.
transitivity (S * weighted_geometric_truncation w d)`_d.
- rewrite coefM.
  apply: eq_bigr => j _.
  congr (_ * _).
  exact: weighted_geometric_truncation_coefficient hpos (leq_subr d j).
- rewrite hfactor -mulrA.
  apply: coef_mul_agrees_with_one.
  exact: weighted_denominator_mul_truncation_agrees hpos d.
Qed.

(** * The four F20 denominator quotients *)

(** These are the same expressions as the field-generic definitions in
    [MQ], stated directly in the polynomial ring.  The polynomial ring is
    only a ring, so it cannot instantiate [MQ]'s [fieldType] parameter. *)
Definition f20_symmetric_denominator_poly : Poly :=
  (1 - 'X) * (1 - 'X ^+ 2) * (1 - 'X ^+ 3) *
    (1 - 'X ^+ 4) * (1 - 'X ^+ 5).

Definition f20_molien_numerator_poly : Poly :=
  1 + 'X ^+ 4 + 'X ^+ 5 + 'X ^+ 6 + 'X ^+ 7 + 'X ^+ 8.

Definition identity_denominator_complement : Poly :=
  (1 + 'X) * (1 + 'X + 'X ^+ 2) *
    (1 + 'X + 'X ^+ 2 + 'X ^+ 3) *
    (1 + 'X + 'X ^+ 2 + 'X ^+ 3 + 'X ^+ 4).

Definition five_cycle_denominator_complement : Poly :=
  (1 - 'X) * (1 - 'X ^+ 2) * (1 - 'X ^+ 3) * (1 - 'X ^+ 4).

Definition one_two_two_denominator_complement : Poly :=
  (1 - 'X ^+ 3) * (1 + 'X ^+ 2) * (1 - 'X ^+ 5).

Definition one_four_denominator_complement : Poly :=
  (1 - 'X ^+ 2) * (1 - 'X ^+ 3) * (1 - 'X ^+ 5).

(** Local reflective-ring bridge for identities in [rat['X]]. *)
Definition molien_poly_ring_carrier : Type := Poly.
Definition molien_poly_ring_zero : molien_poly_ring_carrier :=
  @GRing.zero Poly.
Definition molien_poly_ring_one : molien_poly_ring_carrier :=
  @GRing.one Poly.
Definition molien_poly_ring_add :
    molien_poly_ring_carrier -> molien_poly_ring_carrier ->
      molien_poly_ring_carrier := @GRing.add Poly.
Definition molien_poly_ring_mul :
    molien_poly_ring_carrier -> molien_poly_ring_carrier ->
      molien_poly_ring_carrier := @GRing.mul Poly.
Definition molien_poly_ring_sub :
    molien_poly_ring_carrier -> molien_poly_ring_carrier ->
      molien_poly_ring_carrier := fun x y => x - y.
Definition molien_poly_ring_opp :
    molien_poly_ring_carrier -> molien_poly_ring_carrier :=
  @GRing.opp Poly.
Definition molien_poly_ring_eq :
    molien_poly_ring_carrier -> molien_poly_ring_carrier -> Prop :=
  @eq molien_poly_ring_carrier.

Lemma molien_poly_ring_addE (x y : Poly) :
  x + y = molien_poly_ring_add x y. Proof. reflexivity. Qed.
Lemma molien_poly_ring_mulE (x y : Poly) :
  x * y = molien_poly_ring_mul x y. Proof. reflexivity. Qed.
Lemma molien_poly_ring_subE (x y : Poly) :
  x - y = molien_poly_ring_sub x y. Proof. reflexivity. Qed.
Lemma molien_poly_ring_oppE (x : Poly) :
  - x = molien_poly_ring_opp x. Proof. reflexivity. Qed.
Lemma molien_poly_ring_zeroE :
  (0 : Poly) = molien_poly_ring_zero. Proof. reflexivity. Qed.
Lemma molien_poly_ring_oneE :
  (1 : Poly) = molien_poly_ring_one. Proof. reflexivity. Qed.

Lemma molien_poly_ring_theory :
  @ring_theory molien_poly_ring_carrier molien_poly_ring_zero
    molien_poly_ring_one molien_poly_ring_add molien_poly_ring_mul
    molien_poly_ring_sub molien_poly_ring_opp molien_poly_ring_eq.
Proof.
constructor; unfold molien_poly_ring_carrier, molien_poly_ring_zero,
  molien_poly_ring_one, molien_poly_ring_add, molien_poly_ring_mul,
  molien_poly_ring_sub, molien_poly_ring_opp, molien_poly_ring_eq; intros.
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

Add Ring lazard_molien_numerator_poly_ring : molien_poly_ring_theory.
Opaque molien_poly_ring_zero molien_poly_ring_one molien_poly_ring_add
  molien_poly_ring_mul molien_poly_ring_sub molien_poly_ring_opp
  molien_poly_ring_eq.

Ltac finish_molien_poly_ring :=
  repeat first
    [ rewrite molien_poly_ring_addE | rewrite molien_poly_ring_mulE
    | rewrite molien_poly_ring_subE | rewrite molien_poly_ring_oppE
    | rewrite molien_poly_ring_zeroE | rewrite molien_poly_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (molien_poly_ring_eq lhs rhs)
  end;
  ring.

Lemma identity_weights_positive i : 0 < tnth MC.identity_weights i.
Proof.
case: i => [[|[|[|[|[|i]]]]] hi; last by move: hi.
all: by [].
Qed.

Lemma five_cycle_weights_positive i : 0 < tnth MC.five_cycle_weights i.
Proof.
case: i => [[|i] hi]; last by move: hi.
by [].
Qed.

Lemma one_two_two_weights_positive i :
  0 < tnth MC.one_two_two_weights i.
Proof.
case: i => [[|[|[|i]]] hi]; last by move: hi.
all: by [].
Qed.

Lemma one_four_weights_positive i : 0 < tnth MC.one_four_weights i.
Proof.
case: i => [[|[|i]] hi]; last by move: hi.
all: by [].
Qed.

Lemma f20_identity_denominator_factorization :
  f20_symmetric_denominator_poly =
    identity_denominator_complement *
      weighted_denominator_poly MC.identity_weights.
Proof.
rewrite /f20_symmetric_denominator_poly
  /identity_denominator_complement
  /weighted_denominator_poly /MC.identity_weights
  !big_ord_recr big_ord0 /=.
rewrite !exprS expr0 !mulr1.
finish_molien_poly_ring.
Qed.

Lemma f20_five_cycle_denominator_factorization :
  f20_symmetric_denominator_poly =
    five_cycle_denominator_complement *
      weighted_denominator_poly MC.five_cycle_weights.
Proof.
rewrite /f20_symmetric_denominator_poly
  /five_cycle_denominator_complement
  /weighted_denominator_poly /MC.five_cycle_weights
  !big_ord_recr big_ord0 /=.
rewrite !exprS expr0 !mulr1.
finish_molien_poly_ring.
Qed.

Lemma f20_one_two_two_denominator_factorization :
  f20_symmetric_denominator_poly =
    one_two_two_denominator_complement *
      weighted_denominator_poly MC.one_two_two_weights.
Proof.
rewrite /f20_symmetric_denominator_poly
  /one_two_two_denominator_complement
  /weighted_denominator_poly /MC.one_two_two_weights
  !big_ord_recr big_ord0 /=.
rewrite !exprS expr0 !mulr1.
finish_molien_poly_ring.
Qed.

Lemma f20_one_four_denominator_factorization :
  f20_symmetric_denominator_poly =
    one_four_denominator_complement *
      weighted_denominator_poly MC.one_four_weights.
Proof.
rewrite /f20_symmetric_denominator_poly
  /one_four_denominator_complement
  /weighted_denominator_poly /MC.one_four_weights
  !big_ord_recr big_ord0 /=.
rewrite !exprS expr0 !mulr1.
finish_molien_poly_ring.
Qed.

Definition f20_weighted_denominator_complements : Poly :=
  identity_denominator_complement +
  (4%:R : rat)%:P * five_cycle_denominator_complement +
  (5%:R : rat)%:P * one_two_two_denominator_complement +
  (10%:R : rat)%:P * one_four_denominator_complement.

Lemma f20_weighted_denominator_complements_eq_numerator :
  f20_weighted_denominator_complements =
    (20%:R : rat)%:P * f20_molien_numerator_poly.
Proof.
rewrite /f20_weighted_denominator_complements
  /identity_denominator_complement /five_cycle_denominator_complement
  /one_two_two_denominator_complement
  /one_four_denominator_complement
  /f20_molien_numerator_poly.
rewrite !exprS expr0 !mulr1.
finish_molien_poly_ring.
Qed.

(** * The coefficientwise numerator identity *)

Definition series_add (a b : MC.rational_series) : MC.rational_series :=
  fun d => a d + b d.

Definition series_scale (c : rat) (a : MC.rational_series) :
    MC.rational_series :=
  fun d => c * a d.

Lemma polynomial_series_action_add p a b d :
  polynomial_series_action p (series_add a b) d =
    polynomial_series_action p a d + polynomial_series_action p b d.
Proof.
rewrite /polynomial_series_action /series_add.
under [LHS] eq_bigr => i _ do rewrite mulrDr.
exact: big_split.
Qed.

Lemma polynomial_series_action_scale p c a d :
  polynomial_series_action p (series_scale c a) d =
    c * polynomial_series_action p a d.
Proof.
rewrite /polynomial_series_action /series_scale mulr_sumr.
apply: eq_bigr => i _.
by rewrite mulrA [p`_i * c]mulrC -mulrA.
Qed.

Definition f20_geometric_class_expression : MC.rational_series :=
  series_scale (20%:R : rat)^-1
    (series_add
      (series_add
        (series_add MC.identity_geometric_series
          (series_scale 4%:R MC.five_cycle_geometric_series))
        (series_scale 5%:R MC.one_two_two_geometric_series))
      (series_scale 10%:R MC.one_four_geometric_series)).

Lemma f20_geometric_class_expressionE :
  MC.series_equiv MC.f20_geometric_class_sum_series
    f20_geometric_class_expression.
Proof. by move=> d. Qed.

Theorem f20_geometric_class_sum_mul_symmetric_denominator d :
  polynomial_series_action f20_symmetric_denominator_poly
      MC.f20_geometric_class_sum_series d =
    f20_molien_numerator_poly`_d.
Proof.
rewrite (f20_geometric_class_expressionE d)
  /f20_geometric_class_expression.
rewrite polynomial_series_action_scale
  !polynomial_series_action_add !polynomial_series_action_scale.
rewrite (polynomial_action_weighted_geometric_of_factorization
    identity_weights_positive f20_identity_denominator_factorization d).
rewrite (polynomial_action_weighted_geometric_of_factorization
    five_cycle_weights_positive f20_five_cycle_denominator_factorization d).
rewrite (polynomial_action_weighted_geometric_of_factorization
    one_two_two_weights_positive
      f20_one_two_two_denominator_factorization d).
rewrite (polynomial_action_weighted_geometric_of_factorization
    one_four_weights_positive f20_one_four_denominator_factorization d).
have hcoef := congr1 (fun p : Poly => p`_d)
  f20_weighted_denominator_complements_eq_numerator.
rewrite /f20_weighted_denominator_complements
  !coefD !coefCM in hcoef.
rewrite hcoef mulrA mulVf ?mul1r //.
exact: natrG_neq0.
Qed.

(** This is the formal-series interpretation of Lazard's displayed
    numerator for the finite Reynolds-rank sequence.  It says
    coefficientwise that

      [(1-t)(1-t^2)(1-t^3)(1-t^4)(1-t^5)] H(t)
        = 1+t^4+t^5+t^6+t^7+t^8,

    where [H(d)] is the rank of the degree-[d] Reynolds matrix.  The legacy
    theorem and sequence names retain "invariant_hilbert_series", but the
    polynomial-space identification is not asserted here. *)
Theorem f20_invariant_hilbert_series_mul_symmetric_denominator d :
  polynomial_series_action f20_symmetric_denominator_poly
      MC.f20_invariant_hilbert_series d =
    f20_molien_numerator_poly`_d.
Proof.
rewrite /polynomial_series_action.
under [LHS] eq_bigr => j _ do
  rewrite (MC.f20_class_sum_hilbert_series (d - j)).
exact: f20_geometric_class_sum_mul_symmetric_denominator.
Qed.

Theorem f20_invariant_hilbert_series_has_lazard_numerator :
  forall d,
    \sum_(j < d.+1)
      f20_symmetric_denominator_poly`_j *
        MC.f20_invariant_hilbert_series (d - j) =
      f20_molien_numerator_poly`_d.
Proof.
move=> d.
exact: f20_invariant_hilbert_series_mul_symmetric_denominator.
Qed.

End PolynomialFormulasLazardInvariantMolienNumeratorSeries.
