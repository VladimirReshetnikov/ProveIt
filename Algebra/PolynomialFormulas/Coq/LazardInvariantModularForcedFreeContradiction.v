From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.

From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule LazardInvariantSubgroupModule
  LazardInvariantHomogeneousCoordinates
  LazardInvariantModularCounterexample
  LazardInvariantModularCyclicSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The genuine semantic contradiction behind the modular [C6] example.

    The quantified input below is the raw homogeneous finite-free
    decomposition asserted by Lazard's invariant-module theorem, for the
    actual fixed submodule of the regular six-cycle over ['F_3].  No Hilbert
    series, quotient dimension, or spanning consequence is assumed.  They
    are derived from reconstruction, coordinate uniqueness and the literal
    orbit/product matrices. *)
Module PolynomialFormulasLazardInvariantModularForcedFreeContradiction.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.
Local Open Scope matrix_set_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module HC := PolynomialFormulasLazardInvariantHomogeneousCoordinates.
Module MC := PolynomialFormulasLazardInvariantModularCounterexample.
Module CS := PolynomialFormulasLazardInvariantModularCyclicSemantics.

Local Notation F3 := 'F_3.
Local Notation Inv :=
  (SIM.lazard_subgroup_invariant_module F3 CS.regular_C6).
Local Notation Exponent := (6.-tuple nat).

(** * The printed characteristic exclusions *)

Lemma F3_pchar_three : 3 \in [pchar F3].
Proof. exact: pchar_Fp. Qed.

Lemma F3_pcharE : [pchar F3] =i (3 : nat_pred).
Proof. exact: GRing.pcharf_eq F3_pchar_three. Qed.

Lemma F3_pchar_not_two : 2 \notin [pchar F3].
Proof. by rewrite F3_pcharE. Qed.

Lemma F3_pchar_not_five : 5 \notin [pchar F3].
Proof. by rewrite F3_pcharE. Qed.

Theorem F3_satisfies_lazard_printed_characteristic_exclusions :
  (2 \notin [pchar F3]) /\ (5 \notin [pchar F3]).
Proof. exact: conj F3_pchar_not_two F3_pchar_not_five. Qed.

(** * Coordinate homogeneity transported to the genuine invariant subtype *)

Section HypotheticalDecomposition.

Variable D :
  @FF.homogeneous_finite_free_decomposition
    {mpoly F3[6]} Inv
    (SIM.lazard_invariant_homogeneous
      (F := F3) (n := 6) (H := CS.regular_C6))
    (IM.lazard_degree_bound 6).

Local Notation B := (FF.hffd_free D).
Local Notation bdeg := (FF.hffd_degree D).

Definition invariant_homogeneous_coordinate
    (p : Inv) (t : nat) (i : FF.ffd_index B) : {mpoly F3[6]} :=
  if bdeg i <= t then
    pihomog mnmwgt (t - bdeg i) (FF.ffd_coeff B p i)
  else 0.

Lemma invariant_val_reconstruct (p : Inv) :
  SIM.lazard_subgroup_invariant_val p =
    \sum_i IM.sym_eval (FF.ffd_coeff B p i) *
      SIM.lazard_subgroup_invariant_val (FF.ffd_basis B i).
Proof.
have h := congr1 SIM.lazard_subgroup_invariant_val
  (FF.ffd_reconstruct B p).
move: h; rewrite linear_sum /=.
under [RHS] eq_bigr=> i _ do
  rewrite linearZ /= SM.symmetric_scalarE.
by move=> ->.
Qed.

Lemma invariant_pihomog_reconstruct (p : Inv) t :
  pihomog mdeg t (SIM.lazard_subgroup_invariant_val p) =
    \sum_i IM.sym_eval (invariant_homogeneous_coordinate p t i) *
      SIM.lazard_subgroup_invariant_val (FF.ffd_basis B i).
Proof.
rewrite invariant_val_reconstruct raddf_sum /=.
apply: eq_bigr=> i _.
rewrite /invariant_homogeneous_coordinate.
rewrite HC.lazard_pihomog_symmetric_scalar_right;
  last exact: FF.hffd_basis_is_homogeneous D i.
case hib: (bdeg i <= t)=> //=.
by rewrite IM.sym_eval0 mul0r.
Qed.

Lemma invariant_homogeneous_coordinateE
    (p : Inv) t (hp : SIM.lazard_invariant_homogeneous p t) i :
  invariant_homogeneous_coordinate p t i = FF.ffd_coeff B p i.
Proof.
apply: FF.ffd_coeff_unique.
apply: SIM.lazard_subgroup_invariant_val_injective.
rewrite linear_sum /=.
under [RHS] eq_bigr=> j _ do
  rewrite linearZ /= SM.symmetric_scalarE.
move: (invariant_pihomog_reconstruct p t).
by rewrite pihomog_dE //.
Qed.

Lemma invariant_ffd_coeff_eq0_of_degree_lt
    (p : Inv) t (hp : SIM.lazard_invariant_homogeneous p t) i :
  t < bdeg i -> FF.ffd_coeff B p i = 0.
Proof.
move=> hti.
have hc := invariant_homogeneous_coordinateE hp i.
rewrite /invariant_homogeneous_coordinate in hc.
have hnot : ~~ (bdeg i <= t) by rewrite -ltnNge.
by rewrite (negbTE hnot) in hc; rewrite -hc.
Qed.

Lemma invariant_ffd_coeff_homogeneous
    (p : Inv) t (hp : SIM.lazard_invariant_homogeneous p t) i :
  bdeg i <= t ->
  FF.ffd_coeff B p i \is (t - bdeg i).-homog for mnmwgt.
Proof.
move=> hit; rewrite homog_piE; apply/eqP.
move: (invariant_homogeneous_coordinateE hp i).
by rewrite /invariant_homogeneous_coordinate hit.
Qed.

(** * The elementary-symmetric tower in one bounded degree *)

Definition bounded_scalar_exponent (d : nat) := 6.-tuple 'I_d.+1.

Definition bounded_scalar_exponent_val d
    (a : bounded_scalar_exponent d) : Exponent :=
  [tuple (tnth a i : nat) | i < 6].

Definition bounded_scalar_monomial d
    (a : bounded_scalar_exponent d) : 'X_{1..6} :=
  [multinom (tnth a i : nat) | i < 6].

Definition bounded_scalar_weight d
    (a : bounded_scalar_exponent d) : nat :=
  \sum_(i < 6) (tnth a i : nat) * i.+1.

Lemma bounded_scalar_monomialE d (a : bounded_scalar_exponent d) i :
  bounded_scalar_monomial a i = (tnth a i : nat).
Proof. by rewrite /bounded_scalar_monomial mnmE. Qed.

Lemma bounded_scalar_monomial_injective d :
  injective (@bounded_scalar_monomial d).
Proof.
move=> a b hab; apply/eq_from_tnth=> i; apply/val_inj=> /=.
move/mnmP/(_ i): hab.
by rewrite !bounded_scalar_monomialE.
Qed.

Lemma bounded_scalar_monomial_weight d (a : bounded_scalar_exponent d) :
  mnmwgt (bounded_scalar_monomial a) = bounded_scalar_weight a.
Proof.
rewrite /mnmwgt /bounded_scalar_weight.
apply: eq_bigr=> i _.
by rewrite bounded_scalar_monomialE.
Qed.

Definition tower_degree_index (d : nat) :=
  {ai : bounded_scalar_exponent d * FF.ffd_index B |
    bounded_scalar_weight ai.1 + bdeg ai.2 == d}.

Definition tower_scalar d (r : tower_degree_index d) : {mpoly F3[6]} :=
  'X_[F3, bounded_scalar_monomial r.1.1].

Definition tower_invariant d (r : tower_degree_index d) : Inv :=
  tower_scalar r *: FF.ffd_basis B r.1.2.

Lemma tower_invariant_val d (r : tower_degree_index d) :
  SIM.lazard_subgroup_invariant_val (tower_invariant r) =
    IM.sym_eval (tower_scalar r) *
      SIM.lazard_subgroup_invariant_val (FF.ffd_basis B r.1.2).
Proof. by rewrite /tower_invariant linearZ /= SM.symmetric_scalarE. Qed.

Lemma tower_invariant_homogeneous d (r : tower_degree_index d) :
  SIM.lazard_invariant_homogeneous (tower_invariant r) d.
Proof.
rewrite /SIM.lazard_invariant_homogeneous tower_invariant_val.
have hdegree : bounded_scalar_weight r.1.1 + bdeg r.1.2 = d :=
  eqP (valP r).
rewrite -hdegree.
apply: dhomogM.
- rewrite -IM.sym_eval_homogeneousE dhomogX
    bounded_scalar_monomial_weight eqxx.
- exact: FF.hffd_basis_is_homogeneous D r.1.2.
Qed.

Definition tower_polynomial d (r : tower_degree_index d) : {mpoly F3[6]} :=
  SIM.lazard_subgroup_invariant_val (tower_invariant r).

Definition tower_matrix (d : nat) :
    'M[F3]_(#|tower_degree_index d|, MC.invariant_orbit_count d) :=
  \matrix_(r, c)
    (tower_polynomial r)@_
      (CS.exponent_monomial (CS.orbit_representative c)).

Definition tower_row_combination d
    (u : 'rV[F3]_#|tower_degree_index d|) : {mpoly F3[6]} :=
  \sum_r (u 0 r) *: tower_polynomial r.

Definition tower_combination_invariant d
    (u : 'rV[F3]_#|tower_degree_index d|) : Inv :=
  \sum_r (u 0 r)%:MP *: tower_invariant r.

Lemma sym_eval_mpolyC (c : F3) : IM.sym_eval c%:MP = c%:MP.
Proof. exact: comp_mpolyC. Qed.

Lemma tower_combination_invariant_val d u :
  SIM.lazard_subgroup_invariant_val (tower_combination_invariant u) =
    tower_row_combination u.
Proof.
rewrite /tower_combination_invariant /tower_row_combination linear_sum /=.
apply: eq_bigr=> r _.
rewrite linearZ /= SM.symmetric_scalarE sym_eval_mpolyC mul_mpolyC.
reflexivity.
Qed.

Lemma tower_row_combination_homogeneous (d : 'I_8) u :
  tower_row_combination (d := d) u \is d.-homog.
Proof.
rewrite /tower_row_combination rpred_sum //= => r _.
exact/rpredZ/tower_invariant_homogeneous.
Qed.

Lemma orbit_coordinates_tower_row_combination (d : nat) u :
  CS.orbit_coordinates d (tower_row_combination u) = u *m tower_matrix d.
Proof.
apply/matrixP=> i j.
rewrite !mxE /CS.orbit_coordinates /tower_row_combination raddf_sum /=.
apply: eq_bigr=> r _.
by rewrite mcoeffZ !mxE.
Qed.

(** Coefficients of a tower combination, before homogeneous
    reconstruction.  This is the exact point where raw [hffd_unique]
    supplies linear independence; no vector-space basis is postulated. *)
Lemma ffd_coeff_tower_term d (u : F3) (r : tower_degree_index d) i m :
  (FF.ffd_coeff B ((u%:MP) *: tower_invariant r) i)@_m =
    if (r.1.2 == i) &&
        (bounded_scalar_monomial r.1.1 == m)
    then u else 0.
Proof.
rewrite /tower_invariant !FF.ffd_coeffZ
  FF.ffd_coeff_basis eq_sym.
case hri: (r.1.2 == i); last first.
- by rewrite hri /= !mulr0 mcoeff0.
- move/eqP: hri=> ->; rewrite eqxx /= mulr1.
  rewrite mcoeffCM mcoeffX mulr1.
  by case: (bounded_scalar_monomial r.1.1 == m).
Qed.

Lemma ffd_coeff_tower_combination_mcoeff d u i m :
  (FF.ffd_coeff B (tower_combination_invariant u) i)@_m =
    \sum_r if (r.1.2 == i) &&
        (bounded_scalar_monomial r.1.1 == m)
      then u 0 r else 0.
Proof.
rewrite /tower_combination_invariant FF.ffd_coeff_sum raddf_sum /=.
apply: eq_bigr=> r _.
exact: ffd_coeff_tower_term.
Qed.

Lemma tower_matching_index_unique d (r s : tower_degree_index d) :
  s.1.2 = r.1.2 ->
  bounded_scalar_monomial s.1.1 = bounded_scalar_monomial r.1.1 ->
  s = r.
Proof.
move=> hb hm; apply/val_inj; congr (_, _) => //.
exact: bounded_scalar_monomial_injective hm.
Qed.

Lemma ffd_coeff_tower_combination_at_index d u
    (r : tower_degree_index d) :
  (FF.ffd_coeff B (tower_combination_invariant u) r.1.2)@_
      (bounded_scalar_monomial r.1.1) = u 0 r.
Proof.
rewrite ffd_coeff_tower_combination_mcoeff (bigD1 r) //= !eqxx.
rewrite big1 ?addr0 // => s hsr.
case hsb: (s.1.2 == r.1.2); last by rewrite hsb.
case hsm: (bounded_scalar_monomial s.1.1 ==
    bounded_scalar_monomial r.1.1); last by rewrite hsm andbF.
have : s = r.
  apply: tower_matching_index_unique; exact/eqP.
  exact/eqP.
by move: hsr; rewrite this eqxx.
Qed.

Lemma tower_matrix_row_free (d : 'I_8) : row_free (tower_matrix D d).
Proof.
apply: inj_row_free=> u hu.
have hcoords :
    CS.orbit_coordinates d
      (tower_row_combination (D := D) u) = 0.
  by rewrite orbit_coordinates_tower_row_combination hu.
have hhom : SIM.lazard_invariant_homogeneous
    (tower_combination_invariant (D := D) u) d.
  rewrite /SIM.lazard_invariant_homogeneous
    tower_combination_invariant_val.
  exact: tower_row_combination_homogeneous D d u.
have hpoly : tower_row_combination (D := D) u = 0.
  have hrec := CS.orbit_reconstruction d
    (tower_combination_invariant (D := D) u)
    hhom.
  rewrite tower_combination_invariant_val hcoords
    /CS.orbit_combination big1 in hrec;
    last by move=> i _; rewrite mxE scale0r.
  by rewrite hrec.
have hinv0 : tower_combination_invariant (D := D) u = 0.
  apply: SIM.lazard_subgroup_invariant_val_injective.
  by rewrite tower_combination_invariant_val hpoly linear0.
apply/matrixP=> i r; rewrite ord1 mxE.
have hz := congr1
  (fun q : Inv =>
    (FF.ffd_coeff B q r.1.2)@_
      (bounded_scalar_monomial r.1.1))
  hinv0.
move: hz; rewrite FF.ffd_coeff0 mcoeff0
  ffd_coeff_tower_combination_at_index.
by move=> ->.
Qed.

(** Every monomial of weighted degree at most [d] has a canonical bounded
    tuple representative. *)
Definition bound_scalar_monomial (d : nat) (m : 'X_{1..6}) :
    bounded_scalar_exponent d :=
  [tuple inord (m i) | i < 6].

Lemma monomial_coordinate_le_weight (m : 'X_{1..6}) i :
  m i <= mnmwgt m.
Proof.
have himdeg : m i <= mdeg m.
  rewrite mdegE (bigD1 i) //=.
  exact: leq_addr.
exact: leq_trans himdeg (leq_mdeg_mnmwgt m).
Qed.

Lemma bounded_scalar_monomial_boundK d m :
  mnmwgt m <= d ->
  bounded_scalar_monomial (bound_scalar_monomial d m) = m.
Proof.
move=> hmd; apply/mnmP=> i.
rewrite bounded_scalar_monomialE /bound_scalar_monomial tnth_mktuple.
rewrite inordK // -ltnS.
exact: leq_trans (monomial_coordinate_le_weight m i) hmd.
Qed.

Lemma bounded_scalar_weight_boundK d m (hmd : mnmwgt m <= d) :
  bounded_scalar_weight (bound_scalar_monomial d m) = mnmwgt m.
Proof.
rewrite -bounded_scalar_monomial_weight
  bounded_scalar_monomial_boundK //.
Qed.

Definition tower_coordinates d (p : Inv) :
    'rV[F3]_#|tower_degree_index d| :=
  \row_r (FF.ffd_coeff B p r.1.2)@_
    (bounded_scalar_monomial r.1.1).

(** Raw homogeneous coordinates reconstruct every homogeneous invariant from
    exactly the tower indices of its total degree. *)
Lemma tower_homogeneous_reconstruct (d : 'I_8) (p : Inv) :
  SIM.lazard_invariant_homogeneous p d ->
  tower_combination_invariant (D := D) (tower_coordinates D d p) = p.
Proof.
move=> hp; apply: FF.ffd_eq_of_coeff_eq=> i.
apply/mpolyP=> m.
rewrite ffd_coeff_tower_combination_mcoeff /tower_coordinates mxE.
case hid: (bdeg i <= d).
- have hc := invariant_ffd_coeff_homogeneous D hp i hid.
  case hweight: (mnmwgt m == d - bdeg i).
  + have hmweight : mnmwgt m = d - bdeg i by exact/eqP.
    have hmd : mnmwgt m <= d by rewrite hmweight; exact: leq_subr.
    pose a := bound_scalar_monomial d m.
    have haweight : bounded_scalar_weight a = mnmwgt m :=
      bounded_scalar_weight_boundK hmd.
    have hatotal : bounded_scalar_weight a + bdeg i == d.
      apply/eqP; rewrite haweight hmweight subnK //.
    pose r : tower_degree_index D d := Sub (a, i) hatotal.
    rewrite (bigD1 r) //= !eqxx.
    rewrite bounded_scalar_monomial_boundK // addr0.
    rewrite big1 ?addr0 // => s hsr.
    case hsi: (s.1.2 == i); last by rewrite hsi.
    case hsm: (bounded_scalar_monomial s.1.1 == m);
      last by rewrite hsm andbF.
    have hsr' : s = r.
      apply: tower_matching_index_unique; first exact/eqP.
      move/eqP: hsm=> ->.
      by rewrite bounded_scalar_monomial_boundK.
    by move: hsr; rewrite hsr' eqxx.
  + have hzero : (FF.ffd_coeff B p i)@_m = 0.
      exact: dhomog_nemf_coeff hc hweight.
    rewrite hzero; apply: big1=> s _.
    case hsi: (s.1.2 == i); last by rewrite hsi.
    case hsm: (bounded_scalar_monomial s.1.1 == m);
      last by rewrite hsm andbF.
    have hsdegree := eqP (valP s).
    have hsweight := bounded_scalar_monomial_weight s.1.1.
    move/eqP: hsi=> hsi; move/eqP: hsm=> hsm.
    have : mnmwgt m = d - bdeg i.
      rewrite -hsm hsweight hsi.
      lia.
    by move: hweight; rewrite this eqxx.
- have hdi : d < bdeg i by rewrite ltnNge hid.
  have hzero := invariant_ffd_coeff_eq0_of_degree_lt D hp i hdi.
  rewrite hzero mcoeff0; apply: big1=> s _.
  case hsi: (s.1.2 == i); last by rewrite hsi.
  case hsm: (bounded_scalar_monomial s.1.1 == m);
    last by rewrite hsm andbF.
  have hsdegree := eqP (valP s).
  move/eqP: hsi=> hsi.
  rewrite hsi in hsdegree.
  lia.
Qed.

Lemma tower_coordinates_matrixE (d : 'I_8)
    (p : Inv) (hp : SIM.lazard_invariant_homogeneous p d) :
  tower_coordinates D d p *m tower_matrix D d =
    CS.orbit_coordinates d (SIM.lazard_subgroup_invariant_val p).
Proof.
rewrite -orbit_coordinates_tower_row_combination.
have hrec := tower_homogeneous_reconstruct D hp.
have hval := congr1 SIM.lazard_subgroup_invariant_val hrec.
rewrite tower_combination_invariant_val in hval.
by rewrite hval.
Qed.

Lemma tower_matrix_row_full (d : 'I_8) : row_full (tower_matrix D d).
Proof.
apply/row_fullP.
exists (\matrix_(j, r)
  tower_coordinates D d
    (CS.orbit_combination_invariant d (row j 1%:M)) 0 r).
apply/matrixP=> i j.
have hp : SIM.lazard_invariant_homogeneous
    (CS.orbit_combination_invariant d (row i 1%:M)) d.
  rewrite /SIM.lazard_invariant_homogeneous
    CS.orbit_combination_invariant_val.
  exact: CS.orbit_combination_homogeneous d (row i 1%:M).
have hrow := tower_coordinates_matrixE D hp.
have hcoord := CS.orbit_coordinates_combination d (row i 1%:M).
move: (congr1 (fun A => A 0 j) hrow).
rewrite mxE hcoord row1 !mxE.
by move=> ->.
Qed.

Theorem tower_degree_index_card_eq_orbit_count (d : 'I_8) :
  #|tower_degree_index D d| = MC.invariant_orbit_count d.
Proof.
have hfree := tower_matrix_row_free D d.
have hfull := tower_matrix_row_full D d.
move: hfree; rewrite /row_free=> /eqP hfree.
move: hfull; rewrite /row_full=> /eqP hfull.
by rewrite -hfree hfull.
Qed.

(** * The bounded Hilbert convolution derived from the raw tower *)

Definition coefficient_weight_count (e : nat) : nat :=
  nth 0 [:: 1; 1; 2; 3; 5; 7; 11; 14] e.

Lemma bounded_scalar_weight_fiber_card (d e : 'I_8) :
  e <= d ->
  #|[pred a : bounded_scalar_exponent d |
      bounded_scalar_weight a == e]| = coefficient_weight_count e.
Proof.
move=> hed.
have hclosed :
    [forall b : 'I_8,
      [forall w : 'I_8,
        (w <= b) ==>
          (#|[pred a : bounded_scalar_exponent b |
            bounded_scalar_weight a == w]| ==
              coefficient_weight_count w)]].
  vm_compute.
have h := forallP (forallP hclosed d) e.
by rewrite hed /= in h; exact/eqP: h.
Qed.

Lemma tower_degree_index_card_eq_basis_sum (d : 'I_8) :
  #|tower_degree_index D d| =
    \sum_i if bdeg i <= d then
      coefficient_weight_count (d - bdeg i) else 0.
Proof.
rewrite /tower_degree_index card_sig -sum1_card.
rewrite -pair_big_dep /=.
rewrite (exchange_big_dep predT) //=.
apply: eq_bigr=> i _.
rewrite sum1_card.
case hid: (bdeg i <= d).
- pose e : 'I_8 := Ordinal
    (leq_ltn_trans (leq_subr (bdeg i) d) (ltn_ord d)).
  have he : e = d - bdeg i :> nat by reflexivity.
  have hpred :
      [pred a : bounded_scalar_exponent d |
        bounded_scalar_weight a + bdeg i == d] =1
      [pred a : bounded_scalar_exponent d |
        bounded_scalar_weight a == e].
    move=> a; rewrite he -{2}(subnK hid) eqn_add2r.
    reflexivity.
  rewrite (eq_card hpred) (bounded_scalar_weight_fiber_card d e) // he.
- apply: eq_card0=> a.
  apply/negP=> /eqP ha.
  move: hid; apply/negP; rewrite -ltnNge.
  lia.
Qed.

Definition basis_degree_fin (i : FF.ffd_index B) : 'I_16 :=
  @Ordinal 16 (bdeg i)
    (leq_ltn_trans (FF.hffd_basis_degree_bounded D i) (by vm_compute)).

Definition basis_degree_count (e : nat) : nat :=
  #|[pred i : FF.ffd_index B | bdeg i == e]|.

Lemma basis_degree_fin_fiber_card (e : 'I_16) :
  #|[pred i : FF.ffd_index B | basis_degree_fin i == e]| =
    basis_degree_count e.
Proof.
apply: eq_card=> i.
apply/eqP/eqP.
- move=> hie.
  exact: congr1 val hie.
- move=> hie; apply/val_inj.
  exact: hie.
Qed.

Lemma sum_by_basis_degree (f : nat -> nat) :
  \sum_i f (bdeg i) =
    \sum_(e < 16) basis_degree_count D e * f e.
Proof.
rewrite (partition_big (basis_degree_fin D) predT) //=.
apply: eq_bigr=> e _.
have hconst :
    \sum_(i | basis_degree_fin D i == e) f (bdeg i) =
      \sum_(i | basis_degree_fin D i == e) f e.
  apply: eq_bigr=> i /eqP hi.
  by rewrite (congr1 val hi).
rewrite hconst sum_nat_const basis_degree_fin_fiber_card.
Qed.

Theorem invariant_orbit_count_hilbert_convolution (d : 'I_8) :
  MC.invariant_orbit_count d =
    \sum_(e < 16) basis_degree_count D e *
      (if e <= d then coefficient_weight_count (d - e) else 0).
Proof.
rewrite -tower_degree_index_card_eq_orbit_count
  tower_degree_index_card_eq_basis_sum.
exact: sum_by_basis_degree
  (fun e => if e <= d then coefficient_weight_count (d - e) else 0).
Qed.

Lemma invariant_orbit_count_small (d : 'I_8) :
  MC.invariant_orbit_count d =
    nth 0 [:: 1; 1; 4; 10; 22; 42; 80; 132] d.
Proof.
have hclosed :
    [forall e : 'I_8,
      MC.invariant_orbit_count e ==
        nth 0 [:: 1; 1; 4; 10; 22; 42; 80; 132] e].
  vm_compute.
exact/eqP: (forallP hclosed d).
Qed.

(** Expanding the eight finite convolutions and solving successively gives
    the Hilbert numerator forced by [D]. *)
Lemma basis_degree_count_zero : basis_degree_count D 0 = 1.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (0 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=.
lia.
Qed.

Lemma basis_degree_count_one : basis_degree_count D 1 = 0.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (1 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /= basis_degree_count_zero.
lia.
Qed.

Lemma basis_degree_count_two : basis_degree_count D 2 = 2.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (2 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=
  basis_degree_count_zero basis_degree_count_one.
lia.
Qed.

Lemma basis_degree_count_three : basis_degree_count D 3 = 5.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (3 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=
  basis_degree_count_zero basis_degree_count_one
  basis_degree_count_two.
lia.
Qed.

Lemma basis_degree_count_four : basis_degree_count D 4 = 8.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (4 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=
  basis_degree_count_zero basis_degree_count_one
  basis_degree_count_two basis_degree_count_three.
lia.
Qed.

Lemma basis_degree_count_five : basis_degree_count D 5 = 11.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (5 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=
  basis_degree_count_zero basis_degree_count_one
  basis_degree_count_two basis_degree_count_three
  basis_degree_count_four.
lia.
Qed.

Lemma basis_degree_count_six : basis_degree_count D 6 = 17.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (6 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=
  basis_degree_count_zero basis_degree_count_one
  basis_degree_count_two basis_degree_count_three
  basis_degree_count_four basis_degree_count_five.
lia.
Qed.

Theorem basis_degree_count_seven : basis_degree_count D 7 = 16.
Proof.
have h := invariant_orbit_count_hilbert_convolution D (7 : 'I_8).
rewrite invariant_orbit_count_small in h.
move: h; rewrite !big_ord_recl big_ord0 /=
  basis_degree_count_zero basis_degree_count_one
  basis_degree_count_two basis_degree_count_three
  basis_degree_count_four basis_degree_count_five
  basis_degree_count_six.
lia.
Qed.

(** * Positive elementary degree maps into the literal 159-row product span *)

Lemma product_source_mem (k : 'I_6)
    (j : CS.orbit_index (6 - k)) :
  (k.+1, CS.orbit_representative j) \in MC.product_sources 7.
Proof.
have hclosed :
    [forall i : 'I_6,
      [forall r : CS.orbit_index (6 - i),
        (i.+1, CS.orbit_representative r) \in MC.product_sources 7]].
  vm_compute.
exact: forallP (forallP hclosed k) j.
Qed.

Definition product_source_index (k : 'I_6)
    (j : CS.orbit_index (6 - k)) :
    'I_(size (MC.product_sources 7)).
Proof.
apply: Ordinal.
by rewrite index_mem product_source_mem.
Defined.

Lemma nth_product_source_index (k : 'I_6)
    (j : CS.orbit_index (6 - k)) :
  nth (1, MC.zero_exponent) (MC.product_sources 7)
      (product_source_index k j) =
    (k.+1, CS.orbit_representative j).
Proof.
rewrite /product_source_index /= nth_index //.
exact: product_source_mem k j.
Qed.

Definition product_embedding_coefficients (k : 'I_6)
    (w : 'rV[F3]_(MC.invariant_orbit_count (6 - k))) :
    'rV[F3]_(size (MC.product_sources 7)) :=
  \sum_j (w 0 j) *: delta_mx 0 (product_source_index k j).

Lemma elementary_mul_orbit_combination_coordinates (k : 'I_6)
    (w : 'rV[F3]_(MC.invariant_orbit_count (6 - k))) :
  CS.orbit_coordinates 7
      (mesym 6 F3 k.+1 * CS.orbit_combination (6 - k) w) =
    product_embedding_coefficients k w *m MC.product_matrix 7.
Proof.
rewrite /product_embedding_coefficients mulmx_suml.
under [RHS] eq_bigr=> j _ do rewrite -scalemxAl -rowE.
apply/matrixP=> z c.
rewrite !mxE /CS.orbit_coordinates /CS.orbit_combination
  mulr_sumr raddf_sum /=.
apply: eq_bigr=> j _.
rewrite mcoeffZ !mxE.
congr (w 0 j * _).
have hpoly :
    mesym 6 F3 k.+1 * CS.orbit_basis_polynomial j =
      CS.literal_product_polynomial (product_source_index k j).
  by rewrite /CS.literal_product_polynomial
    nth_product_source_index /CS.orbit_basis_polynomial.
have hrow := CS.orbit_coordinates_literal_product
  (product_source_index k j).
move: (congr1 (fun A => A 0 c) hrow).
by rewrite !mxE -hpoly.
Qed.

Lemma elementary_mul_orbit_combination_row_sub (k : 'I_6)
    (w : 'rV[F3]_(MC.invariant_orbit_count (6 - k))) :
  (CS.orbit_coordinates 7
      (mesym 6 F3 k.+1 * CS.orbit_combination (6 - k) w)
    <= MC.product_matrix 7)%MS.
Proof.
apply/submxP; exists (product_embedding_coefficients k w).
exact: elementary_mul_orbit_combination_coordinates.
Qed.

Lemma sym_eval_variable (k : 'I_6) :
  IM.sym_eval ('X_[F3, U_(k)]) = mesym 6 F3 k.+1.
Proof.
rewrite /IM.sym_eval /IM.elementary_symmetric_tuple comp_mpolyXU.
by rewrite tnth_mktuple.
Qed.

Lemma nonzero_monomial_coordinate (m : 'X_{1..6}) :
  m != 0%MM -> exists i : 'I_6, 0 < m i.
Proof.
move=> hm; apply/existsP; apply: contraNT hm.
rewrite negb_exists=> /forallP hzero.
apply/eqP/mnmP=> i; rewrite mnm0E.
move: (hzero i).
by rewrite -eqn0Ngt=> /eqP.
Qed.

Lemma unit_monomial_le_of_positive (m : 'X_{1..6}) i :
  0 < m i -> (U_(i) <= m)%MM.
Proof.
move=> hi; apply/mnm_lepP=> j; rewrite mnm1E.
case hij: (i == j).
- by move/eqP: hij=> <-; rewrite -ltnS.
- exact: leq0n _.
Qed.

Lemma mnmwgt_sub_unit_add (m : 'X_{1..6}) i :
  0 < m i -> mnmwgt (m - U_(i)) + i.+1 = mnmwgt m.
Proof.
move=> hi.
have hsplit := submK (unit_monomial_le_of_positive hi).
move: (congr1 mnmwgt hsplit).
by rewrite mnmwgtD mnmwgt1.
Qed.

Lemma scalar_monomial_factor (m : 'X_{1..6}) i :
  0 < m i ->
  'X_[F3, m] = 'X_[F3, U_(i)] * 'X_[F3, m - U_(i)].
Proof.
move=> hi.
have hsplit := submK (unit_monomial_le_of_positive hi).
rewrite -{1}hsplit mpolyXD.
exact: mulrC _ _.
Qed.

Lemma tower_matrix_rowE d (r : tower_degree_index D d) :
  row r (tower_matrix D d) =
    CS.orbit_coordinates d (tower_polynomial r).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma positive_tower_row_sub_product
    (r : tower_degree_index D 7) :
  bounded_scalar_monomial r.1.1 != 0%MM ->
  (row r (tower_matrix D 7) <= MC.product_matrix 7)%MS.
Proof.
move=> hm0.
case: (nonzero_monomial_coordinate hm0)=> k hk.
pose m := bounded_scalar_monomial r.1.1.
pose m' := (m - U_(k))%MM.
pose q : Inv := 'X_[F3, m'] *: FF.ffd_basis B r.1.2.
have hrdegree : mnmwgt m + bdeg r.1.2 = 7.
  move/eqP: (valP r).
  by rewrite -bounded_scalar_monomial_weight.
have hsplit : mnmwgt m' + k.+1 = mnmwgt m.
  exact: mnmwgt_sub_unit_add hk.
have hqdegree : mnmwgt m' + bdeg r.1.2 = 6 - k.
  lia.
have hqhom : SIM.lazard_invariant_homogeneous q (6 - k).
  rewrite /SIM.lazard_invariant_homogeneous /q linearZ /=
    SM.symmetric_scalarE -hqdegree.
  apply: dhomogM.
  + rewrite -IM.sym_eval_homogeneousE dhomogX eqxx.
  + exact: FF.hffd_basis_is_homogeneous D r.1.2.
have htower : tower_polynomial r = mesym 6 F3 k.+1 *
    SIM.lazard_subgroup_invariant_val q.
  rewrite /tower_polynomial tower_invariant_val /tower_scalar
    /q linearZ /= SM.symmetric_scalarE.
  rewrite (scalar_monomial_factor hk) IM.sym_evalM
    sym_eval_variable.
  by rewrite mulrA.
pose e : 'I_8 := @Ordinal 8 (6 - k)
  (leq_ltn_trans (leq_subr k 6) isT).
have hrec := CS.orbit_reconstruction e q hqhom.
rewrite tower_matrix_rowE htower -hrec.
exact: elementary_mul_orbit_combination_row_sub k
  (CS.orbit_coordinates (6 - k)
    (SIM.lazard_subgroup_invariant_val q)).
Qed.

(** The only tower rows not covered above have scalar exponent zero; they
    are exactly the hypothetical basis vectors of degree seven. *)
Definition degree_seven_basis_index :=
  {i : FF.ffd_index B | bdeg i == 7}.

Lemma degree_seven_basis_index_card :
  #|degree_seven_basis_index| = 16.
Proof.
rewrite /degree_seven_basis_index card_sig.
exact: basis_degree_count_seven D.
Qed.

Definition degree_seven_residue_matrix :
    'M[F3]_(#|degree_seven_basis_index|, MC.invariant_orbit_count 7) :=
  \matrix_(r, c)
    (SIM.lazard_subgroup_invariant_val (FF.ffd_basis B r.1))@_
      (CS.exponent_monomial (CS.orbit_representative c)).

Lemma degree_seven_residue_matrix_rowE
    (r : degree_seven_basis_index) :
  row r degree_seven_residue_matrix =
    CS.orbit_coordinates 7
      (SIM.lazard_subgroup_invariant_val (FF.ffd_basis B r.1)).
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

Lemma zero_tower_row_sub_residue (r : tower_degree_index D 7) :
  bounded_scalar_monomial r.1.1 = 0%MM ->
  (row r (tower_matrix D 7) <= degree_seven_residue_matrix)%MS.
Proof.
move=> hm0.
have hw0 : bounded_scalar_weight r.1.1 = 0.
  by rewrite -bounded_scalar_monomial_weight hm0 mnmwgt0.
have hbdeg : bdeg r.1.2 = 7.
  move/eqP: (valP r).
  by rewrite hw0 add0n.
have hbdegb : bdeg r.1.2 == 7 by exact/eqP.
pose s : degree_seven_basis_index := Sub r.1.2 hbdegb.
have hpoly : tower_polynomial r =
    SIM.lazard_subgroup_invariant_val (FF.ffd_basis B s.1).
  rewrite /tower_polynomial /tower_invariant /tower_scalar hm0
    mpolyX0 scale1r.
  reflexivity.
apply/submxP; exists (delta_mx 0 s).
rewrite -rowE tower_matrix_rowE hpoly.
exact: esym (degree_seven_residue_matrix_rowE s).
Qed.

Lemma tower_matrix_sub_product_add_residue :
  (tower_matrix D 7 <=
    MC.product_matrix 7 + degree_seven_residue_matrix)%MS.
Proof.
apply/row_subP=> r.
case hm0: (bounded_scalar_monomial r.1.1 == 0%MM).
- apply: submx_trans (zero_tower_row_sub_residue r (eqP hm0)).
  exact: addsmxSr.
- apply: submx_trans (positive_tower_row_sub_product r hm0).
  exact: addsmxSl.
Qed.

Lemma product_add_residue_row_full :
  row_full (MC.product_matrix 7 + degree_seven_residue_matrix)%MS.
Proof.
have h1tower : (1%:M <= tower_matrix D 7)%MS.
  by rewrite sub1mx tower_matrix_row_full.
have h1sum := submx_trans h1tower tower_matrix_sub_product_add_residue.
by rewrite sub1mx in h1sum.
Qed.

Theorem no_homogeneous_finite_free_decomposition : False.
Proof.
have hfull := product_add_residue_row_full.
have hsumrank :
    \rank (MC.product_matrix 7 + degree_seven_residue_matrix)%MS = 132.
  move/eqP: hfull; rewrite /row_full.
  by rewrite MC.cyclic_six_degree_seven_orbit_count.
have hproduct : \rank (MC.product_matrix 7) = 115.
  exact: MC.cyclic_six_degree_seven_product_rank.
have hresidue : \rank degree_seven_residue_matrix <= 16.
  move: (rank_leq_row degree_seven_residue_matrix).
  by rewrite degree_seven_basis_index_card.
have hsumle :
    \rank (MC.product_matrix 7 + degree_seven_residue_matrix)%MS <=
      \rank (MC.product_matrix 7) +
        \rank degree_seven_residue_matrix :=
  (mxrank_adds_leqif
    (MC.product_matrix 7) degree_seven_residue_matrix).1.
lia.
Qed.

End HypotheticalDecomposition.

(** This is the literal negation of the genuine Coq theorem target, not a
    negation of a separately supplied consequence record. *)
Theorem regular_C6_char_three_no_lazard_homogeneous_invariant_basis :
  ~ inhabited
    (@SIM.lazard_homogeneous_invariant_basis F3 6 CS.regular_C6).
Proof.
move=> [D].
exact: (no_homogeneous_finite_free_decomposition D).
Qed.

Theorem regular_C6_counterexample_with_printed_characteristic_exclusions :
  (2 \notin [pchar F3]) /\ (5 \notin [pchar F3]) /\
  ~ inhabited
    (@SIM.lazard_homogeneous_invariant_basis F3 6 CS.regular_C6).
Proof.
repeat split.
- exact: F3_pchar_not_two.
- exact: F3_pchar_not_five.
- exact: regular_C6_char_three_no_lazard_homogeneous_invariant_basis.
Qed.

(** Fully closed semantic package: the displayed subgroup has order six,
    the coefficient field has characteristic three while satisfying the
    paper's printed exclusions, and the actual fixed module has no
    advertised bounded homogeneous finite-free basis. *)
Theorem regular_C6_closed_semantic_counterexample :
  #|CS.regular_C6| = 6 /\
  3 \in [pchar F3] /\
  2 \notin [pchar F3] /\
  5 \notin [pchar F3] /\
  ~ inhabited
    (@SIM.lazard_homogeneous_invariant_basis F3 6 CS.regular_C6).
Proof.
repeat split.
- exact: CS.regular_C6_card.
- exact: F3_pchar_three.
- exact: F3_pchar_not_two.
- exact: F3_pchar_not_five.
- exact: regular_C6_char_three_no_lazard_homogeneous_invariant_basis.
Qed.

Print Assumptions regular_C6_char_three_no_lazard_homogeneous_invariant_basis.
Print Assumptions regular_C6_counterexample_with_printed_characteristic_exclusions.
Print Assumptions regular_C6_closed_semantic_counterexample.

End PolynomialFormulasLazardInvariantModularForcedFreeContradiction.
