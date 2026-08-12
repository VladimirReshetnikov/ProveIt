From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Homogeneous coordinates in a finite symmetric-polynomial basis.

    The scalar ring is the source copy of the symmetric ring, graded by the
    elementary-symmetric weight [mnmwgt].  Taking the ordinary homogeneous
    component after multiplying by a homogeneous basis vector shifts that
    weighted degree.  Coordinate uniqueness therefore forces every
    coordinate of a homogeneous vector to have the corresponding shifted
    degree.  In particular, coordinates above the vector degree vanish and
    equal-degree coordinates are constants from the ground field. *)
Module PolynomialFormulasLazardInvariantHomogeneousCoordinates.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.

Section HomogeneousComponents.

Variables (F : fieldType) (n : nat).
Implicit Types p q : {mpoly F[n]}.

(** Taking a homogeneous component after right multiplication by a
    homogeneous polynomial merely shifts the requested degree. *)
Lemma lazard_pihomog_mul_right p q e t :
  q \is e.-homog ->
  pihomog mdeg t (p * q) =
    if (e <= t)%N then pihomog mdeg (t - e)%N p * q else 0.
Proof.
move=> hq.
rewrite {1}(mpolyE p) mulr_suml linear_sum /=.
case het: (e <= t)%N.
- rewrite /= [pihomog mdeg (t - e)%N p]pihomogE
    mulr_suml big_mkcond.
  change (
    (\sum_(u <- msupp p)
      pihomog mdeg t ((p@_u *: 'X_[F, u]) * q)) =
    (\sum_(u <- msupp p | mdeg u == (t - e)%N)
      (p@_u *: 'X_[F, u]) * q)).
  elim: (msupp p) => [|u s ih] /=.
  - by rewrite !big_nil.
  - rewrite !big_cons ih.
  have hterm : 'X_[F, u] * q \is ((mdeg u + e)%N).-homog.
    apply: dhomogM; last exact: hq.
    by rewrite dhomogX eqxx.
  case hud: (mdeg u == (t - e)%N).
  + rewrite /= -!scalerAl linearZ /=.
    have hdegree : (mdeg u + e)%N = t.
      by rewrite (eqP hud) (subnK het).
    have hproj : pihomog mdeg t ('X_[F, u] * q) = 'X_[F, u] * q.
      apply: pihomog_dE.
      by move: hterm; rewrite hdegree.
    by rewrite hproj.
  + rewrite /= -scalerAl linearZ /=.
    have hne : (mdeg u + e)%N != t.
      by rewrite -(subnK het) eqn_add2r hud.
    by rewrite (pihomog_ne0 hne hterm) scaler0 add0r.
- rewrite /=.
  apply: big1 => u hu.
  rewrite -scalerAl linearZ /=.
  have hterm : 'X_[F, u] * q \is ((mdeg u + e)%N).-homog.
    apply: dhomogM; last exact: hq.
    by rewrite dhomogX eqxx.
  have hte : (t < e)%N by rewrite ltnNge het.
  have htdegree : (t < (mdeg u + e)%N)%N :=
    leq_trans hte (leq_addl (mdeg u) e).
  have hne : (mdeg u + e)%N != t.
    by rewrite eq_sym (ltn_eqF htdegree).
  by rewrite (pihomog_ne0 hne hterm) scaler0.
Qed.

(** The homogeneous projection commutes with elementary-symmetric
    substitution, changing ordinary degree into elementary-symmetric
    weight. *)
Lemma lazard_pihomog_symmetric_scalar_right
    (c : {mpoly F[n]}) q e t :
  q \is e.-homog ->
  pihomog mdeg t (IM.sym_eval c * q) =
    if (e <= t)%N then
      IM.sym_eval (pihomog mnmwgt (t - e)%N c) * q
    else 0.
Proof.
move=> hq.
rewrite (lazard_pihomog_mul_right
  (q := q) (e := e) (IM.sym_eval c) t hq).
case: ifP => _ //.
by rewrite /IM.sym_eval pihomog_mPo.
Qed.

End HomogeneousComponents.

Section FiniteFreeCoordinates.

Variables (F : fieldType) (n : nat).
Variable degree_bound : nat.
Variable D :
  @FF.homogeneous_finite_free_decomposition
    {mpoly F[n]}
    (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
      F n)
    (SM.symmetric_module_homogeneous (R := F) (n := n))
    degree_bound.

Local Notation B := (FF.hffd_free D).
Local Notation degree := (FF.hffd_degree D).

Definition lazard_homogeneous_coordinate
    (p : SM.symmetric_polynomial_module F n) (t : nat)
    (i : FF.ffd_index B) : {mpoly F[n]} :=
  if (degree i <= t)%N then
    pihomog mnmwgt (t - degree i)%N (FF.ffd_coeff B p i)
  else 0.

(** Homogeneous projection of a basis expansion is obtained by taking the
    uniquely shifted weighted component of every scalar coordinate. *)
Lemma lazard_pihomog_reconstruct
    (p : SM.symmetric_polynomial_module F n) t :
  pihomog mdeg t p =
    \sum_i (lazard_homogeneous_coordinate p t i) *:
      FF.ffd_basis B i.
Proof.
rewrite {1}(FF.ffd_reconstruct B p) linear_sum /=.
apply: eq_bigr => i _.
rewrite !SM.symmetric_scalarE /lazard_homogeneous_coordinate.
rewrite (@lazard_pihomog_symmetric_scalar_right F n
  (FF.ffd_coeff B p i) (FF.ffd_basis B i) (degree i) t);
  last exact: (FF.hffd_basis_is_homogeneous (D := D) i).
case: ifP => hi //.
by rewrite IM.sym_eval0 mul0r.
Qed.

Lemma lazard_homogeneous_coordinateE
    (p : SM.symmetric_polynomial_module F n) t
    (hp : SM.symmetric_module_homogeneous p t) i :
  lazard_homogeneous_coordinate p t i = FF.ffd_coeff B p i.
Proof.
apply: FF.ffd_coeff_unique.
move: (lazard_pihomog_reconstruct p t).
by rewrite pihomog_dE //.
Qed.

(** A coordinate whose basis degree is larger than the degree of a
    homogeneous vector is zero. *)
Theorem lazard_ffd_coeff_eq0_of_degree_lt
    (p : SM.symmetric_polynomial_module F n) t
    (hp : SM.symmetric_module_homogeneous p t) i :
  (t < degree i)%N -> FF.ffd_coeff B p i = 0.
Proof.
move=> hti.
have hcomponent := lazard_homogeneous_coordinateE hp i.
rewrite /lazard_homogeneous_coordinate in hcomponent.
have hnot : ~~ (degree i <= t)%N by rewrite -ltnNge.
by rewrite (negbTE hnot) in hcomponent; rewrite -hcomponent.
Qed.

(** Every surviving coordinate has exactly the shifted weighted degree. *)
Theorem lazard_ffd_coeff_homogeneous
    (p : SM.symmetric_polynomial_module F n) t
    (hp : SM.symmetric_module_homogeneous p t) i :
  (degree i <= t)%N ->
  FF.ffd_coeff B p i \is ((t - degree i)%N).-homog for mnmwgt.
Proof.
move=> hit.
rewrite homog_piE.
apply/eqP.
move: (lazard_homogeneous_coordinateE hp i).
by rewrite /lazard_homogeneous_coordinate hit.
Qed.

(** Weighted degree zero contains only constants from the ground field. *)
Lemma lazard_weighted_homogeneous_zero_constant
    (c : {mpoly F[n]}) :
  c \is 0.-homog for mnmwgt ->
  exists r : F, c = r%:MP.
Proof.
move=> hc.
exists (c@_0%MM).
apply/mpolyP=> u.
rewrite mcoeffC.
case hu: (u == 0%MM).
- by move/eqP: hu => ->; rewrite mulr1.
- rewrite mulr0.
  apply: (@dhomog_nemf_coeff n F mnmwgt 0 c u hc).
  have hmdeg : (0 < mdeg u)%N by rewrite lt0n mdeg_eq0 hu.
  have hwgt : (0 < mnmwgt u)%N :=
    leq_trans hmdeg (leq_mdeg_mnmwgt u).
  by rewrite -lt0n.
Qed.

(** Equal-degree matrix entries of every degree-preserving endomorphism are
    ground-field constants. *)
Theorem lazard_ffd_coeff_constant_of_equal_degree
    (p : SM.symmetric_polynomial_module F n) t
    (hp : SM.symmetric_module_homogeneous p t) i :
  degree i = t ->
  exists r : F, FF.ffd_coeff B p i = r%:MP.
Proof.
move=> hit.
apply: lazard_weighted_homogeneous_zero_constant.
have hle : (degree i <= t)%N by rewrite hit.
have hcoord := lazard_ffd_coeff_homogeneous (i := i) hp hle.
rewrite hit subnn in hcoord.
exact: hcoord.
Qed.

Section DegreePreservingMap.

Variable T :
  SM.symmetric_polynomial_module F n ->
  SM.symmetric_polynomial_module F n.
Hypothesis T_homogeneous : forall p d,
  SM.symmetric_module_homogeneous p d ->
  SM.symmetric_module_homogeneous (T p) d.

Theorem lazard_degree_preserving_matrix_triangular i j :
  (degree j < degree i)%N ->
  FF.ffd_coeff B (T (FF.ffd_basis B j)) i = 0.
Proof.
move=> hji.
have hT : SM.symmetric_module_homogeneous
    (T (FF.ffd_basis B j)) (degree j).
  apply: T_homogeneous.
  exact: FF.hffd_basis_is_homogeneous.
exact: lazard_ffd_coeff_eq0_of_degree_lt hT i hji.
Qed.

Theorem lazard_degree_preserving_matrix_constant i j :
  degree i = degree j ->
  exists r : F,
    FF.ffd_coeff B (T (FF.ffd_basis B j)) i = r%:MP.
Proof.
move=> hij.
have hT : SM.symmetric_module_homogeneous
    (T (FF.ffd_basis B j)) (degree j).
  apply: T_homogeneous.
  exact: FF.hffd_basis_is_homogeneous.
exact: lazard_ffd_coeff_constant_of_equal_degree hT i hij.
Qed.

End DegreePreservingMap.

End FiniteFreeCoordinates.

End PolynomialFormulasLazardInvariantHomogeneousCoordinates.
