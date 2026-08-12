From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.multinomials Require Import mpoly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The multivariate/univariate equivalence omitted from the public
    multinomials API.

    MathComp multinomials 2.4 defines both

      [muni   : mpoly R (n.+1) -> poly (mpoly R n)]
      [mmulti : poly (mpoly R n) -> mpoly R (n.+1)],

    but proves neither inverse law.  The ordered-root construction behind
    Lazard's Artin basis needs this equivalence at every successor stage.
    This module derives the two inverse laws directly from the definitions;
    no freeness or coordinate assumption is used. *)
Module PolynomialFormulasLazardInvariantMpolyUnivariate.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Section MpolyUnivariate.

Variables (R : comRingType) (n : nat).

Local Notation widen := (widen_ord (leqnSn _)).
Local Notation lastX := ('X_(ord_max) : {mpoly R[n.+1]}).

(** [mmulti] is Horner evaluation after widening every coefficient.  This
    presentation makes its ring-homomorphism laws transparent. *)
Definition mmulti_horner (p : {poly {mpoly R[n]}}) :
    {mpoly R[n.+1]} :=
  (map_poly (@mwiden n R) p).[lastX].

Lemma mmulti_hornerE p : mmulti_horner p = mmulti p.
Proof.
rewrite /mmulti_horner /mmulti horner_coef.
rewrite (size_map_inj_poly (@inj_mwiden n R) (@mwiden0 n R)).
apply: eq_bigr => i _.
by rewrite coef_map.
Qed.

Lemma mmulti0 : mmulti (0 : {poly {mpoly R[n]}}) = 0.
Proof. by rewrite -mmulti_hornerE /mmulti_horner map_poly0 horner0. Qed.

Lemma mmulti1 : mmulti (1 : {poly {mpoly R[n]}}) = 1.
Proof. by rewrite -mmulti_hornerE /mmulti_horner rmorph1 hornerC. Qed.

Lemma mmultiD : {morph @mmulti n R : p q / p + q}.
Proof.
move=> p q.
by rewrite -!mmulti_hornerE /mmulti_horner raddfD /= hornerD.
Qed.

Lemma mmultiN : {morph @mmulti n R : p / - p}.
Proof.
move=> p.
by rewrite -!mmulti_hornerE /mmulti_horner raddfN /= hornerN.
Qed.

Lemma mmultiM : {morph @mmulti n R : p q / p * q}.
Proof.
move=> p q.
by rewrite -!mmulti_hornerE /mmulti_horner rmorphM /= hornerM.
Qed.

Lemma mmultiC (p : {mpoly R[n]}) :
  mmulti p%:P = mwiden p.
Proof.
by rewrite -mmulti_hornerE /mmulti_horner map_polyC hornerC.
Qed.

Lemma mmultiX : mmulti ('X : {poly {mpoly R[n]}}) = lastX.
Proof.
by rewrite -mmulti_hornerE /mmulti_horner map_polyX hornerX.
Qed.

(** Widening a monomial and then viewing the last variable as the
    univariate variable produces a constant polynomial. *)
Lemma muni_mwidenX (m : 'X_{1..n}) :
  muni (mwiden ('X_[R, m])) = ('X_[R, m])%:P.
Proof.
rewrite mwidenX muniE msuppX big_seq1 mcoeffX eqxx scale1r.
rewrite mnmwiden_ordmax expr0.
have hprefix :
    [multinom (mnmwiden m) (widen i) | i < n] = m.
  apply/mnmP=> i.
  by rewrite !mnmE mnmwiden_widen.
rewrite hprefix.
by rewrite -mul_polyC mulr1.
Qed.

(** The last multivariate variable becomes the univariate indeterminate. *)
Lemma muni_lastX : muni lastX = ('X : {poly {mpoly R[n]}}).
Proof.
change (muni ('X_[R, U_(ord_max)]) = ('X : {poly {mpoly R[n]}})).
rewrite muniE msuppX big_seq1 mcoeffX eqxx scale1r.
rewrite mnm1E eqxx expr1.
have hprefix :
    [multinom (U_(ord_max)%MM : 'X_{1..n.+1}) (widen i) | i < n] = 0%MM.
  apply/mnmP=> i.
  rewrite mnmE mnm1E eqE /=.
  rewrite (gtn_eqF (ltn_ord i)).
  by rewrite mnm0E.
rewrite hprefix mpolyX0.
by rewrite scale1r.
Qed.

(** [muni] cancels coefficient widening. *)
Lemma muni_mwiden (p : {mpoly R[n]}) :
  muni (mwiden p) = p%:P.
Proof.
elim/mpolyind: p => [|c m p hm hc ih].
- by rewrite mwiden0 muni0 polyC0.
- rewrite mwidenD mwidenZ muniD muniZ muni_mwidenX ih.
  rewrite rmorphD.
  congr (_ + p%:P).
  by rewrite -mul_polyC -mul_mpolyC rmorphM.
Qed.

(** First inverse law: converting a univariate polynomial to one more
    multivariate variable and back is the identity. *)
Theorem muni_mmulti (p : {poly {mpoly R[n]}}) :
  muni (mmulti p) = p.
Proof.
elim/poly_ind: p => [|p c ih].
- by rewrite mmulti0 muni0.
- rewrite mmultiD mmultiM mmultiX mmultiC.
  by rewrite muniD muniM muni_lastX muni_mwiden ih.
Qed.

(** A monomial survives the round trip in the other direction. *)
Lemma mmulti_muniX (m : 'X_{1..n.+1}) :
  mmulti (muni ('X_[R, m])) = 'X_[R, m].
Proof.
rewrite muniE msuppX big_seq1 mcoeffX eqxx scale1r.
rewrite -mul_polyC mmultiM mmultiC.
rewrite -mmulti_hornerE /mmulti_horner map_polyXn hornerXn.
rewrite mwidenX.
rewrite mpolyXn -mpolyXD.
congr 'X_[_].
apply/mnmP=> i.
case: (unliftP ord_max i) => [j ->|->].
- have hlift : lift ord_max j = widen j.
    apply/val_inj.
    change ((lift ord_max j : nat) = (widen j : nat)).
    by rewrite lift_max.
  rewrite hlift mnmDE mnmwiden_widen mulmnE mnm1E eqE /=.
  by rewrite mnmE (gtn_eqF (ltn_ord j)) mul0n addn0.
- rewrite mnmDE mnmwiden_ordmax mulmnE mnm1E eqxx mul1n add0n.
  reflexivity.
Qed.

(** Second inverse law: viewing the last multivariate variable as a
    univariate variable and flattening again is the identity. *)
Theorem mmulti_muni (p : {mpoly R[n.+1]}) :
  mmulti (muni p) = p.
Proof.
elim/mpolyind: p => [|c m p hm hc ih].
- by rewrite muni0 mmulti0.
- rewrite muniD muniZ mmultiD.
  rewrite -mul_polyC mmultiM mmultiC mmulti_muniX ih.
  by rewrite mwidenC mul_mpolyC.
Qed.

Corollary muni_injective : injective (@muni n R).
Proof. exact: can_inj mmulti_muni. Qed.

Corollary muni_surjective : forall p, exists q, @muni n R q = p.
Proof. by move=> p; exists (mmulti p); exact: muni_mmulti. Qed.

Corollary mmulti_injective : injective (@mmulti n R).
Proof. exact: can_inj muni_mmulti. Qed.

Corollary mmulti_surjective : forall p, exists q, @mmulti n R q = p.
Proof. by move=> p; exists (muni p); exact: mmulti_muni. Qed.

End MpolyUnivariate.

End PolynomialFormulasLazardInvariantMpolyUnivariate.
