(** PAUSED DRAFT CHECKPOINT (not registered in the committed Coq manifests).

    This proposed polynomial-coordinate bridge has not yet passed its first
    proof-body compilation because its Molien-coefficient dependency remains
    unfinished. *)
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantMultinomials LazardInvariantMolienCoefficients.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Polynomial coordinates for the finite homogeneous Molien matrices.

    [LazardInvariantMolienCoefficients] constructs, in every degree [d], a
    finite permutation matrix whose indices are bounded exponent tuples of
    total degree [d].  This file identifies that finite index type with the
    genuine monomial basis of the MathComp space [dhomog 5 F d].

    The two explicit linear maps below are inverse.  More importantly, the
    coefficient calculation at the end proves that right multiplication by
    the transposed permutation matrix is exactly the honest polynomial left
    action [s |-> msym s^-1].  Thus the matrix fixed spaces are not merely
    combinatorial proxies: their coordinates are the coefficients of actual
    homogeneous polynomials. *)
Module PolynomialFormulasLazardInvariantMolienPolynomialCoordinates.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module MC := PolynomialFormulasLazardInvariantMolienCoefficients.

(** * Exponent tuples and genuine multivariate monomials *)

Definition degree_exponent_monomial d (a : MC.degree_exponent d) :
    'X_{1..5} :=
  [multinom (tnth (val a) i : nat) | i < 5].

Lemma degree_exponent_monomialE d (a : MC.degree_exponent d) i :
  degree_exponent_monomial a i = (tnth (val a) i : nat).
Proof. by rewrite /degree_exponent_monomial mnmE. Qed.

Lemma degree_exponent_monomial_degree d (a : MC.degree_exponent d) :
  mdeg (degree_exponent_monomial a) = d.
Proof.
rewrite mdegE /degree_exponent_monomial.
under eq_bigr=> i _ do rewrite mnmE.
exact/eqP: valP a.
Qed.

Lemma degree_exponent_monomial_injective d :
  injective (@degree_exponent_monomial d).
Proof.
move=> a b hab; apply/val_inj/eq_from_tnth=> i; apply/val_inj.
move: (congr1 (fun m : 'X_{1..5} => m i) hab).
by rewrite !degree_exponent_monomialE.
Qed.

Lemma monomial_coordinate_lt_degreeS d (m : 'X_{1..5}) :
  mdeg m = d -> forall i, m i < d.+1.
Proof.
move=> hmd i; rewrite ltnS -hmd mdegE (bigD1 i) //=.
exact: leq_addr.
Qed.

(** A degree-[d] monomial has all coordinates at most [d], hence can be
    converted canonically to the bounded tuple used by the matrix layer. *)
Definition monomial_degree_exponent d (m : 'X_{1..5})
    (hm : mdeg m = d) : MC.degree_exponent d.
Proof.
refine (Sub [tuple inord (m i) | i < 5] _).
apply/eqP.
have hinord i : ((inord (m i) : 'I_d.+1) : nat) = m i.
  exact: inordK (monomial_coordinate_lt_degreeS hm i).
rewrite /MC.exponent_total.
under eq_bigr=> i _ do rewrite tnth_mktuple hinord.
by rewrite -mdegE hm.
Defined.

Lemma degree_exponent_monomialK d (a : MC.degree_exponent d) :
  monomial_degree_exponent (degree_exponent_monomial_degree a) = a.
Proof.
apply/val_inj/eq_from_tnth=> i; apply/val_inj.
rewrite /monomial_degree_exponent tnth_mktuple inordK //.
exact: ltn_ord (tnth (val a) i).
Qed.

Lemma monomial_degree_exponentK d (m : 'X_{1..5})
    (hm : mdeg m = d) :
  degree_exponent_monomial (monomial_degree_exponent hm) = m.
Proof.
apply/mnmP=> i.
rewrite degree_exponent_monomialE /monomial_degree_exponent
  tnth_mktuple inordK //.
exact: monomial_coordinate_lt_degreeS hm i.
Qed.

(** Permuting a bounded exponent and permuting its monomial are the same
    operation.  The inverse here is precisely the inverse in the honest
    polynomial left action. *)
Lemma degree_exponent_monomial_act s d (a : MC.degree_exponent d) :
  degree_exponent_monomial (MC.act_degree_exponent s a) =
    [multinom degree_exponent_monomial a (s^-1 i) | i < 5].
Proof.
apply/mnmP=> i.
by rewrite degree_exponent_monomialE
  /MC.act_degree_exponent /= /MC.act_bounded_exponent
  mnmE tnth_mktuple degree_exponent_monomialE.
Qed.

(** * Mutually inverse homogeneous coordinate maps *)

Section HomogeneousCoordinates.

Variables (F : fieldType) (d : nat).

Definition homogeneous_coordinates (p : dhomog 5 F d) :
    'rV[F]_#|{: MC.degree_exponent d}| :=
  \row_(i < #|{: MC.degree_exponent d}|)
    p@_(degree_exponent_monomial (enum_val i)).

Lemma homogeneous_coordinates_is_linear : linear homogeneous_coordinates.
Proof.
move=> c p q; apply/matrixP=> i j.
by rewrite !mxE /= mcoeffD mcoeffZ.
Qed.

HB.instance Definition homogeneous_coordinates_linear :=
  GRing.isLinear.Build F (dhomog 5 F d)
    'rV[F]_#|{: MC.degree_exponent d}| _
    homogeneous_coordinates homogeneous_coordinates_is_linear.

Definition homogeneous_decode_poly
    (v : 'rV[F]_#|{: MC.degree_exponent d}|) : {mpoly F[5]} :=
  \sum_(a : MC.degree_exponent d)
    v 0 (enum_rank a) *: 'X_[F, degree_exponent_monomial a].

Lemma homogeneous_decode_poly_homogeneous
    (v : 'rV[F]_#|{: MC.degree_exponent d}|) :
  homogeneous_decode_poly v \is d.-homog.
Proof.
apply: rpred_sum=> a _; apply: dhomogZ.
by rewrite dhomogX degree_exponent_monomial_degree eqxx.
Qed.

Definition homogeneous_decode
    (v : 'rV[F]_#|{: MC.degree_exponent d}|) : dhomog 5 F d :=
  DHomog (homogeneous_decode_poly_homogeneous v).

Lemma homogeneous_coordinates_decode
    (v : 'rV[F]_#|{: MC.degree_exponent d}|) :
  homogeneous_coordinates (homogeneous_decode v) = v.
Proof.
apply/matrixP=> i j.
rewrite /homogeneous_coordinates /homogeneous_decode /=
  /homogeneous_decode_poly !mxE ord1 raddf_sum /=.
rewrite (bigD1 (enum_val j)) //= mcoeffZ mcoeffX enum_valK eqxx mulr1.
rewrite big1 ?addr0 // => a haj.
rewrite mcoeffZ mcoeffX.
have hne : degree_exponent_monomial a !=
    degree_exponent_monomial (enum_val j).
  apply/negP=> /eqP hmon.
  have ha : a = enum_val j := degree_exponent_monomial_injective hmon.
  by move: haj; rewrite ha eqxx.
by rewrite (negbTE hne) mulr0.
Qed.

Lemma homogeneous_monomial_expansion (p : dhomog 5 F d) :
  (p : {mpoly F[5]}) =
    \sum_(a : MC.degree_exponent d)
      p@_(degree_exponent_monomial a) *:
        'X_[F, degree_exponent_monomial a].
Proof.
apply/mpolyP=> m; rewrite raddf_sum.
case hsm: (m \in msupp p).
- have hmd : mdeg m = d := dhomog_mf (dhomog_is_dhomog p) hsm.
  pose a := monomial_degree_exponent hmd.
  have ha : degree_exponent_monomial a = m :=
    monomial_degree_exponentK hmd.
  rewrite (bigD1 a) //= mcoeffZ mcoeffX ha eqxx mulr1.
  rewrite big1 ?addr0 // => b hba.
  rewrite mcoeffZ mcoeffX.
  have hbm : degree_exponent_monomial b != m.
    apply/negP=> /eqP hbm.
    have hba' : b = a.
      apply: degree_exponent_monomial_injective.
      exact: hbm.trans ha.symm.
    by move: hba; rewrite hba' eqxx.
  by rewrite (negbTE hbm) mulr0.
- have hcoeff : p@_m = 0.
    apply/eqP; by rewrite mcoeff_eq0 hsm.
  rewrite hcoeff big1 // => a _.
  rewrite mcoeffZ mcoeffX.
  case ham: (degree_exponent_monomial a == m).
  + move/eqP: ham=> ->.
    by rewrite hcoeff mul0r.
  + by rewrite /= mulr0.
Qed.

Lemma homogeneous_decode_coordinates (p : dhomog 5 F d) :
  homogeneous_decode (homogeneous_coordinates p) = p.
Proof.
apply/val_inj; rewrite /homogeneous_decode /= /homogeneous_decode_poly.
under eq_bigr=> a _ do rewrite /homogeneous_coordinates mxE enum_rankK.
exact: esym (homogeneous_monomial_expansion p).
Qed.

Lemma homogeneous_coordinates_injective : injective homogeneous_coordinates.
Proof. exact: can_inj homogeneous_decode_coordinates. Qed.

Lemma homogeneous_decode_injective : injective homogeneous_decode.
Proof. exact: can_inj homogeneous_coordinates_decode. Qed.

Theorem homogeneous_coordinates_bijective :
  bijective homogeneous_coordinates.
Proof.
exists homogeneous_decode; split.
- exact: homogeneous_decode_coordinates.
- exact: homogeneous_coordinates_decode.
Qed.

Lemma homogeneous_decode_is_linear : linear homogeneous_decode.
Proof.
move=> c v w; apply: homogeneous_coordinates_injective.
by rewrite linearP /= !homogeneous_coordinates_decode.
Qed.

HB.instance Definition homogeneous_decode_linear :=
  GRing.isLinear.Build F 'rV[F]_#|{: MC.degree_exponent d}|
    (dhomog 5 F d) _ homogeneous_decode homogeneous_decode_is_linear.

(** * Compatibility with the honest polynomial left action *)

Definition homogeneous_left_action (s : 'S_5) (p : dhomog 5 F d) :
    dhomog 5 F d :=
  DHomog (IM.mpoly_left_action_homogeneous s (dhomog_is_dhomog p)).

Lemma homogeneous_left_action_val s (p : dhomog 5 F d) :
  (homogeneous_left_action s p : {mpoly F[5]}) =
    IM.mpoly_left_action s p.
Proof. reflexivity. Qed.

Lemma homogeneous_left_action_is_linear s :
  linear (homogeneous_left_action s).
Proof.
move=> c p q; apply/val_inj.
by rewrite /homogeneous_left_action /=
  IM.mpoly_left_actionD IM.mpoly_left_actionZ.
Qed.

HB.instance Definition homogeneous_left_action_linear s :=
  GRing.isLinear.Build F (dhomog 5 F d) (dhomog 5 F d) _
    (homogeneous_left_action s) (homogeneous_left_action_is_linear s).

Lemma homogeneous_left_action1 p : homogeneous_left_action 1 p = p.
Proof.
apply/val_inj.
exact: IM.mpoly_left_action1 p.
Qed.

Lemma homogeneous_left_actionM s t p :
  homogeneous_left_action (s * t) p =
    homogeneous_left_action s (homogeneous_left_action t p).
Proof.
apply/val_inj.
exact: IM.mpoly_left_actionM s t p.
Qed.

Lemma homogeneous_left_action_coefficient
    (s : 'S_5) (p : dhomog 5 F d) (a : MC.degree_exponent d) :
  (homogeneous_left_action s p)@_(degree_exponent_monomial a) =
    p@_(degree_exponent_monomial (MC.act_degree_exponent s a)).
Proof.
rewrite /homogeneous_left_action /= /IM.mpoly_left_action mcoeff_sym.
by rewrite degree_exponent_monomial_act.
Qed.

(** The central coordinate-action theorem.  The transpose in the matrix
    definition is essential: multiplying a row vector by it reads the old
    coordinate at [act_degree_exponent s a], which is exactly the preceding
    coefficient formula for [msym s^-1]. *)
Theorem homogeneous_coordinates_action (s : 'S_5) (p : dhomog 5 F d) :
  homogeneous_coordinates (homogeneous_left_action s p) =
    homogeneous_coordinates p *m MC.homogeneous_monomial_matrix F s d.
Proof.
rewrite /MC.homogeneous_monomial_matrix tr_perm_mx -col_permE.
apply/matrixP=> i j.
rewrite /homogeneous_coordinates !mxE
  homogeneous_left_action_coefficient
  MC.degree_exponent_permE enum_rankK.
reflexivity.
Qed.

Corollary homogeneous_coordinates_fixedE
    (s : 'S_5) (p : dhomog 5 F d) :
  homogeneous_left_action s p = p <->
    homogeneous_coordinates p *m
      MC.homogeneous_monomial_matrix F s d = homogeneous_coordinates p.
Proof.
split.
- move=> hp.
  have hcoordinates := congr1 homogeneous_coordinates hp.
  rewrite homogeneous_coordinates_action in hcoordinates.
  exact: hcoordinates.
- move=> hcoordinates; apply: homogeneous_coordinates_injective.
  by rewrite homogeneous_coordinates_action.
Qed.

Corollary homogeneous_decode_matrix_action
    (s : 'S_5) (v : 'rV[F]_#|{: MC.degree_exponent d}|) :
  homogeneous_decode
      (v *m MC.homogeneous_monomial_matrix F s d) =
    homogeneous_left_action s (homogeneous_decode v).
Proof.
apply: homogeneous_coordinates_injective.
by rewrite homogeneous_coordinates_decode
  homogeneous_coordinates_action homogeneous_coordinates_decode.
Qed.

End HomogeneousCoordinates.

End PolynomialFormulasLazardInvariantMolienPolynomialCoordinates.
