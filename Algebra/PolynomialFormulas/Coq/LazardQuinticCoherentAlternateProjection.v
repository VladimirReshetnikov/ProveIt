From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticProjection LazardQuinticRootRadicals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A convention-safe version of Lazard's alternate projection.

    The explicit formula uses [U = - U_printed], whereas the alternate row
    in Section 5 is written with [U_printed].  Substituting signs into that
    row without changing its character is not equivariant under the
    multiplier-by-two generator.  The fourth row below is the coherent
    row with parameters [(a,b)=(-1,2)]:

      epsilon * [-T+2U, -2T-U, T-2U, 2T+U].

    Its determinant is

      16 epsilon^2 (T^2 + T U - U^2),

    and the displayed inverse recovers the first source coordinate.  These
    are polynomial/field identities; root-level nonvanishing and descent are
    kept in the subsequent modules. *)
Module PolynomialFormulasLazardQuinticCoherentAlternateProjection.

Import GRing.Theory.
Local Open Scope ring_scope.

Module P := PolynomialFormulasLazardQuinticProjection.
Module R := PolynomialFormulasLazardQuinticRootRadicals.

Section Projection.

Variable F : fieldType.

Definition lazard_coherent_alternate_projection_matrix
    (epsilon t u : F) : 'M[F]_4 :=
  \matrix_(i < 4, j < 4)
    (nth [::]
      [:: [:: 1; 1; 1; 1];
          [:: epsilon; - epsilon; epsilon; - epsilon];
          [:: t; - u; - t; u];
          [:: epsilon * (- t + 2%:R * u);
              epsilon * (- 2%:R * t - u);
              epsilon * (t - 2%:R * u);
              epsilon * (2%:R * t + u)]] i)`_j.

Definition lazard_coherent_alternate_denominator (t u : F) : F :=
  t ^+ 2 + t * u - u ^+ 2.

Definition lazard_coherent_alternate_projections
    (epsilon t u : F) (source : 'I_4 -> F) : 'I_4 -> F :=
  fun i => \sum_(j : 'I_4)
    lazard_coherent_alternate_projection_matrix epsilon t u i j * source j.

Definition lazard_coherent_alternate_recover
    (epsilon t u : F) (projections : 'I_4 -> F) : F :=
  projections P.p0 / 4%:R + projections P.p1 / (4%:R * epsilon) +
    (epsilon * (2%:R * t + u) * projections P.p2 -
       u * projections P.p3) /
      (4%:R * epsilon * lazard_coherent_alternate_denominator t u).

Lemma lazard_coherent_alternate_projection0 epsilon t u source :
  lazard_coherent_alternate_projections epsilon t u source P.p0 =
    source P.p0 + source P.p1 + source P.p2 + source P.p3.
Proof.
rewrite /lazard_coherent_alternate_projections P.lazard_sum_ord4
  /lazard_coherent_alternate_projection_matrix !mxE /=.
by rewrite !mul1r.
Qed.

Lemma lazard_coherent_alternate_projection1 epsilon t u source :
  lazard_coherent_alternate_projections epsilon t u source P.p1 =
    epsilon * source P.p0 - epsilon * source P.p1 +
      epsilon * source P.p2 - epsilon * source P.p3.
Proof.
rewrite /lazard_coherent_alternate_projections P.lazard_sum_ord4
  /lazard_coherent_alternate_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_coherent_alternate_projection2 epsilon t u source :
  lazard_coherent_alternate_projections epsilon t u source P.p2 =
    t * source P.p0 - u * source P.p1 -
      t * source P.p2 + u * source P.p3.
Proof.
rewrite /lazard_coherent_alternate_projections P.lazard_sum_ord4
  /lazard_coherent_alternate_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_coherent_alternate_projection3 epsilon t u source :
  lazard_coherent_alternate_projections epsilon t u source P.p3 =
    epsilon * (- t + 2%:R * u) * source P.p0 +
    epsilon * (- 2%:R * t - u) * source P.p1 +
    epsilon * (t - 2%:R * u) * source P.p2 +
    epsilon * (2%:R * t + u) * source P.p3.
Proof.
rewrite /lazard_coherent_alternate_projections P.lazard_sum_ord4
  /lazard_coherent_alternate_projection_matrix !mxE /=.
reflexivity.
Qed.

(** The corrected projection commutes with every field embedding.  This is
    the functoriality bridge needed when a Galois automorphism acts on both
    the fifth root of unity and the ordered roots. *)
Lemma lazard_coherent_alternate_projections_map
    (E : fieldType) (h : {rmorphism F -> E})
    (epsilon t u : F) (source : 'I_4 -> F) (i : 'I_4) :
  h (lazard_coherent_alternate_projections epsilon t u source i) =
    lazard_coherent_alternate_projections
      (h epsilon) (h t) (h u) (fun j => h (source j)) i.
Proof.
case: i=> [[|[|[|[|i]]]] hi] //=.
- rewrite !lazard_coherent_alternate_projection0 !rmorphD.
  reflexivity.
- rewrite !lazard_coherent_alternate_projection1
    !rmorphD !rmorphB !rmorphM.
  reflexivity.
- rewrite !lazard_coherent_alternate_projection2
    !rmorphD !rmorphB !rmorphM.
  reflexivity.
- rewrite !lazard_coherent_alternate_projection3
    !rmorphD !rmorphB !rmorphM !rmorphN rmorph_nat.
  reflexivity.
Qed.

Lemma lazard_coherent_alternate_denominator_printed_U (t u : F) :
  lazard_coherent_alternate_denominator t u =
    - P.lazard_alternate_denominator t (- u).
Proof.
rewrite /lazard_coherent_alternate_denominator
  /P.lazard_alternate_denominator !P.lazard_projection_expr2.
P.lazard_projection_ring.
Qed.

Theorem lazard_coherent_alternate_projection_matrix_det epsilon t u :
  \det (lazard_coherent_alternate_projection_matrix epsilon t u) =
    16%:R * epsilon ^+ 2 *
      lazard_coherent_alternate_denominator t u.
Proof.
rewrite /lazard_coherent_alternate_projection_matrix.
do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl, big_ord0) //= ?mxE //=;
  rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
  rewrite ?(mul1r, mulr1, mulN1r, mul0r, mulr0, addr0) /=;
  do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
rewrite /lazard_coherent_alternate_denominator
  !P.lazard_projection_two_natrE
  P.lazard_projection_sixteen_natrE !P.lazard_projection_expr2.
P.lazard_projection_ring.
Qed.

Theorem lazard_coherent_alternate_projection_matrix_det_neq0 epsilon t u
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (denominator_neq0 : lazard_coherent_alternate_denominator t u != 0) :
  \det (lazard_coherent_alternate_projection_matrix epsilon t u) != 0.
Proof.
rewrite lazard_coherent_alternate_projection_matrix_det.
apply: mulf_neq0
  (mulf_neq0 _ (expf_neq0 2 epsilon_neq0)) denominator_neq0.
rewrite (@natrM F 8 2).
have four_neq0 := P.lazard_projection_four_neq0 two_neq0.
have eight_neq0 : (8%:R : F) != 0.
  rewrite (@natrM F 4 2).
  exact: mulf_neq0 four_neq0 two_neq0.
exact: mulf_neq0 eight_neq0 two_neq0.
Qed.

Theorem lazard_coherent_alternate_recover_projections epsilon t u source
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (denominator_neq0 : lazard_coherent_alternate_denominator t u != 0) :
  lazard_coherent_alternate_recover epsilon t u
      (lazard_coherent_alternate_projections epsilon t u source) =
    source P.p0.
Proof.
have four_neq0 := P.lazard_projection_four_neq0 two_neq0.
have four_epsilon_neq0 : 4%:R * epsilon != 0 :=
  mulf_neq0 four_neq0 epsilon_neq0.
have common_neq0 :
    4%:R * epsilon * lazard_coherent_alternate_denominator t u != 0 :=
  mulf_neq0 four_epsilon_neq0 denominator_neq0.
apply: (mulfI common_neq0).
rewrite /lazard_coherent_alternate_recover.
transitivity (
    ((4%:R)^-1 * 4%:R) *
      (epsilon * lazard_coherent_alternate_denominator t u) *
      lazard_coherent_alternate_projections epsilon t u source P.p0 +
    (((4%:R * epsilon)^-1 * (4%:R * epsilon)) *
      lazard_coherent_alternate_denominator t u *
      lazard_coherent_alternate_projections epsilon t u source P.p1) +
    (((4%:R * epsilon * lazard_coherent_alternate_denominator t u)^-1 *
        (4%:R * epsilon * lazard_coherent_alternate_denominator t u)) *
      (epsilon * (2%:R * t + u) *
         lazard_coherent_alternate_projections epsilon t u source P.p2 -
       u * lazard_coherent_alternate_projections epsilon t u source P.p3))).
- rewrite !P.lazard_projection_two_natrE
    !P.lazard_projection_four_natrE.
  P.lazard_projection_ring.
- rewrite (mulVf four_neq0) (mulVf four_epsilon_neq0)
    (mulVf common_neq0) !mul1r.
  rewrite lazard_coherent_alternate_projection0
    lazard_coherent_alternate_projection1
    lazard_coherent_alternate_projection2
    lazard_coherent_alternate_projection3.
  rewrite /lazard_coherent_alternate_denominator
    P.lazard_projection_two_natrE P.lazard_projection_four_natrE
    !P.lazard_projection_expr2.
  P.lazard_projection_ring.
Qed.

End Projection.

Print Assumptions lazard_coherent_alternate_denominator_printed_U.
Print Assumptions lazard_coherent_alternate_projection_matrix_det.
Print Assumptions lazard_coherent_alternate_projections_map.
Print Assumptions lazard_coherent_alternate_projection_matrix_det_neq0.
Print Assumptions lazard_coherent_alternate_recover_projections.

End PolynomialFormulasLazardQuinticCoherentAlternateProjection.
