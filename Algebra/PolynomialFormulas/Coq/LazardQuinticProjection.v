From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The four-dimensional linear algebra behind Lazard's standard and
    alternate projections.  This file deliberately keeps the hypotheses on
    characteristic visible: recovery needs characteristic different from
    two, while the determinant identities are polynomial identities over an
    arbitrary field. *)
Module PolynomialFormulasLazardQuinticProjection.

Import GRing.Theory.
Local Open Scope ring_scope.

Section Projection.

Variable F : fieldType.

Definition p0 : 'I_4 := @ord0 3.
Definition p1 : 'I_4 := lift (@ord0 3) (@ord0 2).
Definition p2 : 'I_4 := lift (@ord0 3) (lift (@ord0 2) (@ord0 1)).
Definition p3 : 'I_4 :=
  lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0))).

(** Lazard's matrix for [I1,I2,I3,I4]. *)
Definition lazard_standard_projection_matrix (epsilon t u : F) : 'M[F]_4 :=
  \matrix_(i < 4, j < 4)
    (nth [::]
      [:: [:: 1; 1; 1; 1];
          [:: epsilon; - epsilon; epsilon; - epsilon];
          [:: t; - u; - t; u];
          [:: u; t; - u; - t]] i)`_j.

(** Lazard's matrix for [I1,I2,I3,I4'], used in the exceptional standard
    denominator case. *)
Definition lazard_alternate_projection_matrix (epsilon t u : F) : 'M[F]_4 :=
  \matrix_(i < 4, j < 4)
    (nth [::]
      [:: [:: 1; 1; 1; 1];
          [:: epsilon; - epsilon; epsilon; - epsilon];
          [:: t; - u; - t; u];
          [:: epsilon * (t + 2%:R * u);
              epsilon * (u - 2%:R * t);
              - epsilon * (t + 2%:R * u);
              - epsilon * (u - 2%:R * t)]] i)`_j.

Definition lazard_alternate_denominator (t u : F) : F :=
  t * u - t ^+ 2 + u ^+ 2.

Definition lazard_standard_projections
    (epsilon t u : F) (source : 'I_4 -> F) : 'I_4 -> F :=
  fun i => \sum_(j : 'I_4)
    lazard_standard_projection_matrix epsilon t u i j * source j.

Definition lazard_alternate_projections
    (epsilon t u : F) (source : 'I_4 -> F) : 'I_4 -> F :=
  fun i => \sum_(j : 'I_4)
    lazard_alternate_projection_matrix epsilon t u i j * source j.

Definition lazard_standard_recover
    (epsilon t u : F) (projections : 'I_4 -> F) : F :=
  projections p0 / 4%:R + projections p1 / (4%:R * epsilon) +
    (t * projections p2 + u * projections p3) /
      (2%:R * (t ^+ 2 + u ^+ 2)).

Definition lazard_alternate_recover
    (epsilon t u : F) (projections : 'I_4 -> F) : F :=
  projections p0 / 4%:R + projections p1 / (4%:R * epsilon) +
    (epsilon * (u - 2%:R * t) * projections p2 +
       u * projections p3) /
      (4%:R * epsilon * lazard_alternate_denominator t u).

Lemma lazard_sum_ord4 (f : 'I_4 -> F) :
  \sum_(i : 'I_4) f i = f p0 + f p1 + f p2 + f p3.
Proof.
rewrite !big_ord_recl !big_ord0.
by rewrite addr0 !addrA.
Qed.

(** The eight coordinate equations are retained as named lemmas, so later
    developments can use the projection relations without unfolding a
    matrix product. *)
Lemma lazard_standard_projection0 epsilon t u source :
  lazard_standard_projections epsilon t u source p0 =
    source p0 + source p1 + source p2 + source p3.
Proof.
rewrite /lazard_standard_projections lazard_sum_ord4
  /lazard_standard_projection_matrix !mxE /=.
by rewrite !mul1r.
Qed.

Lemma lazard_standard_projection1 epsilon t u source :
  lazard_standard_projections epsilon t u source p1 =
    epsilon * source p0 - epsilon * source p1 +
      epsilon * source p2 - epsilon * source p3.
Proof.
rewrite /lazard_standard_projections lazard_sum_ord4
  /lazard_standard_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_standard_projection2 epsilon t u source :
  lazard_standard_projections epsilon t u source p2 =
    t * source p0 - u * source p1 - t * source p2 + u * source p3.
Proof.
rewrite /lazard_standard_projections lazard_sum_ord4
  /lazard_standard_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_standard_projection3 epsilon t u source :
  lazard_standard_projections epsilon t u source p3 =
    u * source p0 + t * source p1 - u * source p2 - t * source p3.
Proof.
rewrite /lazard_standard_projections lazard_sum_ord4
  /lazard_standard_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_alternate_projection0 epsilon t u source :
  lazard_alternate_projections epsilon t u source p0 =
    source p0 + source p1 + source p2 + source p3.
Proof.
rewrite /lazard_alternate_projections lazard_sum_ord4
  /lazard_alternate_projection_matrix !mxE /=.
by rewrite !mul1r.
Qed.

Lemma lazard_alternate_projection1 epsilon t u source :
  lazard_alternate_projections epsilon t u source p1 =
    epsilon * source p0 - epsilon * source p1 +
      epsilon * source p2 - epsilon * source p3.
Proof.
rewrite /lazard_alternate_projections lazard_sum_ord4
  /lazard_alternate_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_alternate_projection2 epsilon t u source :
  lazard_alternate_projections epsilon t u source p2 =
    t * source p0 - u * source p1 - t * source p2 + u * source p3.
Proof.
rewrite /lazard_alternate_projections lazard_sum_ord4
  /lazard_alternate_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

Lemma lazard_alternate_projection3 epsilon t u source :
  lazard_alternate_projections epsilon t u source p3 =
    epsilon * (t + 2%:R * u) * source p0 +
    epsilon * (u - 2%:R * t) * source p1 -
    epsilon * (t + 2%:R * u) * source p2 -
    epsilon * (u - 2%:R * t) * source p3.
Proof.
rewrite /lazard_alternate_projections lazard_sum_ord4
  /lazard_alternate_projection_matrix !mxE /=.
by rewrite !mulNr.
Qed.

(** Local bridge from MathComp's packed ring operations to Stdlib [ring]. *)
Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma lazard_projection_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_projection_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_projection_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_projection_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_projection_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_projection_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_projection_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
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

Add Ring lazard_projection_ring : lazard_projection_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac lazard_projection_ring :=
  repeat first
    [ rewrite lazard_projection_ring_addE
    | rewrite lazard_projection_ring_mulE
    | rewrite lazard_projection_ring_subE
    | rewrite lazard_projection_ring_oppE
    | rewrite lazard_projection_ring_zeroE
    | rewrite lazard_projection_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_projection_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_projection_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -lazard_projection_two_natrE.
  exact: (@natrD F 2 1).
rewrite -h3.
exact: (@natrD F 3 1).
Qed.

Lemma lazard_projection_eight_natrE :
  (8%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_projection_four_natrE.
have h7 : (7%:R : F) = 4%:R + 1 + 1 + 1.
  rewrite -(@natrD F 4 1) -(@natrD F 5 1).
  exact: (@natrD F 6 1).
rewrite -h7.
exact: (@natrD F 7 1).
Qed.

Lemma lazard_projection_sixteen_natrE :
  (16%:R : F) =
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 +
    1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_projection_eight_natrE.
have h15 : (15%:R : F) =
    8%:R + 1 + 1 + 1 + 1 + 1 + 1 + 1.
  rewrite -(@natrD F 8 1) -(@natrD F 9 1) -(@natrD F 10 1)
    -(@natrD F 11 1) -(@natrD F 12 1) -(@natrD F 13 1).
  exact: (@natrD F 14 1).
rewrite -h15.
exact: (@natrD F 15 1).
Qed.

Lemma lazard_projection_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

(** The two determinant polynomials from Lazard's Section 5. *)
Theorem lazard_standard_projection_matrix_det epsilon t u :
  \det (lazard_standard_projection_matrix epsilon t u) =
    - 8%:R * epsilon * (t ^+ 2 + u ^+ 2).
Proof.
rewrite /lazard_standard_projection_matrix.
do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl, big_ord0) //= ?mxE //=;
  rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
  rewrite ?(mul1r, mulr1, mulN1r, mul0r, mulr0, addr0) /=;
  do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
rewrite lazard_projection_eight_natrE.
lazard_projection_ring.
Qed.

Theorem lazard_alternate_projection_matrix_det epsilon t u :
  \det (lazard_alternate_projection_matrix epsilon t u) =
    - 16%:R * epsilon ^+ 2 * lazard_alternate_denominator t u.
Proof.
rewrite /lazard_alternate_projection_matrix.
do ?[rewrite (expand_det_row _ ord0) //=;
  rewrite ?(big_ord_recl, big_ord0) //= ?mxE //=;
  rewrite /cofactor /= ?(addn0, add0n, expr0, exprS);
  rewrite ?(mul1r, mulr1, mulN1r, mul0r, mulr0, addr0) /=;
  do ?rewrite [row' _ _]mx11_scalar det_scalar1 !mxE /=].
rewrite /lazard_alternate_denominator !lazard_projection_two_natrE
  lazard_projection_sixteen_natrE !expr2.
lazard_projection_ring.
Qed.

Lemma lazard_projection_four_neq0
    (two_neq0 : (2%:R : F) != 0) : (4%:R : F) != 0.
Proof.
rewrite (@natrM F 2 2).
exact (mulf_neq0 two_neq0 two_neq0).
Qed.

Theorem lazard_standard_projection_matrix_det_neq0 epsilon t u
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (denominator_neq0 : t ^+ 2 + u ^+ 2 != 0) :
  \det (lazard_standard_projection_matrix epsilon t u) != 0.
Proof.
rewrite lazard_standard_projection_matrix_det.
apply: mulf_neq0 (mulf_neq0 _ epsilon_neq0) denominator_neq0.
rewrite oppr_eq0.
have h4 := lazard_projection_four_neq0 two_neq0.
rewrite (@natrM F 4 2).
exact (mulf_neq0 h4 two_neq0).
Qed.

Theorem lazard_alternate_projection_matrix_det_neq0 epsilon t u
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (denominator_neq0 : lazard_alternate_denominator t u != 0) :
  \det (lazard_alternate_projection_matrix epsilon t u) != 0.
Proof.
rewrite lazard_alternate_projection_matrix_det.
apply: mulf_neq0 (mulf_neq0 _ (expf_neq0 2 epsilon_neq0))
  denominator_neq0.
rewrite oppr_eq0 (@natrM F 8 2).
have h4 := lazard_projection_four_neq0 two_neq0.
have h8 : (8%:R : F) != 0.
  rewrite (@natrM F 4 2).
  exact (mulf_neq0 h4 two_neq0).
exact (mulf_neq0 h8 two_neq0).
Qed.

(** The standard formula recovers the first source coordinate.  The three
    hypotheses are precisely the nonzero factors occurring in its
    denominators. *)
Theorem lazard_standard_recover_projections epsilon t u source
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (denominator_neq0 : t ^+ 2 + u ^+ 2 != 0) :
  lazard_standard_recover epsilon t u
      (lazard_standard_projections epsilon t u source) = source p0.
Proof.
have four_neq0 := lazard_projection_four_neq0 two_neq0.
have four_epsilon_neq0 : 4%:R * epsilon != 0 :=
  mulf_neq0 four_neq0 epsilon_neq0.
have two_denominator_neq0 : 2%:R * (t ^+ 2 + u ^+ 2) != 0 :=
  mulf_neq0 two_neq0 denominator_neq0.
have common_neq0 :
    4%:R * epsilon * (2%:R * (t ^+ 2 + u ^+ 2)) != 0 :=
  mulf_neq0 four_epsilon_neq0 two_denominator_neq0.
apply: (mulfI common_neq0).
rewrite /lazard_standard_recover.
transitivity (
    ((4%:R)^-1 * 4%:R) *
      (epsilon * (2%:R * (t ^+ 2 + u ^+ 2))) *
      lazard_standard_projections epsilon t u source p0 +
    (((4%:R * epsilon)^-1 * (4%:R * epsilon)) *
      (2%:R * (t ^+ 2 + u ^+ 2)) *
      lazard_standard_projections epsilon t u source p1) +
    (((2%:R * (t ^+ 2 + u ^+ 2))^-1 *
        (2%:R * (t ^+ 2 + u ^+ 2))) *
      (4%:R * epsilon) *
      (t * lazard_standard_projections epsilon t u source p2 +
       u * lazard_standard_projections epsilon t u source p3))).
- rewrite !lazard_projection_two_natrE !lazard_projection_four_natrE
    !lazard_projection_expr2.
  lazard_projection_ring.
- rewrite (mulVf four_neq0) (mulVf four_epsilon_neq0)
    (mulVf two_denominator_neq0) !mul1r.
  rewrite lazard_standard_projection0 lazard_standard_projection1
    lazard_standard_projection2 lazard_standard_projection3.
  rewrite lazard_projection_two_natrE lazard_projection_four_natrE
    !lazard_projection_expr2.
  lazard_projection_ring.
Qed.

(** The alternate formula recovers the first source coordinate even when
    [t^2+u^2] vanishes, provided its own determinant factor does not. *)
Theorem lazard_alternate_recover_projections epsilon t u source
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (denominator_neq0 : lazard_alternate_denominator t u != 0) :
  lazard_alternate_recover epsilon t u
      (lazard_alternate_projections epsilon t u source) = source p0.
Proof.
have four_neq0 := lazard_projection_four_neq0 two_neq0.
have four_epsilon_neq0 : 4%:R * epsilon != 0 :=
  mulf_neq0 four_neq0 epsilon_neq0.
have common_neq0 :
    4%:R * epsilon * lazard_alternate_denominator t u != 0 :=
  mulf_neq0 four_epsilon_neq0 denominator_neq0.
apply: (mulfI common_neq0).
rewrite /lazard_alternate_recover.
transitivity (
    ((4%:R)^-1 * 4%:R) *
      (epsilon * lazard_alternate_denominator t u) *
      lazard_alternate_projections epsilon t u source p0 +
    (((4%:R * epsilon)^-1 * (4%:R * epsilon)) *
      lazard_alternate_denominator t u *
      lazard_alternate_projections epsilon t u source p1) +
    (((4%:R * epsilon * lazard_alternate_denominator t u)^-1 *
        (4%:R * epsilon * lazard_alternate_denominator t u)) *
      (epsilon * (u - 2%:R * t) *
         lazard_alternate_projections epsilon t u source p2 +
       u * lazard_alternate_projections epsilon t u source p3))).
- rewrite !lazard_projection_two_natrE !lazard_projection_four_natrE.
  lazard_projection_ring.
- rewrite (mulVf four_neq0) (mulVf four_epsilon_neq0)
    (mulVf common_neq0) !mul1r.
  rewrite lazard_alternate_projection0 lazard_alternate_projection1
    lazard_alternate_projection2 lazard_alternate_projection3.
  rewrite /lazard_alternate_denominator lazard_projection_two_natrE
    lazard_projection_four_natrE !lazard_projection_expr2.
  lazard_projection_ring.
Qed.

End Projection.

End PolynomialFormulasLazardQuinticProjection.
