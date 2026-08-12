From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticProjection LazardQuinticCoherentAlternateProjection
  LazardQuinticQuadratic LazardQuinticQ1ProjectionBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Equivariance of the convention-safe alternate projection under all
    four coherent sign/source branches.  The final lemmas also record why
    the uncorrected Section-5 row cannot simply be reused after replacing
    its [U] by the formula-sign coordinate: it has a nontrivial sign
    character under the multiplier-by-two transformation. *)
Module PolynomialFormulasLazardQuinticCoherentAlternateProjectionBridge.

Import GRing.Theory.
Local Open Scope ring_scope.

Module P := PolynomialFormulasLazardQuinticProjection.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module QB := PolynomialFormulasLazardQuinticQ1ProjectionBridge.

Section Bridge.

Variable F : fieldType.

Definition lazard_coherent_source_for_branch
    (source : 'I_4 -> F) (branch : Q.lazard_sign_branch) : 'I_4 -> F :=
  match branch with
  | Q.LazardBranchBase => source
  | Q.LazardBranchNegateTU => QB.lazard_negate_source source
  | Q.LazardBranchRotate => QB.lazard_rotate_source source
  | Q.LazardBranchRotateNegate => QB.lazard_rotate_negate_source source
  end.

(** Every corrected projection coordinate is fixed when the quadratic
    triple and the four source coordinates are transformed coherently. *)
Theorem lazard_coherent_alternate_projections_branch
    (v : Q.lazard_quadratic_triple F) (source : 'I_4 -> F)
    (branch : Q.lazard_sign_branch) (i : 'I_4) :
  C.lazard_coherent_alternate_projections
      (Q.lazard_epsilon (Q.lazard_branch_triple v branch))
      (Q.lazard_t (Q.lazard_branch_triple v branch))
      (Q.lazard_u (Q.lazard_branch_triple v branch))
      (lazard_coherent_source_for_branch source branch) i =
    C.lazard_coherent_alternate_projections
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v) source i.
Proof.
case: v=> epsilon t u.
case: branch;
case: i=> [[|[|[|[|j]]]] hj] //=;
rewrite /lazard_coherent_source_for_branch
  /Q.lazard_branch_triple
  /QB.lazard_negate_source /QB.lazard_rotate_source
  /QB.lazard_rotate_negate_source
  /C.lazard_coherent_alternate_projections P.lazard_sum_ord4
  /C.lazard_coherent_alternate_projection_matrix
  /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=;
P.lazard_projection_ring.
Qed.

Definition lazard_printed_alternate_character
    (values : 'I_4 -> F) (i : 'I_4) : F :=
  nth 0 [:: values P.p0; values P.p1;
           - values P.p2; - values P.p3] i.

(** With the original Section-5 [U], multiplication by two sends
    [(epsilon,T,U)] to [(-epsilon,-U,T)].  The first two alternate
    projections are fixed and the last two are negated. *)
Theorem lazard_printed_alternate_projections_multiplier_two
    (epsilon t u : F) (source : 'I_4 -> F) (i : 'I_4) :
  P.lazard_alternate_projections (- epsilon) (- u) t
      (QB.lazard_rotate_source source) i =
    lazard_printed_alternate_character
      (P.lazard_alternate_projections epsilon t u source) i.
Proof.
case: i=> [[|[|[|[|j]]]] hj] //=;
rewrite /lazard_printed_alternate_character
  /QB.lazard_rotate_source
  /P.lazard_alternate_projections P.lazard_sum_ord4
  /P.lazard_alternate_projection_matrix
  /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=;
P.lazard_projection_ring.
Qed.

Corollary lazard_printed_alternate_projection3_multiplier_two
    (epsilon t u : F) (source : 'I_4 -> F) :
  P.lazard_alternate_projections (- epsilon) (- u) t
      (QB.lazard_rotate_source source) P.p3 =
    - P.lazard_alternate_projections epsilon t u source P.p3.
Proof.
exact: lazard_printed_alternate_projections_multiplier_two.
Qed.

(** Multiplication by [epsilon] cancels the preceding sign character. *)
Corollary lazard_epsilon_printed_alternate_projection3_multiplier_two
    (epsilon t u : F) (source : 'I_4 -> F) :
  (- epsilon) *
      P.lazard_alternate_projections (- epsilon) (- u) t
        (QB.lazard_rotate_source source) P.p3 =
    epsilon * P.lazard_alternate_projections epsilon t u source P.p3.
Proof.
rewrite lazard_printed_alternate_projection3_multiplier_two.
P.lazard_projection_ring.
Qed.

End Bridge.

Print Assumptions lazard_coherent_alternate_projections_branch.
Print Assumptions lazard_printed_alternate_projections_multiplier_two.
Print Assumptions lazard_epsilon_printed_alternate_projection3_multiplier_two.

End PolynomialFormulasLazardQuinticCoherentAlternateProjectionBridge.
