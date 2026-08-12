From mathcomp Require Import
  all_ssreflect all_fingroup all_solvable all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  Fin5TransitiveClassification QuinticF20Data QuinticSolvableCriterion
  QuinticGaloisAction QuinticGaloisCriterion QuinticThetaValues
  QuinticThetaGaloisBridge QuinticCanonicalDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The Section 5 classification and the quintic resolvent criterion

    This file packages the two group-theoretic ingredients used together in
    Section 5 of Lazard's paper.  The complete transitive-subgroup list is
    [C5,D5,F20,A5,S5]; the four-item list printed in the paper is complete
    only for proper subgroups.  Solvability, and hence a rational root of the
    scalar Frobenius--Dummit resolvent, detects containment in a conjugate of
    [F20].  The conjugate cannot in general be replaced by the displayed
    standard subgroup without first choosing a compatible root ordering. *)
Module PolynomialFormulasLazardSection5ClassificationResolventBridge.

Module F20 := PolynomialFormulasQuinticF20Data.
Module Class := PolynomialFormulasFin5TransitiveClassification.
Module SolvableCriterion := PolynomialFormulasQuinticSolvableCriterion.
Module QGA := PolynomialFormulasQuinticGaloisAction.
Module GaloisCriterion := PolynomialFormulasQuinticGaloisCriterion.
Module TV := PolynomialFormulasQuinticThetaValues.
Module ThetaCriterion := PolynomialFormulasQuinticThetaGaloisBridge.
Module Canonical := PolynomialFormulasQuinticCanonicalDecision.

Local Open Scope group_scope.
Local Open Scope action_scope.
Local Open Scope ring_scope.

Local Notation S5 := F20.S5.

(** The complete five-class statement and the conjugate-[F20] solvability
    criterion, packaged for an arbitrary transitive subgroup of [S5]. *)
Theorem transitive_classification_and_solvability_criterion
    (G : {group S5}) :
  [transitive G, on [set: 'I_5] | 'P] ->
  (exists! c : Class.transitive_class,
      Class.is_conjugate_to_class G c) /\
  (solvable G <->
    exists x : S5, G \subset (F20.standard_F20 :^ x)).
Proof.
move=> transG; split.
- exact: Class.transitive_subgroup_classification transG.
- exact: SolvableCriterion.solvable_transitive_S5_iff transG.
Qed.

Section IrreducibleQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.
Let roots : 5.-tuple L := @QGA.quintic_root_tuple p p_size.
Let G : {group S5} := @QGA.quintic_galois_image p p_size p_irr.

(** For an irreducible rational quintic, the transitive permutation image is
    classified by the five groups above, and the scalar resolvent has a
    rational root exactly for the three solvable classes, equivalently when
    that image lies in some conjugate of [F20]. *)
Theorem irreducible_quintic_classification_and_resolvent_criterion :
  (exists! c : Class.transitive_class,
      Class.is_conjugate_to_class G c) /\
  ((exists q : rat,
      root (TV.quintic_scalar_resolvent roots) (in_alg L q)) <->
    exists x : S5, G \subset (F20.standard_F20 :^ x)).
Proof.
split.
- exact: Class.transitive_subgroup_classification
    (@QGA.quintic_galois_image_transitive p p_size p_irr).
- rewrite (@ThetaCriterion.quintic_scalar_resolvent_has_rational_root_iff_galois_solvable
    p p_size p_irr
    (@Canonical.canonical_quintic_theta_value_injective p p_size p_irr)).
  exact: (@GaloisCriterion.quintic_galois_solvable_iff_conjugate_F20
    p p_size p_irr).
Qed.

End IrreducibleQuintic.

End PolynomialFormulasLazardSection5ClassificationResolventBridge.
