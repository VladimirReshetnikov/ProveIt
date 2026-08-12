From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticRootAlternateRecovery
  LazardQuinticRootBranchEquivariance
  LazardQuinticCoherentAlternateProjectionBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root-level branch equivariance of the corrected alternate projection.
    This connects the convention-safe linear algebra to the actual Fourier
    fifth-power orbit without asserting the still-separate coefficient-field
    descent step. *)
Module PolynomialFormulasLazardQuinticRootCoherentAlternateEquivariance.

Import GRing.Theory.
Local Open Scope ring_scope.

Module P := PolynomialFormulasLazardQuinticProjection.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RA := PolynomialFormulasLazardQuinticRootAlternateRecovery.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.
Module CB :=
  PolynomialFormulasLazardQuinticCoherentAlternateProjectionBridge.

Section Equivariance.

Variable F : fieldType.

Lemma lazard_root_fourier_fifth_orbitE
    (omega : F) (roots : 5.-tuple F) (i : 'I_4) :
  RP.lazard_root_fourier_fifth_orbit omega roots i =
    BE.lazard_root_fourier_orbit omega roots i ^+ 5.
Proof.
case: i=> [[|[|[|[|j]]]] hj] //=;
by rewrite /RP.lazard_root_fourier_fifth_orbit
  /BE.lazard_root_fourier_orbit /P.p0 /P.p1 /P.p2 /P.p3.
Qed.

(** The fifth powers inherit exactly the same source permutation as the
    unpowered Fourier orbit. *)
Lemma lazard_root_fourier_fifth_orbit_roots_for_branch
    (omega : F) (roots : 5.-tuple F) (branch : Q.lazard_sign_branch)
    (i : 'I_4) :
  RP.lazard_root_fourier_fifth_orbit omega
      (BE.lazard_roots_for_branch roots branch) i =
    CB.lazard_coherent_source_for_branch
      (RP.lazard_root_fourier_fifth_orbit omega roots) branch i.
Proof.
rewrite !lazard_root_fourier_fifth_orbitE
  BE.lazard_root_fourier_orbit_roots_for_branch.
case: branch;
case: i=> [[|[|[|[|j]]]] hj] //=;
by rewrite /CB.lazard_coherent_source_for_branch
  /BE.lazard_source_for_branch
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_negate_source
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_source
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_negate_source
  /P.p0 /P.p1 /P.p2 /P.p3.
Qed.

(** All four corrected root projection values are unchanged by every
    coherent root reordering. *)
Theorem lazard_root_coherent_alternate_projection_values_roots_for_branch
    (omega : F) (roots : 5.-tuple F) (branch : Q.lazard_sign_branch)
    (i : 'I_4) :
  RA.lazard_root_coherent_alternate_projection_values omega
      (BE.lazard_roots_for_branch roots branch) i =
    RA.lazard_root_coherent_alternate_projection_values omega roots i.
Proof.
change
  C.lazard_coherent_alternate_projections
    (Q.lazard_epsilon
      (BE.lazard_root_quadratic_triple omega
        (BE.lazard_roots_for_branch roots branch)))
    (Q.lazard_t
      (BE.lazard_root_quadratic_triple omega
        (BE.lazard_roots_for_branch roots branch)))
    (Q.lazard_u
      (BE.lazard_root_quadratic_triple omega
        (BE.lazard_roots_for_branch roots branch)))
    (RP.lazard_root_fourier_fifth_orbit omega
      (BE.lazard_roots_for_branch roots branch)) i =
  C.lazard_coherent_alternate_projections
    (Q.lazard_epsilon (BE.lazard_root_quadratic_triple omega roots))
    (Q.lazard_t (BE.lazard_root_quadratic_triple omega roots))
    (Q.lazard_u (BE.lazard_root_quadratic_triple omega roots))
    (RP.lazard_root_fourier_fifth_orbit omega roots) i.
rewrite BE.lazard_root_quadratic_triple_roots_for_branch
  lazard_root_fourier_fifth_orbit_roots_for_branch.
exact: CB.lazard_coherent_alternate_projections_branch.
Qed.

End Equivariance.

Print Assumptions lazard_root_fourier_fifth_orbit_roots_for_branch.
Print Assumptions
  lazard_root_coherent_alternate_projection_values_roots_for_branch.

End PolynomialFormulasLazardQuinticRootCoherentAlternateEquivariance.
