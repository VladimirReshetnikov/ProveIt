From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticFourier LazardQuinticRootProjections
  LazardQuinticRootBranchEquivariance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** At least one nonconstant Fourier component of a depressed injective
    root tuple is nonzero.

    This removes the final "choose a nonzero [P1]" certificate from the
    root-side reconstruction.  If all four components vanished, the
    depressed relation would also make the constant Fourier component zero;
    the proved inverse Fourier transform would then force all five roots to
    be zero, contradicting injectivity. *)
Module PolynomialFormulasLazardQuinticRootFourierNonzero.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module LF := PolynomialFormulasLazardQuinticFourier.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.

Local Open Scope ring_scope.

Section FourierNonzero.

Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : 5.-primitive_root omega.

Lemma lazard_fourier_sum_o0 (roots : 5.-tuple F) :
  LF.lazard_fourier_sum omega roots o0 = RP.lazard_root_esymm1 roots.
Proof.
rewrite /LF.lazard_fourier_sum LF.lazard_sum_ord5
  /RP.lazard_root_esymm1 /=.
by rewrite !muln0 !expr0 !mul1r.
Qed.

(** Every coordinate is zero when all five Fourier coordinates are zero. *)
Lemma lazard_roots_zero_of_fourier_sums_zero
    (five_neq0 : (5%:R : F) != 0) (roots : 5.-tuple F)
    (hall : forall k : 'I_5, LF.lazard_fourier_sum omega roots k = 0) :
  forall k : 'I_5, tnth roots k = 0.
Proof.
move=> k.
have hnum : LF.lazard_inverse_fourier_numerator omega roots k = 0.
  rewrite /LF.lazard_inverse_fourier_numerator.
  apply: big1=> j _.
  by rewrite hall mulr0.
have hcoord := @LF.lazard_inverse_fourier_coordinateE
  F omega omega_primitive five_neq0 roots k.
rewrite /LF.lazard_inverse_fourier_coordinate hnum mulr0 in hcoord.
exact: esym hcoord.
Qed.

(** Public nonzero-component theorem in exactly the index order used by the
    four Lazard sign branches. *)
Theorem lazard_exists_nonzero_fourier_component
    (five_neq0 : (5%:R : F) != 0) (roots : 5.-tuple F)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  LF.lazard_fourier_sum omega roots o1 != 0 \/
  LF.lazard_fourier_sum omega roots o2 != 0 \/
  LF.lazard_fourier_sum omega roots o4 != 0 \/
  LF.lazard_fourier_sum omega roots o3 != 0.
Proof.
case: (eqVneq (LF.lazard_fourier_sum omega roots o1) 0)=> h1;
  last by left.
case: (eqVneq (LF.lazard_fourier_sum omega roots o2) 0)=> h2;
  last by right; left.
case: (eqVneq (LF.lazard_fourier_sum omega roots o4) 0)=> h4;
  last by right; right; left.
case: (eqVneq (LF.lazard_fourier_sum omega roots o3) 0)=> h3;
  last by right; right; right.
have h0 : LF.lazard_fourier_sum omega roots o0 = 0.
  by rewrite lazard_fourier_sum_o0 hsum.
have hall : forall k : 'I_5,
    LF.lazard_fourier_sum omega roots k = 0.
  move=> k.
  case: k=> [[|[|[|[|[|k]]]]] hk].
  - have -> : @Ordinal 5 0 hk = o0 by apply: val_inj.
    exact: h0.
  - have -> : @Ordinal 5 1 hk = o1 by apply: val_inj.
    exact: h1.
  - have -> : @Ordinal 5 2 hk = o2 by apply: val_inj.
    exact: h2.
  - have -> : @Ordinal 5 3 hk = o3 by apply: val_inj.
    exact: h3.
  - have -> : @Ordinal 5 4 hk = o4 by apply: val_inj.
    exact: h4.
  - by move: hk.
have hz0 := lazard_roots_zero_of_fourier_sums_zero five_neq0 hall o0.
have hz1 := lazard_roots_zero_of_fourier_sums_zero five_neq0 hall o1.
have heq : o0 = o1.
  apply: hroots.
  by rewrite hz0 hz1.
by move: (congr1 val heq).
Qed.

(** The branch representation used by the numerator reconstruction can
    therefore choose a nonzero [P1] without taking it as input.  The first
    branch is the identity; the second moves whichever nonzero component was
    found into the [p0] slot. *)
Theorem lazard_exists_two_branches_with_nonzero_P1
    (five_neq0 : (5%:R : F) != 0) (roots : 5.-tuple F)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  exists first second :
      PolynomialFormulasLazardQuinticQuadratic.lazard_sign_branch,
    BE.lazard_source_for_branch
      (BE.lazard_source_for_branch
        (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0.
Proof.
have hcomponent := lazard_exists_nonzero_fourier_component
  five_neq0 hroots hsum.
exists PolynomialFormulasLazardQuinticQuadratic.LazardBranchBase.
destruct hcomponent as [h1 | [h2 | [h4 | h3]]].
- exists PolynomialFormulasLazardQuinticQuadratic.LazardBranchBase.
  rewrite /BE.lazard_source_for_branch /BE.lazard_root_fourier_orbit
    /p0 /= RP.lazard_root_fourier_P1E.
  exact: h1.
- exists PolynomialFormulasLazardQuinticQuadratic.LazardBranchRotateNegate.
  rewrite /BE.lazard_source_for_branch
    /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_negate_source
    /BE.lazard_root_fourier_orbit /p0 /p1 /=
    (RP.lazard_root_fourier_P2E omega_primitive).
  exact: h2.
- exists PolynomialFormulasLazardQuinticQuadratic.LazardBranchNegateTU.
  rewrite /BE.lazard_source_for_branch
    /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_negate_source
    /BE.lazard_root_fourier_orbit /p0 /p2 /=
    (RP.lazard_root_fourier_P4E omega_primitive).
  exact: h4.
- exists PolynomialFormulasLazardQuinticQuadratic.LazardBranchRotate.
  rewrite /BE.lazard_source_for_branch
    /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_source
    /BE.lazard_root_fourier_orbit /p0 /p3 /=
    (RP.lazard_root_fourier_P3E omega_primitive).
  exact: h3.
Qed.

End FourierNonzero.

End PolynomialFormulasLazardQuinticRootFourierNonzero.
