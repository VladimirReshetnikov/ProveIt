From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticProjection LazardQuinticCoherentAlternateProjection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Denominator-safe alternate recovery from ordered quintic roots.

    The printed Section-7 formula uses the standard fourth projection and
    is only justified in the paper when [-1] is not a square.  The alternate
    fourth projection has a nonzero denominator for every tuple of distinct
    roots.  This module proves the root-level recovery statement without a
    [T^2+U^2 != 0] assumption; expressing the alternate projections over the
    coefficient field is a separate invariant-theory step. *)
Module PolynomialFormulasLazardQuinticRootAlternateRecovery.

Import GRing.Theory.
Local Open Scope ring_scope.

Module R := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module P := PolynomialFormulasLazardQuinticProjection.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.

Section AlternateRecovery.

Variable F : fieldType.

(** Lazard's four alternate projections of the Fourier fifth-power orbit,
    using the original Section-5 [U] convention. *)
Definition lazard_root_alternate_projection_values
    (omega : F) (roots : 5.-tuple F) (j : 'I_4) : F :=
  P.lazard_alternate_projections
    (R.lazard_root_epsilon omega roots)
    (R.lazard_root_T omega roots)
    (R.lazard_root_printed_U omega roots)
    (RP.lazard_root_fourier_fifth_orbit omega roots) j.

(** Corrected alternate projections in the formula-sign [U] convention. *)
Definition lazard_root_coherent_alternate_projection_values
    (omega : F) (roots : 5.-tuple F) (j : 'I_4) : F :=
  C.lazard_coherent_alternate_projections
    (R.lazard_root_epsilon omega roots)
    (R.lazard_root_T omega roots)
    (R.lazard_root_formula_U omega roots)
    (RP.lazard_root_fourier_fifth_orbit omega roots) j.

(** The alternate denominator factors into the two nonzero cyclic
    difference products and the nonzero fifth-root coefficient. *)
Lemma lazard_root_alternate_denominator_identity
    (omega : F) (roots : 5.-tuple F)
    (hcyclo : R.lazard_root_fifth_cyclotomic_value omega = 0) :
  P.lazard_alternate_denominator
      (R.lazard_root_T omega roots)
      (R.lazard_root_printed_U omega roots) =
    5%:R * R.lazard_root_T_prime roots *
      R.lazard_root_U_prime roots *
      R.lazard_fifth_root_discriminant_factor omega.
Proof.
have hzero :=
  R.lazard_fifth_root_change_relation_of_cyclotomic hcyclo.
have hmixed :=
  R.lazard_fifth_root_change_mixed_relation_of_cyclotomic hcyclo.
have hid :
    P.lazard_alternate_denominator
        (R.lazard_root_T omega roots)
        (R.lazard_root_printed_U omega roots) =
      (R.lazard_root_T_prime roots ^+ 2 -
          R.lazard_root_U_prime roots ^+ 2) *
        (R.lazard_fifth_root_B omega ^+ 2 +
          R.lazard_fifth_root_A omega * R.lazard_fifth_root_B omega -
          R.lazard_fifth_root_A omega ^+ 2) +
      (R.lazard_root_T_prime roots * R.lazard_root_U_prime roots) *
        (R.lazard_fifth_root_B omega ^+ 2 -
          R.lazard_fifth_root_A omega ^+ 2 -
          4%:R * R.lazard_fifth_root_A omega *
            R.lazard_fifth_root_B omega).
  rewrite /P.lazard_alternate_denominator /R.lazard_root_T
    /R.lazard_root_printed_U.
  R.finish_lazard_ring.
rewrite hid hzero hmixed mulr0 add0r.
R.finish_lazard_ring.
Qed.

Lemma lazard_fifth_root_discriminant_factor_neq0
    (omega : F)
    (hcyclo : R.lazard_root_fifth_cyclotomic_value omega = 0)
    (five_neq0 : (5%:R : F) != 0) :
  R.lazard_fifth_root_discriminant_factor omega != 0.
Proof.
apply/eqP=> hzero.
have hsquare :=
  R.lazard_fifth_root_discriminant_factor_sq_of_cyclotomic hcyclo.
move: five_neq0.
by rewrite -hsquare hzero expr0 eqxx.
Qed.

Lemma lazard_root_alternate_denominator_neq0
    (omega : F) (roots : 5.-tuple F)
    (hcyclo : R.lazard_root_fifth_cyclotomic_value omega = 0)
    (five_neq0 : (5%:R : F) != 0)
    (hroots : injective (tnth roots)) :
  P.lazard_alternate_denominator
      (R.lazard_root_T omega roots)
      (R.lazard_root_printed_U omega roots) != 0.
Proof.
rewrite (lazard_root_alternate_denominator_identity hcyclo).
exact: mulf_neq0
  (mulf_neq0
    (mulf_neq0 five_neq0 (R.lazard_root_T_prime_neq0 hroots))
    (R.lazard_root_U_prime_neq0 hroots))
  (lazard_fifth_root_discriminant_factor_neq0 hcyclo five_neq0).
Qed.

(** In formula-sign coordinates the corrected denominator is the negative
    of the already proved Section-5 denominator. *)
Lemma lazard_root_coherent_alternate_denominator_neq0
    (omega : F) (roots : 5.-tuple F)
    (hcyclo : R.lazard_root_fifth_cyclotomic_value omega = 0)
    (five_neq0 : (5%:R : F) != 0)
    (hroots : injective (tnth roots)) :
  C.lazard_coherent_alternate_denominator
      (R.lazard_root_T omega roots)
      (R.lazard_root_formula_U omega roots) != 0.
Proof.
rewrite C.lazard_coherent_alternate_denominator_printed_U
  /R.lazard_root_formula_U opprK oppr_eq0.
exact: lazard_root_alternate_denominator_neq0 hcyclo five_neq0 hroots.
Qed.

(** The convention-safe system recovers the same actual fifth power, with
    no standard-denominator hypothesis. *)
Theorem lazard_root_coherent_alternate_recover_fourier_P1_fifth
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (hroots : injective (tnth roots))
    (hepsilon : R.lazard_root_epsilon omega roots != 0) :
  C.lazard_coherent_alternate_recover
      (R.lazard_root_epsilon omega roots)
      (R.lazard_root_T omega roots)
      (R.lazard_root_formula_U omega roots)
      (lazard_root_coherent_alternate_projection_values omega roots) =
    RP.lazard_root_fourier_P1 omega roots ^+ 5.
Proof.
have hcyclo := R.lazard_primitive_fifth_root_cyclotomic omega_primitive.
have hden := lazard_root_coherent_alternate_denominator_neq0
  hcyclo five_neq0 hroots.
rewrite /lazard_root_coherent_alternate_projection_values
  (C.lazard_coherent_alternate_recover_projections
    two_neq0 hepsilon hden).
exact: RP.lazard_root_fourier_fifth_orbit_p0.
Qed.

(** The alternate system recovers the actual fifth power of [P1] for every
    ordered tuple of distinct roots. *)
Theorem lazard_root_alternate_recover_fourier_P1_fifth
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (hroots : injective (tnth roots))
    (hepsilon : R.lazard_root_epsilon omega roots != 0) :
  P.lazard_alternate_recover
      (R.lazard_root_epsilon omega roots)
      (R.lazard_root_T omega roots)
      (R.lazard_root_printed_U omega roots)
      (lazard_root_alternate_projection_values omega roots) =
    RP.lazard_root_fourier_P1 omega roots ^+ 5.
Proof.
have hcyclo := R.lazard_primitive_fifth_root_cyclotomic omega_primitive.
have hden := lazard_root_alternate_denominator_neq0
  hcyclo five_neq0 hroots.
rewrite /lazard_root_alternate_projection_values
  (P.lazard_alternate_recover_projections two_neq0 hepsilon hden).
exact: RP.lazard_root_fourier_fifth_orbit_p0.
Qed.

End AlternateRecovery.

Print Assumptions lazard_root_alternate_denominator_identity.
Print Assumptions lazard_root_alternate_denominator_neq0.
Print Assumptions lazard_root_alternate_recover_fourier_P1_fifth.
Print Assumptions lazard_root_coherent_alternate_denominator_neq0.
Print Assumptions lazard_root_coherent_alternate_recover_fourier_P1_fifth.

End PolynomialFormulasLazardQuinticRootAlternateRecovery.
