From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0.
From PolynomialFormulas Require Import
  LazardSection5DegreeFiveRelativeResolvents
  LazardQuinticRationalDeterminantTransport
  LazardQuinticRootExtensionTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Arbitrary-rational Section-5 relative resolvents

    The first Coq paper-facing epsilon endpoint used the integer-coded
    quintic consumed by the executable pipeline.  This module closes the
    coefficient-scope gap for an arbitrary rational monic depressed
    irreducible quintic.

    The existing rational adapter replaces [p(X)] by the integral dilation
    [D^5 p(X / D)] and supplies a complete rescaled root tuple for [p].
    Lazard's epsilon product is homogeneous of degree five in those roots.
    Since [D] is nonzero, the canonical nonvanishing theorem for the
    integral dilation therefore implies nonvanishing on the original root
    tuple.  The literal [D5/C5] and [F20/D5] separability theorems can then
    be applied with no caller-supplied injectivity, epsilon, coset, or
    separability certificate.  As in the paired Lean endpoint, the final
    theorem still takes a primitive fifth root in the chosen ambient field;
    it does not assert that the bare quintic splitting field contains one.
    The last theorem therefore maps the complete tuple to [algC], constructs
    a primitive fifth root there, and gives the unconditional common-field
    specialization. *)
Module PolynomialFormulasLazardSection5DegreeFiveRationalRelativeResolvents.

Import GRing.Theory.
Module S5R := PolynomialFormulasLazardSection5DegreeFiveRelativeResolvents.
Module RT := PolynomialFormulasLazardQuinticRationalDeterminantTransport.
Module RSA := PolynomialFormulasLazardQuinticRationalScalingAdapter.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module ET := PolynomialFormulasLazardQuinticRootExtensionTransport.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.

Local Open Scope ring_scope.
Local Open Scope group_scope.

(** Epsilon is homogeneous of degree five under simultaneous root
    dilation.  This is a derived polynomial identity, not a scaling
    certificate accepted by the rational wrapper. *)
Section EpsilonScaling.

Variable F : fieldType.

Add Ring lazard_section5_rational_epsilon_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_section5_rational_epsilon_ring :=
  lazard_numerator_prepare;
  repeat first [rewrite exprS | rewrite expr0];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_epsilon_product_scale d (roots : 5.-tuple F) :
  RR.lazard_epsilon_product
      (RSA.lazard_scale_quintic_roots d roots) =
    d ^+ 5 * RR.lazard_epsilon_product roots.
Proof.
rewrite /RR.lazard_epsilon_product
  /RSA.lazard_scale_quintic_roots !tnth_mktuple.
finish_lazard_section5_rational_epsilon_ring.
Qed.

Lemma lazard_root_epsilon_scale omega d (roots : 5.-tuple F) :
  RR.lazard_root_epsilon omega
      (RSA.lazard_scale_quintic_roots d roots) =
    d ^+ 5 * RR.lazard_root_epsilon omega roots.
Proof.
rewrite /RR.lazard_root_epsilon lazard_epsilon_product_scale.
finish_lazard_section5_rational_epsilon_ring.
Qed.

End EpsilonScaling.

(** A fixed primitive fifth root in the algebraically closed common ambient
    field used by the premise-free wrapper below. *)
Definition lazard_section5_complex_omega : algC :=
  projT1 (C_prim_root_exists (n := 5) isT).

Lemma lazard_section5_complex_omega_primitive :
  5.-primitive_root lazard_section5_complex_omega.
Proof.
rewrite /lazard_section5_complex_omega.
case: C_prim_root_exists=> z /= hz.
exact: hz.
Qed.

Section ArbitraryRationalDepressedQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_monic : p \is monic.

Let f : QRF.monic_quintic := RSA.lazard_quintic_integer_data p.
Let pD : {poly rat} := RSA.lazard_quintic_scaled_polynomial p.
Let pD_size : size pD = 6%N := CD.size_rational_monic_quintic f.
Let D : rat := (RSA.lazard_quintic_common_denominator p)%:~R.
Let L : splittingFieldType rat := numfield pD.
Let rootsD : 5.-tuple L := @GA.quintic_root_tuple pD pD_size.
Let roots : 5.-tuple L :=
  @RT.lazard_rational_original_roots p p_size p_monic.

Lemma lazard_rational_scaled_irreducible
    (p_irr : irreducible_poly p) : irreducible_poly pD.
Proof.
exact: (proj2 (@RSA.lazard_quintic_scaled_irreducible_iff
  p p_size p_monic)) p_irr.
Qed.

(** The complete rescaled root tuple is duplicate-free.  Injectivity is
    transported from the irreducible integral dilation by cancellation of
    the nonzero inverse denominator. *)
Theorem lazard_rational_original_roots_injective
    (p_irr : irreducible_poly p) : injective (tnth roots).
Proof.
have hpDirr := lazard_rational_scaled_irreducible p_irr.
have hDinv : (in_alg L D)^-1 != 0.
  by rewrite invr_eq0 fmorph_eq0
    RSA.lazard_quintic_common_denominator_cast_neq0.
move=> i j hij.
apply: (@GA.quintic_root_tuple_injective pD pD_size hpDirr).
apply: (mulfI hDinv).
move: hij.
by rewrite /roots /RT.lazard_rational_original_roots
  /RSA.lazard_scale_quintic_roots !tnth_mktuple.
Qed.

Lemma lazard_rational_two_neq0 : (2%:R : L) != 0.
Proof.
by rewrite -[2%:R](rmorph_nat
  (char0_ratr (char_numfield pD)) 2) fmorph_eq0.
Qed.

(** Epsilon nonvanishing for the original arbitrary-rational root tuple.
    Irreducibility and depression are the only substantive hypotheses;
    canonical nonvanishing is transported back through the proved degree-
    five homogeneity identity. *)
Theorem lazard_rational_monic_depressed_root_epsilon_neq0
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  RR.lazard_root_epsilon omega roots != 0.
Proof.
have hpDirr := lazard_rational_scaled_irreducible p_irr.
have hcanonical_depressed : @CE.lazard_canonical_quintic_depressed f :=
  @RSA.lazard_quintic_integer_data_canonical_depressed
    p p_size p_monic p_depressed.
have hepsilonD : RR.lazard_root_epsilon omega rootsD != 0.
  rewrite -(@RT.lazard_canonical_selected_roots_ord0E
    p p_size p_monic).
  exact: (@CE.lazard_selected_root_epsilon_neq0
    f hpDirr hcanonical_depressed ord0 omega omega_primitive).
apply/eqP=> hepsilon0.
move: hepsilonD.
rewrite -(@RT.lazard_rational_scale_original_rootsE
    p p_size p_monic)
  lazard_root_epsilon_scale hepsilon0 mulr0 eqxx.
Qed.

(** The primitive-root-independent epsilon product is already nonzero on
    the original rational root tuple.  This is the form that transports to
    an arbitrary common overfield. *)
Theorem lazard_rational_monic_depressed_epsilon_product_neq0
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  RR.lazard_epsilon_product roots != 0.
Proof.
have hpDirr := lazard_rational_scaled_irreducible p_irr.
have hcanonical_depressed : @CE.lazard_canonical_quintic_depressed f :=
  @RSA.lazard_quintic_integer_data_canonical_depressed
    p p_size p_monic p_depressed.
have hepsilonD : RR.lazard_epsilon_product rootsD != 0.
  rewrite -(@RT.lazard_canonical_selected_roots_ord0E
    p p_size p_monic).
  exact: (@CE.lazard_selected_epsilon_product_neq0
    f hpDirr hcanonical_depressed ord0).
apply/eqP=> hepsilon0.
move: hepsilonD.
rewrite -(@RT.lazard_rational_scale_original_rootsE
    p p_size p_monic)
  lazard_epsilon_product_scale hepsilon0 mulr0 eqxx.
Qed.

Theorem lazard_rational_monic_root_T_prime_C5_D5_relative_resolvent_separable
    (p_irr : irreducible_poly p) :
  separable_poly (@S5R.lazard_C5_D5_T_relative_resolvent L roots).
Proof.
apply: S5R.lazard_root_T_prime_C5_D5_relative_resolvent_separable.
- exact: lazard_rational_original_roots_injective p_irr.
- exact: lazard_rational_two_neq0.
Qed.

Theorem lazard_rational_monic_root_U_prime_C5_D5_relative_resolvent_separable
    (p_irr : irreducible_poly p) :
  separable_poly (@S5R.lazard_C5_D5_U_relative_resolvent L roots).
Proof.
apply: S5R.lazard_root_U_prime_C5_D5_relative_resolvent_separable.
- exact: lazard_rational_original_roots_injective p_irr.
- exact: lazard_rational_two_neq0.
Qed.

Theorem lazard_rational_monic_depressed_root_epsilon_D5_F20_relative_resolvent_separable
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  separable_poly
    (@S5R.lazard_D5_F20_epsilon_relative_resolvent L omega roots).
Proof.
apply: S5R.lazard_root_epsilon_D5_F20_relative_resolvent_separable.
- exact: lazard_rational_monic_depressed_root_epsilon_neq0
    p_irr p_depressed omega_primitive.
- exact: lazard_rational_two_neq0.
Qed.

(** All three literal degree-five relative orbit products on one complete
    root tuple for the caller's arbitrary rational monic depressed
    irreducible quintic.  No nonvanishing or separability premise remains. *)
Theorem lazard_rational_monic_depressed_section5_degree_five_relative_resolvents_separable
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  separable_poly
      (@S5R.lazard_C5_D5_T_relative_resolvent L roots) /\
  separable_poly
      (@S5R.lazard_C5_D5_U_relative_resolvent L roots) /\
  separable_poly
      (@S5R.lazard_D5_F20_epsilon_relative_resolvent L omega roots).
Proof.
split.
- exact: lazard_rational_monic_root_T_prime_C5_D5_relative_resolvent_separable
    p_irr.
- split.
  + exact: lazard_rational_monic_root_U_prime_C5_D5_relative_resolvent_separable
      p_irr.
  + exact:
      lazard_rational_monic_depressed_root_epsilon_D5_F20_relative_resolvent_separable
        p_irr p_depressed omega_primitive.
Qed.

(** ** Premise-free common algebraically closed ambient field *)

Let iota : {rmorphism L -> algC} := numfield_inC pD.

Definition lazard_rational_complex_roots : 5.-tuple algC :=
  map_tuple iota roots.

Theorem lazard_rational_complex_roots_injective
    (p_irr : irreducible_poly p) :
  injective (tnth lazard_rational_complex_roots).
Proof.
exact: ET.lazard_extension_map_tuple_injective iota
  (lazard_rational_original_roots_injective p_irr).
Qed.

Theorem lazard_rational_monic_depressed_complex_root_epsilon_neq0
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  RR.lazard_root_epsilon lazard_section5_complex_omega
      lazard_rational_complex_roots != 0.
Proof.
change (RP.lazard_root_epsilon lazard_section5_complex_omega
  (map_tuple iota roots) != 0).
exact: ET.lazard_extension_mapped_root_epsilon_neq0 iota
  (by rewrite pnatr_eq0)
  (lazard_rational_monic_depressed_epsilon_product_neq0
    p_irr p_depressed)
  lazard_section5_complex_omega_primitive.
Qed.

(** Nonvacuous paper-facing existence package.  Both the complete quintic
    root tuple and a primitive fifth root live in [algC], so no cyclotomic
    containment premise remains. *)
Theorem lazard_rational_monic_depressed_section5_degree_five_relative_resolvents_separable_over_algC
    (p_irr : irreducible_poly p)
    (p_depressed : RSA.lazard_rational_quintic_depressed p) :
  separable_poly
      (@S5R.lazard_C5_D5_T_relative_resolvent algC
        lazard_rational_complex_roots) /\
  separable_poly
      (@S5R.lazard_C5_D5_U_relative_resolvent algC
        lazard_rational_complex_roots) /\
  separable_poly
      (@S5R.lazard_D5_F20_epsilon_relative_resolvent algC
        lazard_section5_complex_omega lazard_rational_complex_roots).
Proof.
have hroots := lazard_rational_complex_roots_injective p_irr.
have htwo : (2%:R : algC) != 0 by rewrite pnatr_eq0.
split.
- exact: S5R.lazard_root_T_prime_C5_D5_relative_resolvent_separable
    hroots htwo.
- split.
  + exact: S5R.lazard_root_U_prime_C5_D5_relative_resolvent_separable
      hroots htwo.
  + exact: S5R.lazard_root_epsilon_D5_F20_relative_resolvent_separable
      (lazard_rational_monic_depressed_complex_root_epsilon_neq0
        p_irr p_depressed) htwo.
Qed.

End ArbitraryRationalDepressedQuintic.

End PolynomialFormulasLazardSection5DegreeFiveRationalRelativeResolvents.
