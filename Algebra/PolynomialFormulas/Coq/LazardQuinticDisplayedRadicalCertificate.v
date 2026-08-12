From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From PolynomialFormulas Require Import
  QuinticF20Data LazardOptimality LazardQuinticVieta
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticCertificateRadicalTower LazardQuinticRootFourierRelations
  LazardQuinticRootProjections LazardQuinticRootBranchEquivariance
  LazardQuinticRootInvariantDFG
  LazardQuinticRootRadicalCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Transport the root-origin radical certificate to Lazard's displayed
    coefficient polynomials D, F, and G.

    The root-origin construction uses the shorter root normal forms because
    their power equations are transparent.  [LazardQuinticRootInvariantDFG]
    proves that the printed coefficient polynomials are equal to those
    normal forms on every depressed root tuple.  The theorem below rewrites
    all dependent certificate fields along those equalities and then reuses
    the complete root-origin tower theorem. *)
Module PolynomialFormulasLazardQuinticDisplayedRadicalCertificate.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.

Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module DFG := PolynomialFormulasLazardQuinticRootInvariantDFG.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module V := PolynomialFormulasLazardQuinticVieta.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.

Section DisplayedCertificate.

Variables (F0 : fieldType) (L : fieldExtType F0).

Definition lazard_displayed_root_radical_certificate
    (roots : 5.-tuple L) : Type :=
  @CRT.lazard_radical_certificate F0 L
    (RP.lazard_depressed_of_roots roots)
    (RP.lazard_root_invariants roots)
    (DFG.lazard_invariant_D (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots))
    (DFG.lazard_invariant_F (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots))
    (DFG.lazard_invariant_G (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots))
    (RRC.lazard_root_H roots) (RRC.lazard_root_I roots)
    (RRC.lazard_root_J roots) (RRC.lazard_root_K roots).

Definition lazard_displayed_root_radical_invariant_data_in
    (B : {subfield L}) (roots : 5.-tuple L) : Prop :=
  @CRT.lazard_radical_invariant_data_in F0 L B
    (RP.lazard_depressed_of_roots roots)
    (RP.lazard_root_invariants roots)
    (DFG.lazard_invariant_D (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots))
    (DFG.lazard_invariant_F (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots))
    (DFG.lazard_invariant_G (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots))
    (RRC.lazard_root_H roots) (RRC.lazard_root_I roots)
    (RRC.lazard_root_J roots) (RRC.lazard_root_K roots).

(** The root-normal-form membership package transports to the displayed
    coefficient formulas with no additional membership premise. *)
Lemma lazard_displayed_root_radical_invariant_data_of_root
    (B : {subfield L}) (roots : 5.-tuple L)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  RRC.lazard_root_radical_invariant_data_in B roots ->
  lazard_displayed_root_radical_invariant_data_in B roots.
Proof.
rewrite /RRC.lazard_root_radical_invariant_data_in
  /lazard_displayed_root_radical_invariant_data_in.
rewrite (DFG.lazard_root_invariant_D_eq hsum)
  (DFG.lazard_root_invariant_F_eq hsum)
  (DFG.lazard_root_invariant_G_eq hsum).
exact: id.
Qed.

Definition lazard_displayed_root_certificate_field
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (d : lazard_displayed_root_radical_certificate roots) : {subfield L} :=
  CRT.lazard_certificate_field_with_root B d omega.

Definition lazard_displayed_root_certificate_output
    (omega : L) (roots : 5.-tuple L)
    (d : lazard_displayed_root_radical_certificate roots)
    (k : 'I_5) : L :=
  V.lazard_inverse_fourier_output omega
    (CRT.lazard_certificate_p1 d)
    (FN.lazard_fourier_P2_formula
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      (CRT.lazard_certificate_chosen d) (CRT.lazard_certificate_p1 d))
    (FN.lazard_fourier_P3_formula
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      (CRT.lazard_certificate_chosen d) (CRT.lazard_certificate_p1 d))
    (FN.lazard_fourier_P4_formula
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
      (CRT.lazard_certificate_chosen d) (CRT.lazard_certificate_p1 d)) k.

(** End-to-end root-origin tower stated with the displayed D/F/G
    coefficient polynomials.  No equality certificate is an input: the
    three dependent transports are the checked reduction theorems. *)
Theorem lazard_exists_displayed_root_radical_tower_complete
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 :
      FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) != 0)
    (hdata : lazard_displayed_root_radical_invariant_data_in B roots)
    (hnum : RRC.lazard_root_fourier_numerator_data_in B roots) :
  exists (first second :
      Q.lazard_sign_branch)
      (d : lazard_displayed_root_radical_certificate roots),
    CRT.lazard_certificate_p1 d != 0 /\
    @PolynomialFormulasLazardOptimality.radical_extension F0 L B
      (lazard_displayed_root_certificate_field B omega roots d) /\
    (forall k : 'I_5,
      lazard_displayed_root_certificate_output omega roots d k \in
        lazard_displayed_root_certificate_field B omega roots d) /\
    (forall k : 'I_5,
      lazard_displayed_root_certificate_output omega roots d k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k) /\
    (forall z : L,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
        (z - lazard_displayed_root_certificate_output omega roots d o0) *
        (z - lazard_displayed_root_certificate_output omega roots d o1) *
        (z - lazard_displayed_root_certificate_output omega roots d o2) *
        (z - lazard_displayed_root_certificate_output omega roots d o3) *
        (z - lazard_displayed_root_certificate_output omega roots d o4)) /\
    (forall k : 'I_5,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
          (lazard_displayed_root_certificate_output omega roots d k) = 0) /\
    (forall z : L,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 ->
      exists k : 'I_5,
        z = lazard_displayed_root_certificate_output omega roots d k).
Proof.
rewrite /lazard_displayed_root_radical_invariant_data_in in hdata.
rewrite /lazard_displayed_root_radical_certificate
  /lazard_displayed_root_certificate_field
  /lazard_displayed_root_certificate_output.
rewrite (DFG.lazard_root_invariant_D_eq hsum)
  (DFG.lazard_root_invariant_F_eq hsum)
  (DFG.lazard_root_invariant_G_eq hsum) in hdata *.
exact: RRC.lazard_exists_root_radical_tower_complete
  two_neq0 five_neq0 omega_primitive hroots hsum
  root_epsilon_neq0 E_neq0 hdata hnum.
Qed.

End DisplayedCertificate.

End PolynomialFormulasLazardQuinticDisplayedRadicalCertificate.
