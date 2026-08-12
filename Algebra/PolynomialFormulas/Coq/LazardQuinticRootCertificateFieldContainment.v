From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From PolynomialFormulas Require Import
  LazardQuinticRootRadicalCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Field-containment consequences of a root-origin Lazard certificate.

    The certificate construction identifies its two square-root generators
    and its fifth-root generator with explicit expressions in the ordered
    roots and a primitive fifth root of unity.  Therefore, whenever those
    roots and that root of unity already lie in a subfield [M], the entire
    square/square/fifth-root tower lies in [M].  This file proves that fact
    directly from the displayed definitions; it introduces no formula-field
    profile and no supplied Vieta or membership certificate. *)
Module PolynomialFormulasLazardQuinticRootCertificateFieldContainment.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.

Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module QB := PolynomialFormulasLazardQuinticQ1ProjectionBridge.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module V := PolynomialFormulasLazardQuinticVieta.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.

Section RootCertificateContainment.

Variables (F0 : fieldType) (L : fieldExtType F0).

(** Recursive closure solver for the explicitly displayed root and Fourier
    expressions below. *)
Ltac solve_lazard_root_field_mem :=
  first
    [ assumption
    | apply: rpred_nat
    | apply: rpredN; solve_lazard_root_field_mem
    | apply: rpredD; solve_lazard_root_field_mem
    | apply: rpredB; solve_lazard_root_field_mem
    | apply: rpredM; solve_lazard_root_field_mem
    | apply: rpredX; solve_lazard_root_field_mem ].

Lemma lazard_root_quadratic_triple_in
    (M : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (homega : omega \in M)
    (hroots : forall k : 'I_5, tnth roots k \in M) :
  CRT.lazard_quadratic_triple_in M
    (BE.lazard_root_quadratic_triple omega roots).
Proof.
have h0 := hroots o0.
have h1 := hroots o1.
have h2 := hroots o2.
have h3 := hroots o3.
have h4 := hroots o4.
constructor;
rewrite /BE.lazard_root_quadratic_triple /=.
- rewrite /RP.lazard_root_epsilon /RP.lazard_root_discriminant_factor
    /RP.lazard_root_epsilon_product.
  solve_lazard_root_field_mem.
- rewrite /RR.lazard_root_T /RR.lazard_fifth_root_A
    /RR.lazard_fifth_root_B /RR.lazard_root_T_prime
    /RR.lazard_root_U_prime.
  solve_lazard_root_field_mem.
- rewrite /RR.lazard_root_formula_U /RR.lazard_root_printed_U
    /RR.lazard_fifth_root_A /RR.lazard_fifth_root_B
    /RR.lazard_root_T_prime /RR.lazard_root_U_prime.
  solve_lazard_root_field_mem.
Qed.

Lemma lazard_root_fourier_orbit_mem
    (M : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (homega : omega \in M)
    (hroots : forall k : 'I_5, tnth roots k \in M)
    (j : 'I_4) :
  BE.lazard_root_fourier_orbit omega roots j \in M.
Proof.
have h0 := hroots o0.
have h1 := hroots o1.
have h2 := hroots o2.
have h3 := hroots o3.
have h4 := hroots o4.
case: j=> [[|[|[|[|j]]]] hj] //=;
rewrite /BE.lazard_root_fourier_orbit
  /RP.lazard_root_fourier_P1 /RP.lazard_root_fourier_P2
  /RP.lazard_root_fourier_P3 /RP.lazard_root_fourier_P4 /=;
solve_lazard_root_field_mem.
Qed.

Lemma lazard_source_for_branch_mem
    (M : {subfield L}) (source : 'I_4 -> L)
    (hsource : forall j : 'I_4, source j \in M)
    (branch : Q.lazard_sign_branch) (j : 'I_4) :
  BE.lazard_source_for_branch source branch j \in M.
Proof.
case: branch;
case: j=> [[|[|[|[|j]]]] hj] //=;
rewrite /BE.lazard_source_for_branch /QB.lazard_negate_source
  /QB.lazard_rotate_source /QB.lazard_rotate_negate_source
  /p0 /p1 /p2 /p3 /=;
exact: hsource.
Qed.

Lemma lazard_source_for_two_branches_mem
    (M : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (homega : omega \in M)
    (hroots : forall k : 'I_5, tnth roots k \in M)
    (first second : Q.lazard_sign_branch) (j : 'I_4) :
  BE.lazard_source_for_branch
      (BE.lazard_source_for_branch
        (BE.lazard_root_fourier_orbit omega roots) first) second j \in M.
Proof.
apply: lazard_source_for_branch_mem.
move=> k; apply: lazard_source_for_branch_mem.
exact: lazard_root_fourier_orbit_mem homega hroots.
Qed.

(** The three generators selected by the root-origin construction are all
    in [M], hence so is their generated certificate field. *)
Theorem lazard_root_certificate_generated_field_le
    (B M : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (first second : Q.lazard_sign_branch)
    (d : RRC.lazard_root_radical_certificate roots)
    (hBM : (B <= M)%VS)
    (homega : omega \in M)
    (hroots : forall k : 'I_5, tnth roots k \in M)
    (hinitial : CRT.lazard_certificate_initial d =
      Q.lazard_branch_triple
        (BE.lazard_root_quadratic_triple omega roots) first)
    (hp1 : CRT.lazard_certificate_p1 d =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0) :
  (CRT.lazard_certificate_generated_field B d <= M)%VS.
Proof.
apply: (CRT.lazard_certificate_generated_field_le (d := d) hBM).
- rewrite hinitial.
  have hv := lazard_root_quadratic_triple_in homega hroots.
  exact: CRT.lazard_triple_epsilon_in
    (CRT.lazard_quadratic_triple_in_branch first hv).
- rewrite hinitial.
  have hv := lazard_root_quadratic_triple_in homega hroots.
  exact: CRT.lazard_triple_t_in
    (CRT.lazard_quadratic_triple_in_branch first hv).
- rewrite hp1.
  exact: lazard_source_for_two_branches_mem homega hroots first second p0.
Qed.

(** Both branch reorderings fix index zero, and positive Fourier inversion
    also fixes that coordinate. *)
Lemma lazard_reversed_two_branches_o0
    (roots : 5.-tuple L) first second :
  RFR.lazard_reversed_root_tuple
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second) o0 =
    tnth roots o0.
Proof.
by case: first; case: second;
  rewrite /RFR.lazard_reversed_root_tuple
    /BE.lazard_roots_for_branch /=.
Qed.

(** The zero-index displayed formula is the distinguished input root and
    belongs to the certificate field before adjoining the fifth root of
    unity. *)
Theorem lazard_root_o0_mem_generated
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (first second : Q.lazard_sign_branch)
    (d : RRC.lazard_root_radical_certificate roots)
    (hdata : RRC.lazard_root_radical_invariant_data_in B roots)
    (hnum : RRC.lazard_root_fourier_numerator_data_in B roots)
    (hreconstruct : forall k : 'I_5,
      RRC.lazard_root_certificate_output omega roots d k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k) :
  tnth roots o0 \in CRT.lazard_certificate_generated_field B d.
Proof.
have hzero := CRT.lazard_certificate_inverse_fourier_output_zero_mem_generated
  d hdata hnum omega.
change RRC.lazard_root_certificate_output omega roots d o0 \in
  CRT.lazard_certificate_generated_field B d in hzero.
rewrite (hreconstruct o0) lazard_reversed_two_branches_o0 in hzero.
exact: hzero.
Qed.

End RootCertificateContainment.

End PolynomialFormulasLazardQuinticRootCertificateFieldContainment.
