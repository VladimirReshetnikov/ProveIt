From Stdlib Require Import Ring Tauto.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals
  LazardQuinticVieta LazardQuinticRootProjections
  LazardQuinticRootProjectionJKCommon
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootInvariantE LazardQuinticRootBranchEquivariance
  LazardQuinticRootQ1Bridge LazardQuinticRootFourierNonzero
  LazardQuinticCertificateRadicalTower
  LazardQuinticRootFourierRelations LazardQuinticRootFormulaReconstruction
  LazardQuinticGeneralDepression LazardQuinticGeneralFormulaReconstruction
  LazardQuinticRootCentering LazardQuinticRootBranchSelectionReconstruction
  LazardQuinticRootCoefficientBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root-origin construction of the small radical certificate used by the
    Lazard tower.  The certificate below is not input data: both coherent
    sign choices and its nonzero first Fourier radical are selected from an
    injective depressed tuple of actual roots. *)
Module PolynomialFormulasLazardQuinticRootRadicalCertificate.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.

Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module RJK := PolynomialFormulasLazardQuinticRootProjectionJKCommon.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module Q1 := PolynomialFormulasLazardQuinticQ1Branches.
Module QB := PolynomialFormulasLazardQuinticQ1ProjectionBridge.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module V := PolynomialFormulasLazardQuinticVieta.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RQ := PolynomialFormulasLazardQuinticRootQ1Bridge.
Module FNZ := PolynomialFormulasLazardQuinticRootFourierNonzero.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module RF := PolynomialFormulasLazardQuinticRootFormulaReconstruction.
Module GD := PolynomialFormulasLazardQuinticGeneralDepression.
Module GF := PolynomialFormulasLazardQuinticGeneralFormulaReconstruction.
Module RC := PolynomialFormulasLazardQuinticRootCentering.
Module BSR :=
  PolynomialFormulasLazardQuinticRootBranchSelectionReconstruction.
Module RCB := PolynomialFormulasLazardQuinticRootCoefficientBridge.

Section FiniteChoices.

Variable F : fieldType.

(** The projection and quadratic files introduced the same root epsilon
    before their APIs were joined.  Record the transparent identification
    explicitly at this composition boundary. *)
Lemma lazard_root_epsilon_definitionsE (omega : F) (roots : 5.-tuple F) :
  RP.lazard_root_epsilon omega roots = RR.lazard_root_epsilon omega roots.
Proof.
rewrite /RP.lazard_root_epsilon /RR.lazard_root_epsilon
  /RP.lazard_root_discriminant_factor
  /RR.lazard_fifth_root_discriminant_factor
  /RP.lazard_root_epsilon_product /RR.lazard_epsilon_product.
reflexivity.
Qed.

Lemma lazard_root_quadratic_tripleE (omega : F) (roots : 5.-tuple F) :
  BE.lazard_root_quadratic_triple omega roots =
    Q.LazardQuadraticTriple (RR.lazard_root_epsilon omega roots)
      (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots).
Proof.
apply: BE.lazard_quadratic_triple_ext.
- exact: lazard_root_epsilon_definitionsE.
- reflexivity.
- reflexivity.
Qed.

(** If the quadratic denominator is nonzero, Base or Rotate makes the
    distinguished T-coordinate nonzero. *)
Lemma lazard_exists_branch_with_nonzero_t
    (v : Q.lazard_quadratic_triple F)
    (htu : Q.lazard_t v ^+ 2 + Q.lazard_u v ^+ 2 != 0) :
  exists branch : Q.lazard_sign_branch,
    Q.lazard_t (Q.lazard_branch_triple v branch) != 0.
Proof.
case: (eqVneq (Q.lazard_t v) 0)=> ht.
- case: (eqVneq (Q.lazard_u v) 0)=> hu.
  + move: htu.
    by rewrite ht hu !expr2 !mul0r addr0 eqxx.
  + exists Q.LazardBranchRotate.
    exact hu.
- exists Q.LazardBranchBase.
  exact ht.
Qed.

(** The four source coordinates in Lazard's orbit order contain a nonzero
    entry. *)
Definition lazard_source_has_nonzero (source : 'I_4 -> F) : Prop :=
  source p0 != 0 \/ source p1 != 0 \/
  source p2 != 0 \/ source p3 != 0.

(** Every coherent sign branch merely permutes those four coordinates. *)
Lemma lazard_source_for_branch_has_nonzero source branch :
  lazard_source_has_nonzero source ->
  lazard_source_has_nonzero (BE.lazard_source_for_branch source branch).
Proof.
case: branch;
rewrite /lazard_source_has_nonzero /BE.lazard_source_for_branch
  /QB.lazard_negate_source /QB.lazard_rotate_source
  /QB.lazard_rotate_negate_source /p0 /p1 /p2 /p3 /=;
tauto.
Qed.

(** A second coherent branch moves any selected nonzero coordinate into the
    P1 slot. *)
Lemma lazard_source_nonzero_selects_p0 source :
  lazard_source_has_nonzero source ->
  exists branch : Q.lazard_sign_branch,
    BE.lazard_source_for_branch source branch p0 != 0.
Proof.
move=> [h0 | [h1 | [h2 | h3]]].
- exists Q.LazardBranchBase.
  exact h0.
- exists Q.LazardBranchRotateNegate.
  by rewrite /BE.lazard_source_for_branch
    /QB.lazard_rotate_negate_source /p0 /p1 /=.
- exists Q.LazardBranchNegateTU.
  by rewrite /BE.lazard_source_for_branch
    /QB.lazard_negate_source /p0 /p2 /=.
- exists Q.LazardBranchRotate.
  by rewrite /BE.lazard_source_for_branch
    /QB.lazard_rotate_source /p0 /p3 /=.
Qed.

Lemma lazard_root_fourier_orbit_has_nonzero
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (five_neq0 : (5%:R : F) != 0)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_source_has_nonzero (BE.lazard_root_fourier_orbit omega roots).
Proof.
have h := FNZ.lazard_exists_nonzero_fourier_component
  omega_primitive five_neq0 hroots hsum.
move: h.
rewrite /lazard_source_has_nonzero /BE.lazard_root_fourier_orbit
  /p0 /p1 /p2 /p3 /= RP.lazard_root_fourier_P1E
  (RP.lazard_root_fourier_P2E omega_primitive)
  (RP.lazard_root_fourier_P4E omega_primitive)
  (RP.lazard_root_fourier_P3E omega_primitive).
by [].
Qed.

(** Unlike the earlier two-branch existence theorem, this lemma keeps an
    arbitrary already chosen first branch. *)
Theorem lazard_exists_branch_with_nonzero_P1_after
    (omega : F) (roots : 5.-tuple F) first
    (omega_primitive : 5.-primitive_root omega)
    (five_neq0 : (5%:R : F) != 0)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  exists second : Q.lazard_sign_branch,
    BE.lazard_source_for_branch
      (BE.lazard_source_for_branch
        (BE.lazard_root_fourier_orbit omega roots) first) second p0 != 0.
Proof.
have horbit := lazard_root_fourier_orbit_has_nonzero
  omega_primitive five_neq0 hroots hsum.
have hfirst := lazard_source_for_branch_has_nonzero first horbit.
exact: lazard_source_nonzero_selects_p0 hfirst.
Qed.

(** The branch-indexed target in the root Q1 bridge is exactly the fifth
    power of the coordinate that the same source branch moves to P1. *)
Lemma lazard_root_q1_target_sourceE
    (omega : F) (roots : 5.-tuple F) branch
    (omega_primitive : 5.-primitive_root omega) :
  RQ.lazard_root_q1_target omega roots branch =
    BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) branch p0 ^+ 5.
Proof.
case: branch.
- by rewrite /RQ.lazard_root_q1_target /BE.lazard_source_for_branch
    /BE.lazard_root_fourier_orbit /p0 /= RP.lazard_root_fourier_P1E.
- by rewrite /RQ.lazard_root_q1_target /BE.lazard_source_for_branch
    /QB.lazard_negate_source /BE.lazard_root_fourier_orbit
    /p0 /p2 /= (RP.lazard_root_fourier_P4E omega_primitive).
- by rewrite /RQ.lazard_root_q1_target /BE.lazard_source_for_branch
    /QB.lazard_rotate_source /BE.lazard_root_fourier_orbit
    /p0 /p3 /= (RP.lazard_root_fourier_P3E omega_primitive).
- by rewrite /RQ.lazard_root_q1_target /BE.lazard_source_for_branch
    /QB.lazard_rotate_negate_source /BE.lazard_root_fourier_orbit
    /p0 /p1 /= (RP.lazard_root_fourier_P2E omega_primitive).
Qed.

(** The only field cancellation needed to turn the root product identity
    into the certificate's displayed formula for U. *)
Lemma lazard_u_formula_of_product (epsilon t u G : F)
    (t_neq0 : t != 0) (epsilon_neq0 : epsilon != 0)
    (hproduct : t * u * epsilon = 5%:R * G) :
  u = 5%:R * G / (t * epsilon).
Proof.
have hden : t * epsilon != 0 := mulf_neq0 t_neq0 epsilon_neq0.
apply: (mulfI hden).
rewrite [t * epsilon * u]mulrA [epsilon * u]mulrC -mulrA hproduct.
by rewrite [(t * epsilon) * _]mulrC divfK.
Qed.

End FiniteChoices.

Section RootCertificate.

Variables (F0 : fieldType) (L : fieldExtType F0).

Definition lazard_root_H (roots : 5.-tuple L) : L :=
  RP.lazard_root_invariant_H
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).

Definition lazard_root_I (roots : 5.-tuple L) : L :=
  RP.lazard_root_invariant_I
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).

Definition lazard_root_J (roots : 5.-tuple L) : L :=
  RJK.lazard_root_invariant_J
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).

Definition lazard_root_K (roots : 5.-tuple L) : L :=
  RJK.lazard_root_invariant_K
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).

(** The exact specialization of the tower certificate to quantities defined
    from an ordered root tuple. *)
Definition lazard_root_radical_certificate (roots : 5.-tuple L) : Type :=
  @CRT.lazard_radical_certificate F0 L
    (RP.lazard_depressed_of_roots roots)
    (RP.lazard_root_invariants roots)
    (Q.lazard_root_D roots) (Q.lazard_root_F roots)
    (Q.lazard_root_G roots) (lazard_root_H roots)
    (lazard_root_I roots) (lazard_root_J roots) (lazard_root_K roots).

Definition lazard_root_radical_invariant_data_in
    (B : {subfield L}) (roots : 5.-tuple L) : Prop :=
  @CRT.lazard_radical_invariant_data_in F0 L B
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots)
    (Q.lazard_root_D roots) (Q.lazard_root_F roots)
    (Q.lazard_root_G roots) (lazard_root_H roots)
    (lazard_root_I roots) (lazard_root_J roots) (lazard_root_K roots).

Definition lazard_root_fourier_numerator_data_in
    (B : {subfield L}) (roots : 5.-tuple L) : Prop :=
  @CRT.lazard_fourier_numerator_data_in F0 L B
    (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).

Definition lazard_root_certificate_field
    (B : {subfield L}) (omega : L) (roots : 5.-tuple L)
    (d : lazard_root_radical_certificate roots) : {subfield L} :=
  CRT.lazard_certificate_field_with_root B d omega.

(** The five displayed inverse-Fourier values attached to a root-derived
    certificate.  This is definitionally the output consumed by the radical
    tower, rather than a second reconstruction function. *)
Definition lazard_root_certificate_output
    (omega : L) (roots : 5.-tuple L)
    (d : lazard_root_radical_certificate roots) (k : 'I_5) : L :=
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

Lemma lazard_root_certificate_outputE
    (omega : L) (roots : 5.-tuple L) first second
    (d : lazard_root_radical_certificate roots)
    (hp1 : CRT.lazard_certificate_p1 d =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0)
    (hchosen : CRT.lazard_certificate_chosen d =
      Q.lazard_branch_triple
        (Q.lazard_branch_triple
          (BE.lazard_root_quadratic_triple omega roots) first) second) :
  lazard_root_certificate_output omega roots d =
    RF.lazard_formula_output_two_branches omega roots first second.
Proof.
apply/funext=> k.
rewrite /lazard_root_certificate_output
  /RF.lazard_formula_output_two_branches /= hp1 hchosen.
reflexivity.
Qed.

(** Actual root epsilon, T, U and a selected nonzero Fourier coordinate
    inhabit the radical certificate.  In particular, neither the record nor
    its P1 nonvanishing is a supplied certificate hypothesis. *)
Theorem lazard_exists_root_radical_certificate
    (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 :
      FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) != 0) :
  exists (first second : Q.lazard_sign_branch)
      (d : lazard_root_radical_certificate roots),
    CRT.lazard_certificate_initial d =
      Q.lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
        first /\
    Q.lazard_t (CRT.lazard_certificate_initial d) != 0 /\
    CRT.lazard_certificate_branch d = second /\
    CRT.lazard_certificate_p1 d =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 /\
    CRT.lazard_certificate_p1 d != 0 /\
    CRT.lazard_certificate_chosen d =
      Q.lazard_branch_triple
        (Q.lazard_branch_triple
          (BE.lazard_root_quadratic_triple omega roots) first) second.
Proof.
have hrootE : Q.lazard_root_E roots != 0.
  rewrite -(@RIE.lazard_root_invariant_E_eq L roots hsum).
  exact E_neq0.
have hTU :
    RR.lazard_root_T omega roots ^+ 2 +
      RR.lazard_root_formula_U omega roots ^+ 2 != 0.
  rewrite (@RQ.lazard_root_TU_square_sum L omega roots omega_primitive).
  exact: mulf_neq0 five_neq0 hrootE.
have [first hfirst_t] := lazard_exists_branch_with_nonzero_t hTU.
pose initial := Q.lazard_branch_triple
  (BE.lazard_root_quadratic_triple omega roots) first.
have initial_t_neq0 : Q.lazard_t initial != 0.
  exact hfirst_t.
have initial_epsilon_neq0 : Q.lazard_epsilon initial != 0.
  apply: BE.lazard_branch_epsilon_neq0.
  exact root_epsilon_neq0.
have root_epsilon_neq0_RR : RR.lazard_root_epsilon omega roots != 0.
  rewrite -lazard_root_epsilon_definitionsE.
  exact root_epsilon_neq0.
have hrelations0 := @Q.lazard_root_quadratic_relations_primitive
  L omega roots two_neq0 omega_primitive root_epsilon_neq0_RR.
have hrelations :
    Q.lazard_quadratic_relations
      (Q.lazard_root_D roots) (Q.lazard_root_E roots)
      (Q.lazard_root_F roots) (Q.lazard_root_G roots) initial.
  rewrite /initial.
  rewrite lazard_root_quadratic_tripleE.
  exact: Q.lazard_quadratic_relations_branch hrelations0.
have hepsilon_square :
    Q.lazard_epsilon initial ^+ 2 = 5%:R * Q.lazard_root_D roots.
  exact: Q.lazard_epsilon_square hrelations.
have ht_square :
    Q.lazard_t initial ^+ 2 =
      ((5%:R : L) / (2%:R : L)) *
        (FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
            (RP.lazard_root_invariants roots) +
          Q.lazard_root_F roots / Q.lazard_epsilon initial).
  rewrite (@RIE.lazard_root_invariant_E_eq L roots hsum).
  exact: Q.lazard_t_square hrelations.
have hu_formula :
    Q.lazard_u initial =
      5%:R * Q.lazard_root_G roots /
        (Q.lazard_t initial * Q.lazard_epsilon initial).
  exact: lazard_u_formula_of_product initial_t_neq0 initial_epsilon_neq0
    (Q.lazard_t_u_epsilon_product hrelations).

have [second hp1] := @lazard_exists_branch_with_nonzero_P1_after
  L omega roots first omega_primitive five_neq0 hroots hsum.
pose p1value :=
  BE.lazard_source_for_branch
    (BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots) first) second p0.
have p1value_neq0 : p1value != 0.
  exact hp1.

pose y := BE.lazard_roots_for_branch roots first.
have hsum_y : RP.lazard_root_esymm1 y = 0.
  by rewrite /y BE.lazard_root_esymm1_roots_for_branch hsum.
have htriple_y : BE.lazard_root_quadratic_triple omega y = initial.
  by rewrite /y /initial BE.lazard_root_quadratic_triple_roots_for_branch.
have hepsilon_y : RP.lazard_root_epsilon omega y != 0.
  change Q.lazard_epsilon (BE.lazard_root_quadratic_triple omega y) != 0.
  by rewrite htriple_y.
have hE_y : Q.lazard_root_E y != 0.
  rewrite -(@RIE.lazard_root_invariant_E_eq L y hsum_y).
  move: E_neq0.
  by rewrite /y BE.lazard_depressed_of_roots_for_branch
    BE.lazard_root_invariants_roots_for_branch.
have hq1_y := @RQ.lazard_root_q1_formula_correct
  L omega y second two_neq0 five_neq0 omega_primitive
  hsum_y hepsilon_y hE_y.
have htarget_y := @lazard_root_q1_target_sourceE
  L omega y second omega_primitive.
have horbit_y :
    BE.lazard_root_fourier_orbit omega y =
      BE.lazard_source_for_branch
        (BE.lazard_root_fourier_orbit omega roots) first.
  apply/funext=> j.
  exact: BE.lazard_root_fourier_orbit_roots_for_branch.
have hp1_fifth_y :
    p1value ^+ 5 = RQ.lazard_root_q1_formula omega y second.
  rewrite /p1value -horbit_y.
  exact: esym (eq_trans hq1_y htarget_y).
have hq1_transport :
    RQ.lazard_root_q1_formula omega y second =
      Q1.lazard_q1 (lazard_root_H roots) (lazard_root_I roots)
        (lazard_root_J roots) (lazard_root_K roots)
        (FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
          (RP.lazard_root_invariants roots))
        (Q.lazard_branch_triple initial second).
  rewrite /RQ.lazard_root_q1_formula /Q1.lazard_q1_branch.
  fold (BE.lazard_root_quadratic_triple omega y).
  rewrite -(@RIE.lazard_root_invariant_E_eq L y hsum_y).
  rewrite htriple_y.
  rewrite /lazard_root_H /lazard_root_I /lazard_root_J /lazard_root_K
    /y BE.lazard_depressed_of_roots_for_branch
    BE.lazard_root_invariants_roots_for_branch.
  reflexivity.
have hp1_fifth :
    p1value ^+ 5 =
      Q1.lazard_q1 (lazard_root_H roots) (lazard_root_I roots)
        (lazard_root_J roots) (lazard_root_K roots)
        (FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
          (RP.lazard_root_invariants roots))
        (Q.lazard_branch_triple initial second).
  exact: eq_trans hp1_fifth_y hq1_transport.

pose d : lazard_root_radical_certificate roots :=
  {| CRT.lazard_certificate_initial := initial;
     CRT.lazard_certificate_branch := second;
     CRT.lazard_certificate_p1 := p1value;
     CRT.lazard_certificate_epsilon_square := hepsilon_square;
     CRT.lazard_certificate_t_square := ht_square;
     CRT.lazard_certificate_u_formula := hu_formula;
     CRT.lazard_certificate_p1_fifth := hp1_fifth |}.
exists first, second, d; split.
- by rewrite /d /initial.
- split.
  + by rewrite /d.
  + split.
    * by rewrite /d.
    * split.
      -- by rewrite /d /p1value.
      -- split.
         ++ by rewrite /d.
         ++ by rewrite /d /CRT.lazard_certificate_chosen /initial.
Qed.

(** Certificate-strengthened form of root branch selection.  The branches
    selected for the radical record are the very same branches used by the
    reconstruction, so its five tower outputs factor the depressed quintic,
    are all roots, and exhaust every root. *)
Theorem lazard_exists_root_radical_certificate_complete
    (omega : L) (roots : 5.-tuple L)
    (two_neq0 : (2%:R : L) != 0)
    (five_neq0 : (5%:R : L) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hroots : injective (tnth roots))
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (root_epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 :
      FN.lazard_invariant_E (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) != 0) :
  exists (first second : Q.lazard_sign_branch)
      (d : lazard_root_radical_certificate roots),
    CRT.lazard_certificate_initial d =
      Q.lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
        first /\
    Q.lazard_t (CRT.lazard_certificate_initial d) != 0 /\
    CRT.lazard_certificate_branch d = second /\
    CRT.lazard_certificate_p1 d =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit omega roots) first) second p0 /\
    CRT.lazard_certificate_p1 d != 0 /\
    CRT.lazard_certificate_chosen d =
      Q.lazard_branch_triple
        (Q.lazard_branch_triple
          (BE.lazard_root_quadratic_triple omega roots) first) second /\
    (forall k : 'I_5,
      lazard_root_certificate_output omega roots d k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k) /\
    (forall z : L,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
        (z - lazard_root_certificate_output omega roots d o0) *
        (z - lazard_root_certificate_output omega roots d o1) *
        (z - lazard_root_certificate_output omega roots d o2) *
        (z - lazard_root_certificate_output omega roots d o3) *
        (z - lazard_root_certificate_output omega roots d o4)) /\
    (forall k : 'I_5,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
          (lazard_root_certificate_output omega roots d k) = 0) /\
    (forall z : L,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 ->
      exists k : 'I_5,
        z = lazard_root_certificate_output omega roots d k).
Proof.
have [first [second [d
    [hinitial [ht [hbranch [hp1 [hp1_neq0 hchosen]]]]]]]] :=
  lazard_exists_root_radical_certificate two_neq0 five_neq0
    omega_primitive hroots hsum root_epsilon_neq0 E_neq0.
have houtput :
    lazard_root_certificate_output omega roots d =
      RF.lazard_formula_output_two_branches omega roots first second.
  exact: lazard_root_certificate_outputE hp1 hchosen.
have hreversed : forall k : 'I_5,
    lazard_root_certificate_output omega roots d k =
    RFR.lazard_reversed_root_tuple
      (BE.lazard_roots_for_branch
        (BE.lazard_roots_for_branch roots first) second) k.
  move=> k; rewrite houtput.
  exact: (@RF.lazard_formula_output_two_branches_eq_reversed_roots
    L omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1_neq0 k).
have hfactor : forall z : L,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
      (z - lazard_root_certificate_output omega roots d o0) *
      (z - lazard_root_certificate_output omega roots d o1) *
      (z - lazard_root_certificate_output omega roots d o2) *
      (z - lazard_root_certificate_output omega roots d o3) *
      (z - lazard_root_certificate_output omega roots d o4).
  move=> z; rewrite houtput.
  exact: (@RF.lazard_formula_output_two_branches_eval_factorization
    L omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1_neq0 z).
have hsound : forall k : 'I_5,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
        (lazard_root_certificate_output omega roots d k) = 0.
  move=> k; rewrite houtput.
  exact: (@RF.lazard_formula_output_two_branches_is_root
    L omega roots first second two_neq0 five_neq0 omega_primitive hsum
    root_epsilon_neq0 E_neq0 hp1_neq0 k).
have hcomplete : forall z : L,
    V.lazard_depressed_quintic_eval
        (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
        (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 ->
    exists k : 'I_5, z = lazard_root_certificate_output omega roots d k.
  move=> z hz.
  apply: (@GD.lazard_five_linear_factors_zero_exists L z
    (lazard_root_certificate_output omega roots d)).
  by rewrite -(hfactor z) hz.
exists first, second, d.
repeat split; assumption.
Qed.

(** Instantiation of the existing radical-tower API with the same
    root-origin certificate whose outputs were just reconstructed.  The two
    membership packages are precisely the old coefficient-to-base-field
    obligations; no radical choice or output-correctness premise remains. *)
Theorem lazard_exists_root_radical_tower_complete
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
    (hdata : lazard_root_radical_invariant_data_in B roots)
    (hnum : lazard_root_fourier_numerator_data_in B roots) :
  exists (first second : Q.lazard_sign_branch)
      (d : lazard_root_radical_certificate roots),
    CRT.lazard_certificate_p1 d != 0 /\
    @PolynomialFormulasLazardOptimality.radical_extension F0 L B
      (lazard_root_certificate_field B omega roots d) /\
    (forall k : 'I_5,
      lazard_root_certificate_output omega roots d k \in
        lazard_root_certificate_field B omega roots d) /\
    (forall k : 'I_5,
      lazard_root_certificate_output omega roots d k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch roots first) second) k) /\
    (forall z : L,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z =
        (z - lazard_root_certificate_output omega roots d o0) *
        (z - lazard_root_certificate_output omega roots d o1) *
        (z - lazard_root_certificate_output omega roots d o2) *
        (z - lazard_root_certificate_output omega roots d o3) *
        (z - lazard_root_certificate_output omega roots d o4)) /\
    (forall k : 'I_5,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots))
          (lazard_root_certificate_output omega roots d k) = 0) /\
    (forall z : L,
      V.lazard_depressed_quintic_eval
          (RP.lazard_root_p (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_q (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_r (RP.lazard_depressed_of_roots roots))
          (RP.lazard_root_s (RP.lazard_depressed_of_roots roots)) z = 0 ->
      exists k : 'I_5,
        z = lazard_root_certificate_output omega roots d k).
Proof.
have [first [second [d
    [_ [_ [_ [_ [hp1_neq0 [_
      [hreversed [hfactor [hsound hcomplete]]]]]]]]]]]]] :=
  lazard_exists_root_radical_certificate_complete two_neq0 five_neq0
    omega_primitive hroots hsum root_epsilon_neq0 E_neq0.
have htower := CRT.lazard_certificate_all_outputs_in_radical_extension
  d hdata hnum omega_primitive.
move: htower=> [hradical hmem].
exists first, second, d.
split; first exact hp1_neq0.
split.
- exact hradical.
- split.
  + exact hmem.
  + repeat split; assumption.
Qed.

End RootCertificate.

End PolynomialFormulasLazardQuinticRootRadicalCertificate.
