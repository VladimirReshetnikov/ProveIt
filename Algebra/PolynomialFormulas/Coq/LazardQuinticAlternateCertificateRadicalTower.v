From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticVieta
  LazardQuinticCoherentAlternateProjection
  LazardQuinticCoherentAlternateProjectionBridge
  LazardQuinticCertificateRadicalTower
  LazardOptimality LazardOptimalityTheoremFourDegree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Alternate radical-tower building blocks.

    The ordinary [lazard_radical_certificate] stores the printed standard
    formula for [P1^5].  That formula is unavailable precisely in the case
    where Lazard invokes his alternate projection matrix.  Reusing that
    certificate would therefore make the alternate proof circular.

    The first part of this file isolates a useful but deliberately partial
    one-coordinate construction.  Its record retains only the two quadratic
    power equations and the formula for [U], but replaces the standard [q1]
    equation by the corrected alternate recovery expression.  Membership of
    the four corrected projection values in the base field then proves
    honestly that [P1^5] lies after the two square adjunctions.  The printed
    formulas for [P2], [P3], and [P4] are retained there only to prove a field-
    membership statement; because those formulas also divide by [E], that
    partial construction is not a correctness theorem when [E = 0].

    The second part supplies the genuinely denominator-independent machinery:
    recover all four Fourier fifth powers, adjoin four fifth roots, and apply
    inverse Fourier reconstruction.  The root-origin correctness adapter is
    in [LazardQuinticRootCompleteAlternateTower]. *)
Module PolynomialFormulasLazardQuinticAlternateCertificateRadicalTower.

Import GRing.Theory.
Local Open Scope ring_scope.

Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module P := PolynomialFormulasLazardQuinticProjection.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module V := PolynomialFormulasLazardQuinticVieta.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.
Module CB :=
  PolynomialFormulasLazardQuinticCoherentAlternateProjectionBridge.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module O := PolynomialFormulasLazardOptimality.
Module T4 := PolynomialFormulasLazardOptimalityTheoremFourDegree.

Section AlternateCertificateTower.

Variables (F0 : fieldType) (L : fieldExtType F0).

(** Only the four coefficient-side quantities used before the fifth-root
    step are required by the alternate tower. *)
Record lazard_alternate_radical_invariant_data_in
    (B : {subfield L})
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L)
    (D Finvariant G : L) : Prop :=
  LazardAlternateRadicalInvariantDataIn {
    lazard_alternate_D_in_base : D \in B;
    lazard_alternate_E_in_base : FN.lazard_invariant_E c i \in B;
    lazard_alternate_F_in_base : Finvariant \in B;
    lazard_alternate_G_in_base : G \in B
  }.

(** All four corrected projection coordinates lie in the coefficient
    field.  The compositum-descent theorem supplies this record without a
    caller-provided root-action certificate. *)
Definition lazard_alternate_projection_data_in
    (B : {subfield L}) (projections : 'I_4 -> L) : Prop :=
  forall j : 'I_4, projections j \in B.

Record lazard_alternate_radical_certificate
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L)
    (D Finvariant G : L)
    (projections : 'I_4 -> L) :=
  LazardAlternateRadicalCertificate {
    lazard_alternate_initial : Q.lazard_quadratic_triple L;
    lazard_alternate_branch : Q.lazard_sign_branch;
    lazard_alternate_p1 : L;
    lazard_alternate_epsilon_square :
      Q.lazard_epsilon lazard_alternate_initial ^+ 2 = 5%:R * D;
    lazard_alternate_t_square :
      Q.lazard_t lazard_alternate_initial ^+ 2 =
        ((5%:R : L) / (2%:R : L)) *
          (FN.lazard_invariant_E c i +
            Finvariant / Q.lazard_epsilon lazard_alternate_initial);
    lazard_alternate_u_formula :
      Q.lazard_u lazard_alternate_initial =
        5%:R * G /
          (Q.lazard_t lazard_alternate_initial *
            Q.lazard_epsilon lazard_alternate_initial);
    lazard_alternate_p1_fifth :
      lazard_alternate_p1 ^+ 5 =
        C.lazard_coherent_alternate_recover
          (Q.lazard_epsilon
            (Q.lazard_branch_triple lazard_alternate_initial
              lazard_alternate_branch))
          (Q.lazard_t
            (Q.lazard_branch_triple lazard_alternate_initial
              lazard_alternate_branch))
          (Q.lazard_u
            (Q.lazard_branch_triple lazard_alternate_initial
              lazard_alternate_branch))
          projections
  }.

Definition lazard_alternate_chosen c i D Finvariant G projections
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) : Q.lazard_quadratic_triple L :=
  Q.lazard_branch_triple (lazard_alternate_initial d)
    (lazard_alternate_branch d).

Definition lazard_alternate_first_field c i D Finvariant G projections
    (B : {subfield L})
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) : {subfield L} :=
  <<B; Q.lazard_epsilon (lazard_alternate_initial d)>>%AS.

Definition lazard_alternate_second_field c i D Finvariant G projections
    (B : {subfield L})
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) : {subfield L} :=
  <<lazard_alternate_first_field B d;
    Q.lazard_t (lazard_alternate_initial d)>>%AS.

Definition lazard_alternate_generated_field c i D Finvariant G projections
    (B : {subfield L})
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) : {subfield L} :=
  <<lazard_alternate_second_field B d; lazard_alternate_p1 d>>%AS.

Definition lazard_alternate_field_with_root c i D Finvariant G projections
    (B : {subfield L})
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) (omega : L) : {subfield L} :=
  <<lazard_alternate_generated_field B d; omega>>%AS.

Lemma lazard_alternate_base_mem_first c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) x :
  x \in B -> x \in lazard_alternate_first_field B d.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_alternate_first_mem_second c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) x :
  x \in lazard_alternate_first_field B d ->
  x \in lazard_alternate_second_field B d.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_alternate_second_mem_generated
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) x :
  x \in lazard_alternate_second_field B d ->
  x \in lazard_alternate_generated_field B d.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_alternate_generated_mem_with_root
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) omega x :
  x \in lazard_alternate_generated_field B d ->
  x \in lazard_alternate_field_with_root B d omega.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_alternate_base_mem_second c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) x :
  x \in B -> x \in lazard_alternate_second_field B d.
Proof.
move=> hx.
exact: lazard_alternate_first_mem_second
  (lazard_alternate_base_mem_first d hx).
Qed.

Lemma lazard_alternate_base_mem_generated c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) x :
  x \in B -> x \in lazard_alternate_generated_field B d.
Proof.
move=> hx.
exact: lazard_alternate_second_mem_generated
  (lazard_alternate_base_mem_second d hx).
Qed.

Lemma lazard_alternate_epsilon_mem_first
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) :
  Q.lazard_epsilon (lazard_alternate_initial d) \in
    lazard_alternate_first_field B d.
Proof. exact: memv_adjoin. Qed.

Lemma lazard_alternate_t_mem_second c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) :
  Q.lazard_t (lazard_alternate_initial d) \in
    lazard_alternate_second_field B d.
Proof. exact: memv_adjoin. Qed.

Lemma lazard_alternate_p1_mem_generated c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) :
  lazard_alternate_p1 d \in lazard_alternate_generated_field B d.
Proof. exact: memv_adjoin. Qed.

Theorem lazard_alternate_initial_mem_second
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G) :
  CRT.lazard_quadratic_triple_in
    (lazard_alternate_second_field B d) (lazard_alternate_initial d).
Proof.
constructor.
- exact: lazard_alternate_first_mem_second
    (lazard_alternate_epsilon_mem_first B d).
- exact: lazard_alternate_t_mem_second B d.
- rewrite (lazard_alternate_u_formula d).
  apply: rpred_div.
  + apply: rpredM; first exact: CRT.lazard_natr_mem.
    exact: lazard_alternate_base_mem_second d
      (lazard_alternate_G_in_base hdata).
  + apply: rpredM.
    * exact: lazard_alternate_t_mem_second B d.
    * exact: lazard_alternate_first_mem_second
        (lazard_alternate_epsilon_mem_first B d).
Qed.

Theorem lazard_alternate_chosen_mem_second
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G) :
  CRT.lazard_quadratic_triple_in
    (lazard_alternate_second_field B d) (lazard_alternate_chosen d).
Proof.
exact: CRT.lazard_quadratic_triple_in_branch
  (lazard_alternate_initial_mem_second d hdata).
Qed.

(** Reusable membership lemma for the corrected Cramer expression.  It is
    independent of either certificate syntax and is shared by the abstract
    certificate and the direct four-fifth-root root tower. *)
Theorem lazard_coherent_alternate_recover_mem
    (M : {subfield L}) (v : Q.lazard_quadratic_triple L)
    (projections : 'I_4 -> L)
    (hv : CRT.lazard_quadratic_triple_in M v)
    (hprojections : forall j : 'I_4, projections j \in M) :
  C.lazard_coherent_alternate_recover
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v) projections \in M.
Proof.
rewrite /C.lazard_coherent_alternate_recover
  /C.lazard_coherent_alternate_denominator.
apply: rpredD.
- exact: rpred_div (hprojections P.p0) (CRT.lazard_natr_mem _ 4).
- apply: rpredD.
  + exact: rpred_div (hprojections P.p1)
      (rpredM (CRT.lazard_natr_mem _ 4)
        (CRT.lazard_triple_epsilon_in hv)).
  + apply: rpred_div.
    * apply: rpredB.
      -- apply: rpredM.
         ++ apply: rpredM.
            ** exact: CRT.lazard_triple_epsilon_in hv.
            ** apply: rpredD.
               --- exact: rpredM (CRT.lazard_natr_mem _ 2)
                     (CRT.lazard_triple_t_in hv).
               --- exact: CRT.lazard_triple_u_in hv.
         ++ exact: hprojections P.p2.
      -- exact: rpredM (CRT.lazard_triple_u_in hv)
           (hprojections P.p3).
    * apply: rpredM.
      -- exact: rpredM (CRT.lazard_natr_mem _ 4)
           (CRT.lazard_triple_epsilon_in hv).
      -- apply: rpredB.
         ++ apply: rpredD.
            ** exact: rpredX (CRT.lazard_triple_t_in hv).
            ** exact: rpredM (CRT.lazard_triple_t_in hv)
                 (CRT.lazard_triple_u_in hv).
         ++ exact: rpredX (CRT.lazard_triple_u_in hv).
Qed.

(** The alternate Cramer expression lies in the second square field because
    its four projection values lie in the base and all three quadratic
    coordinates lie in the second field. *)
Theorem lazard_coherent_alternate_recover_mem_second
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hprojections : lazard_alternate_projection_data_in B projections) :
  C.lazard_coherent_alternate_recover
      (Q.lazard_epsilon (lazard_alternate_chosen d))
      (Q.lazard_t (lazard_alternate_chosen d))
      (Q.lazard_u (lazard_alternate_chosen d)) projections \in
    lazard_alternate_second_field B d.
Proof.
apply: lazard_coherent_alternate_recover_mem
  (lazard_alternate_chosen_mem_second d hdata).
move=> j.
exact: lazard_alternate_base_mem_second d (hprojections j).
Qed.

Theorem lazard_alternate_p1_fifth_mem_second
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hprojections : lazard_alternate_projection_data_in B projections) :
  lazard_alternate_p1 d ^+ 5 \in lazard_alternate_second_field B d.
Proof.
rewrite (lazard_alternate_p1_fifth d).
exact: lazard_coherent_alternate_recover_mem_second d hdata hprojections.
Qed.

(** The corrected alternate certificate has the same honest radical shape:
    two square adjunctions followed by one fifth adjunction. *)
Theorem lazard_alternate_generated_field_has_two_square_fifth_presentation
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hprojections : lazard_alternate_projection_data_in B projections) :
  @T4.square_roots_and_fifth_root_presentation F0 L B
    (lazard_alternate_generated_field B d) 2.
Proof.
have hepsilon : Q.lazard_epsilon (lazard_alternate_initial d) ^+ 2 \in B.
  rewrite (lazard_alternate_epsilon_square d).
  exact: rpredM (CRT.lazard_natr_mem B 5)
    (lazard_alternate_D_in_base hdata).
have ht : Q.lazard_t (lazard_alternate_initial d) ^+ 2 \in
    lazard_alternate_first_field B d.
  rewrite (lazard_alternate_t_square d).
  apply: rpredM.
  - exact: rpred_div (CRT.lazard_natr_mem _ 5)
      (CRT.lazard_natr_mem _ 2).
  - apply: rpredD.
    + exact: lazard_alternate_base_mem_first d
        (lazard_alternate_E_in_base hdata).
    + exact: rpred_div
        (lazard_alternate_base_mem_first d
          (lazard_alternate_F_in_base hdata))
        (lazard_alternate_epsilon_mem_first B d).
have hzero : @T4.square_radical_tower F0 L B 0 B :=
  @T4.SquareRadicalTowerZero F0 L B.
have hfirst : @T4.square_radical_tower F0 L B 1
    (lazard_alternate_first_field B d).
  rewrite /lazard_alternate_first_field.
  exact: T4.SquareRadicalTowerStep hzero hepsilon.
have hsecond : @T4.square_radical_tower F0 L B 2
    (lazard_alternate_second_field B d).
  rewrite /lazard_alternate_second_field.
  exact: T4.SquareRadicalTowerStep hfirst ht.
refine (@T4.SquareRootsAndFifthRootPresentation
  F0 L B (lazard_alternate_generated_field B d) 2
  (lazard_alternate_second_field B d) hsecond
  (lazard_alternate_p1 d)
  (lazard_alternate_p1_fifth_mem_second d hdata hprojections) _).
by rewrite /lazard_alternate_generated_field.
Qed.

Theorem lazard_alternate_generated_field_is_radical
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hprojections : lazard_alternate_projection_data_in B projections) :
  @O.radical_extension F0 L B (lazard_alternate_generated_field B d).
Proof.
exact: T4.square_roots_and_fifth_root_is_radical
  (lazard_alternate_generated_field_has_two_square_fifth_presentation
    d hdata hprojections).
Qed.

(** The remaining three *printed expressions* use the same numerator formulas
    as the standard path.  Their membership proof depends only on the chosen
    quadratic triple and [P1], not on the equation used to obtain [P1^5].
    This does not assert that these expressions are Fourier components when
    [E = 0]; their defining formulas themselves contain division by [E]. *)
Theorem lazard_alternate_P4_mem_generated
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hnum : CRT.lazard_fourier_numerator_data_in B c i) :
  FN.lazard_fourier_P4_formula c i (lazard_alternate_chosen d)
      (lazard_alternate_p1 d) \in lazard_alternate_generated_field B d.
Proof.
rewrite /FN.lazard_fourier_P4_formula.
have hv2 := lazard_alternate_chosen_mem_second d hdata.
have he := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_epsilon_in hv2).
have hp := lazard_alternate_p1_mem_generated B d.
apply: rpredD.
- apply: rpred_div.
  + exact: lazard_alternate_base_mem_generated d
      (CRT.lazard_p41_in_base hnum).
  + exact: rpredM (CRT.lazard_natr_mem _ 2) hp.
- apply: rpred_div.
  + exact: lazard_alternate_base_mem_generated d
      (CRT.lazard_p42_in_base hnum).
  + exact: rpredM (rpredM (CRT.lazard_natr_mem _ 2) he) hp.
Qed.

Theorem lazard_alternate_P3_mem_generated
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hnum : CRT.lazard_fourier_numerator_data_in B c i) :
  FN.lazard_fourier_P3_formula c i (lazard_alternate_chosen d)
      (lazard_alternate_p1 d) \in lazard_alternate_generated_field B d.
Proof.
rewrite /FN.lazard_fourier_P3_formula.
have hv2 := lazard_alternate_chosen_mem_second d hdata.
have he := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_epsilon_in hv2).
have ht := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_t_in hv2).
have hu := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_u_in hv2).
have hp := lazard_alternate_p1_mem_generated B d.
have hp2 : lazard_alternate_p1 d ^+ 2 \in
    lazard_alternate_generated_field B d by exact: rpredX hp.
apply: rpredD.
- apply: rpredD.
  + apply: rpred_div.
    * exact: lazard_alternate_base_mem_generated d
        (CRT.lazard_p31_in_base hnum).
    * exact: rpredM (CRT.lazard_natr_mem _ 4) hp2.
  + apply: rpred_div.
    * exact: lazard_alternate_base_mem_generated d
        (CRT.lazard_p32_in_base hnum).
    * exact: rpredM (rpredM (CRT.lazard_natr_mem _ 4) he) hp2.
- apply: rpred_div.
  + apply: rpredD.
    * exact: rpredM
        (lazard_alternate_base_mem_generated d
          (CRT.lazard_p33_in_base hnum)) ht.
    * exact: rpredM
        (lazard_alternate_base_mem_generated d
          (CRT.lazard_p34_in_base hnum)) hu.
  + exact: rpredM
      (rpredM (CRT.lazard_natr_mem _ 10)
        (lazard_alternate_base_mem_generated d
          (lazard_alternate_E_in_base hdata))) hp2.
Qed.

Theorem lazard_alternate_P2_mem_generated
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hnum : CRT.lazard_fourier_numerator_data_in B c i) :
  FN.lazard_fourier_P2_formula c i (lazard_alternate_chosen d)
      (lazard_alternate_p1 d) \in lazard_alternate_generated_field B d.
Proof.
rewrite /FN.lazard_fourier_P2_formula.
have hv2 := lazard_alternate_chosen_mem_second d hdata.
have he := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_epsilon_in hv2).
have ht := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_t_in hv2).
have hu := lazard_alternate_second_mem_generated
  d (CRT.lazard_triple_u_in hv2).
have hp := lazard_alternate_p1_mem_generated B d.
have hp3 : lazard_alternate_p1 d ^+ 3 \in
    lazard_alternate_generated_field B d by exact: rpredX hp.
apply: rpredD.
- apply: rpredD.
  + apply: rpred_div.
    * exact: lazard_alternate_base_mem_generated d
        (CRT.lazard_p21_in_base hnum).
    * exact: rpredM (CRT.lazard_natr_mem _ 4) hp3.
  + apply: rpred_div.
    * exact: lazard_alternate_base_mem_generated d
        (CRT.lazard_p22_in_base hnum).
    * exact: rpredM (rpredM (CRT.lazard_natr_mem _ 4) he) hp3.
- apply: rpred_div.
  + apply: rpredD.
    * exact: rpredM
        (lazard_alternate_base_mem_generated d
          (CRT.lazard_p23_in_base hnum)) ht.
    * exact: rpredM
        (lazard_alternate_base_mem_generated d
          (CRT.lazard_p24_in_base hnum)) hu.
  + exact: rpredM
      (rpredM (CRT.lazard_natr_mem _ 10)
        (lazard_alternate_base_mem_generated d
          (lazard_alternate_E_in_base hdata))) hp3.
Qed.

Lemma lazard_alternate_omega_mem_with_root
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections) omega :
  omega \in lazard_alternate_field_with_root B d omega.
Proof. exact: memv_adjoin. Qed.

Theorem lazard_alternate_inverse_fourier_output_mem_with_root
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hnum : CRT.lazard_fourier_numerator_data_in B c i)
    (omega : L) (k : 'I_5) :
  V.lazard_inverse_fourier_output omega
      (lazard_alternate_p1 d)
      (FN.lazard_fourier_P2_formula c i (lazard_alternate_chosen d)
        (lazard_alternate_p1 d))
      (FN.lazard_fourier_P3_formula c i (lazard_alternate_chosen d)
        (lazard_alternate_p1 d))
      (FN.lazard_fourier_P4_formula c i (lazard_alternate_chosen d)
        (lazard_alternate_p1 d)) k \in
    lazard_alternate_field_with_root B d omega.
Proof.
rewrite /V.lazard_inverse_fourier_output
  /V.lazard_inverse_fourier_unscaled.
have homega := lazard_alternate_omega_mem_with_root B d omega.
have hp1 := lazard_alternate_generated_mem_with_root d omega
  (lazard_alternate_p1_mem_generated B d).
have hp2 := lazard_alternate_generated_mem_with_root d omega
  (lazard_alternate_P2_mem_generated d hdata hnum).
have hp3 := lazard_alternate_generated_mem_with_root d omega
  (lazard_alternate_P3_mem_generated d hdata hnum).
have hp4 := lazard_alternate_generated_mem_with_root d omega
  (lazard_alternate_P4_mem_generated d hdata hnum).
apply: rpredM.
- exact: rpredV (CRT.lazard_natr_mem _ 5).
- apply: rpredD.
  + apply: rpredD.
    * apply: rpredD.
      -- exact: rpredM (rpredX homega) hp1.
      -- exact: rpredM (rpredX homega) hp2.
    * exact: rpredM (rpredX homega) hp3.
  + exact: rpredM (rpredX homega) hp4.
Qed.

Theorem lazard_alternate_field_with_primitive_root_is_radical
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hprojections : lazard_alternate_projection_data_in B projections)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  @O.radical_extension F0 L B (lazard_alternate_field_with_root B d omega).
Proof.
have hcert := lazard_alternate_generated_field_is_radical
  d hdata hprojections.
have hstep : @O.simple_radical_step F0 L
    (lazard_alternate_generated_field B d)
    (lazard_alternate_field_with_root B d omega).
  exists omega, 5.
  split; first by [].
  split.
  - rewrite (prim_expr_order omega_primitive).
    exact: mem1v.
  - reflexivity.
exact: (@O.RadicalExtensionStep F0 L B
  (lazard_alternate_generated_field B d)
  (lazard_alternate_field_with_root B d omega) hcert hstep).
Qed.

(** Membership-only aggregate for the partial one-coordinate construction.
    A literal radical extension contains the five displayed expressions, and
    no standard [q1] equation occurs in either the statement or proof.  This
    theorem intentionally makes no root-correctness claim.  In particular it
    must not be used as the denominator-safe solution when [E = 0]; use the
    four-fifth construction below and its root-origin adapter instead. *)
Theorem lazard_alternate_all_outputs_in_radical_extension
    c i D Finvariant G projections B
    (d : lazard_alternate_radical_certificate
      c i D Finvariant G projections)
    (hdata : lazard_alternate_radical_invariant_data_in
      B c i D Finvariant G)
    (hprojections : lazard_alternate_projection_data_in B projections)
    (hnum : CRT.lazard_fourier_numerator_data_in B c i)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  @O.radical_extension F0 L B
      (lazard_alternate_field_with_root B d omega) /\
    forall k : 'I_5,
      V.lazard_inverse_fourier_output omega
          (lazard_alternate_p1 d)
          (FN.lazard_fourier_P2_formula c i (lazard_alternate_chosen d)
            (lazard_alternate_p1 d))
          (FN.lazard_fourier_P3_formula c i (lazard_alternate_chosen d)
            (lazard_alternate_p1 d))
          (FN.lazard_fourier_P4_formula c i (lazard_alternate_chosen d)
            (lazard_alternate_p1 d)) k \in
        lazard_alternate_field_with_root B d omega.
Proof.
split.
- exact: lazard_alternate_field_with_primitive_root_is_radical
    d hdata hprojections omega_primitive.
- move=> k.
  exact: lazard_alternate_inverse_fourier_output_mem_with_root
    d hdata hnum k.
Qed.

(* -------------------------------------------------------------------- *)
(** A denominator-independent completion uses all four recovered fifth
    powers.  It costs four fifth-root adjunctions, but remains valid when
    [E = -(T^2+U^2)] vanishes and the printed P2/P3/P4 formulas are singular.
    The construction below is abstract in the four chosen roots, so the
    root-origin adapter only has to prove their four power equations. *)

Definition lazard_two_square_first_field
    (B : {subfield L}) (epsilon : L) : {subfield L} :=
  <<B; epsilon>>%AS.

Definition lazard_two_square_second_field
    (B : {subfield L}) (epsilon t : L) : {subfield L} :=
  <<lazard_two_square_first_field B epsilon; t>>%AS.

Definition lazard_three_square_third_field
    (B : {subfield L}) (epsilon t u : L) : {subfield L} :=
  <<lazard_two_square_second_field B epsilon t; u>>%AS.

Lemma lazard_two_square_base_mem_second B epsilon t x :
  x \in B -> x \in lazard_two_square_second_field B epsilon t.
Proof. move=> hx; exact: subvP_adjoin (subvP_adjoin hx). Qed.

Lemma lazard_two_square_epsilon_mem_second B epsilon t :
  epsilon \in lazard_two_square_second_field B epsilon t.
Proof. exact: subvP_adjoin memv_adjoin. Qed.

Lemma lazard_two_square_t_mem_second B epsilon t :
  t \in lazard_two_square_second_field B epsilon t.
Proof. exact: memv_adjoin. Qed.

Lemma lazard_three_square_base_mem_third B epsilon t u x :
  x \in B -> x \in lazard_three_square_third_field B epsilon t u.
Proof.
move=> hx.
exact: subvP_adjoin (lazard_two_square_base_mem_second epsilon t hx).
Qed.

Lemma lazard_three_square_epsilon_mem_third B epsilon t u :
  epsilon \in lazard_three_square_third_field B epsilon t u.
Proof.
exact: subvP_adjoin
  (lazard_two_square_epsilon_mem_second B epsilon t).
Qed.

Lemma lazard_three_square_t_mem_third B epsilon t u :
  t \in lazard_three_square_third_field B epsilon t u.
Proof. exact: subvP_adjoin (lazard_two_square_t_mem_second B epsilon t). Qed.

Lemma lazard_three_square_u_mem_third B epsilon t u :
  u \in lazard_three_square_third_field B epsilon t u.
Proof. exact: memv_adjoin. Qed.

Theorem lazard_two_square_second_field_is_radical
    (B : {subfield L}) (epsilon t : L)
    (hepsilon : epsilon ^+ 2 \in B)
    (ht : t ^+ 2 \in lazard_two_square_first_field B epsilon) :
  @O.radical_extension F0 L B
    (lazard_two_square_second_field B epsilon t).
Proof.
have hstep1 : @O.simple_radical_step F0 L B
    (lazard_two_square_first_field B epsilon).
  exists epsilon, 2.
  split; first by [].
  split; first exact hepsilon.
  reflexivity.
have hrad1 : @O.radical_extension F0 L B
    (lazard_two_square_first_field B epsilon) :=
  @O.RadicalExtensionStep F0 L B B
    (lazard_two_square_first_field B epsilon)
    (@O.RadicalExtensionRefl F0 L B) hstep1.
have hstep2 : @O.simple_radical_step F0 L
    (lazard_two_square_first_field B epsilon)
    (lazard_two_square_second_field B epsilon t).
  exists t, 2.
  split; first by [].
  split; first exact ht.
  reflexivity.
exact: (@O.RadicalExtensionStep F0 L B
  (lazard_two_square_first_field B epsilon)
  (lazard_two_square_second_field B epsilon t) hrad1 hstep2).
Qed.

Theorem lazard_three_square_third_field_is_radical
    (B : {subfield L}) (epsilon t u : L)
    (hepsilon : epsilon ^+ 2 \in B)
    (ht : t ^+ 2 \in lazard_two_square_first_field B epsilon)
    (hu : u ^+ 2 \in lazard_two_square_second_field B epsilon t) :
  @O.radical_extension F0 L B
    (lazard_three_square_third_field B epsilon t u).
Proof.
have htwo := lazard_two_square_second_field_is_radical hepsilon ht.
have hstep : @O.simple_radical_step F0 L
    (lazard_two_square_second_field B epsilon t)
    (lazard_three_square_third_field B epsilon t u).
  exists u, 2.
  split; first by [].
  split; first exact hu.
  reflexivity.
exact: (@O.RadicalExtensionStep F0 L B
  (lazard_two_square_second_field B epsilon t)
  (lazard_three_square_third_field B epsilon t u) htwo hstep).
Qed.

(** The branch whose transformed zeroth Fourier coordinate is coordinate
    [j] in Lazard's orbit order [P1,P2,P4,P3]. *)
Definition lazard_branch_for_orbit_index (j : 'I_4) : Q.lazard_sign_branch :=
  nth Q.LazardBranchBase
    [:: Q.LazardBranchBase; Q.LazardBranchRotateNegate;
        Q.LazardBranchNegateTU; Q.LazardBranchRotate] j.

Lemma lazard_coherent_source_branch_for_orbit_index
    (source : 'I_4 -> L) (j : 'I_4) :
  CB.lazard_coherent_source_for_branch source
      (lazard_branch_for_orbit_index j) P.p0 = source j.
Proof.
case: j=> [[|[|[|[|j]]]] hj] //=;
by rewrite /lazard_branch_for_orbit_index
  /CB.lazard_coherent_source_for_branch
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_negate_source
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_source
  /PolynomialFormulasLazardQuinticQ1ProjectionBridge.lazard_rotate_negate_source
  /P.p0 /P.p1 /P.p2 /P.p3.
Qed.

Lemma lazard_branch_epsilon_neq0
    (v : Q.lazard_quadratic_triple L) branch :
  Q.lazard_epsilon v != 0 ->
  Q.lazard_epsilon (Q.lazard_branch_triple v branch) != 0.
Proof. by case: branch=> /=; rewrite ?oppr_eq0. Qed.

Lemma lazard_coherent_alternate_denominator_branch_neq0
    (v : Q.lazard_quadratic_triple L) branch :
  C.lazard_coherent_alternate_denominator
      (Q.lazard_t v) (Q.lazard_u v) != 0 ->
  C.lazard_coherent_alternate_denominator
      (Q.lazard_t (Q.lazard_branch_triple v branch))
      (Q.lazard_u (Q.lazard_branch_triple v branch)) != 0.
Proof.
case: v=> epsilon t u /=.
case: branch=> /= hden;
rewrite /C.lazard_coherent_alternate_denominator in hden *.
- exact hden.
- by rewrite !expr2 !mulNr mulrNN opprK in hden *.
- apply/eqP=> hzero; apply/eqP: hden.
  move/eqP: hzero=> hzero.
  apply/eqP.
  rewrite !expr2 !mulNr mulNr mulrN in hzero *.
  move: hzero.
  P.lazard_projection_ring.
- apply/eqP=> hzero; apply/eqP: hden.
  move/eqP: hzero=> hzero.
  apply/eqP.
  rewrite !expr2 !mulNr mulNr mulrN in hzero *.
  move: hzero.
  P.lazard_projection_ring.
Qed.

(** Inverting the coherent projection after the branch assigned to [j]
    recovers the [j]-th source coordinate.  This packages the four inverse
    rows without expanding another large matrix. *)
Theorem lazard_coherent_alternate_recover_orbit_coordinate
    (v : Q.lazard_quadratic_triple L) (source : 'I_4 -> L) (j : 'I_4)
    (two_neq0 : (2%:R : L) != 0)
    (epsilon_neq0 : Q.lazard_epsilon v != 0)
    (denominator_neq0 :
      C.lazard_coherent_alternate_denominator
        (Q.lazard_t v) (Q.lazard_u v) != 0) :
  C.lazard_coherent_alternate_recover
      (Q.lazard_epsilon
        (Q.lazard_branch_triple v (lazard_branch_for_orbit_index j)))
      (Q.lazard_t
        (Q.lazard_branch_triple v (lazard_branch_for_orbit_index j)))
      (Q.lazard_u
        (Q.lazard_branch_triple v (lazard_branch_for_orbit_index j)))
      (C.lazard_coherent_alternate_projections
        (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v) source) =
    source j.
Proof.
pose branch := lazard_branch_for_orbit_index j.
have hproj :
    C.lazard_coherent_alternate_projections
      (Q.lazard_epsilon (Q.lazard_branch_triple v branch))
      (Q.lazard_t (Q.lazard_branch_triple v branch))
      (Q.lazard_u (Q.lazard_branch_triple v branch))
      (CB.lazard_coherent_source_for_branch source branch) =
    C.lazard_coherent_alternate_projections
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v) source.
  apply/funext=> k.
  exact: CB.lazard_coherent_alternate_projections_branch.
rewrite -hproj.
rewrite (C.lazard_coherent_alternate_recover_projections
  two_neq0 (lazard_branch_epsilon_neq0 branch epsilon_neq0)
  (lazard_coherent_alternate_denominator_branch_neq0
    branch denominator_neq0)).
exact: lazard_coherent_source_branch_for_orbit_index.
Qed.

Definition lazard_four_fifth_field0
    (B2 : {subfield L}) (source : 'I_4 -> L) : {subfield L} :=
  <<B2; source P.p0>>%AS.

Definition lazard_four_fifth_field1
    (B2 : {subfield L}) (source : 'I_4 -> L) : {subfield L} :=
  <<lazard_four_fifth_field0 B2 source; source P.p1>>%AS.

Definition lazard_four_fifth_field2
    (B2 : {subfield L}) (source : 'I_4 -> L) : {subfield L} :=
  <<lazard_four_fifth_field1 B2 source; source P.p2>>%AS.

Definition lazard_four_fifth_generated_field
    (B2 : {subfield L}) (source : 'I_4 -> L) : {subfield L} :=
  <<lazard_four_fifth_field2 B2 source; source P.p3>>%AS.

Definition lazard_four_fifth_field_with_root
    (B2 : {subfield L}) (source : 'I_4 -> L) (omega : L) : {subfield L} :=
  <<lazard_four_fifth_generated_field B2 source; omega>>%AS.

Lemma lazard_four_fifth_base_mem_generated B2 source x :
  x \in B2 -> x \in lazard_four_fifth_generated_field B2 source.
Proof.
move=> hx.
apply: subvP_adjoin.
apply: subvP_adjoin.
apply: subvP_adjoin.
exact: subvP_adjoin hx.
Qed.

Lemma lazard_four_fifth_source_mem_generated B2 source j :
  source j \in lazard_four_fifth_generated_field B2 source.
Proof.
case: j=> [[|[|[|[|j]]]] hj] //=.
- apply: subvP_adjoin; apply: subvP_adjoin; apply: subvP_adjoin.
  exact: memv_adjoin.
- apply: subvP_adjoin; apply: subvP_adjoin.
  exact: memv_adjoin.
- apply: subvP_adjoin.
  exact: memv_adjoin.
- exact: memv_adjoin.
Qed.

(** Extend any already-radical two-square field by the four selected fifth
    roots.  Each step uses its explicit fifth-power membership; no degree
    argument or kernel special case is involved. *)
Theorem lazard_four_fifth_generated_field_is_radical
    (B B2 : {subfield L}) (source : 'I_4 -> L)
    (hB2 : @O.radical_extension F0 L B B2)
    (hpow : forall j : 'I_4, source j ^+ 5 \in B2) :
  @O.radical_extension F0 L B
    (lazard_four_fifth_generated_field B2 source).
Proof.
have hstep0 : @O.simple_radical_step F0 L B2
    (lazard_four_fifth_field0 B2 source).
  exists (source P.p0), 5.
  split; first by [].
  split; first exact: hpow P.p0.
  reflexivity.
have hrad0 : @O.radical_extension F0 L B
    (lazard_four_fifth_field0 B2 source) :=
  @O.RadicalExtensionStep F0 L B B2
    (lazard_four_fifth_field0 B2 source) hB2 hstep0.
have hstep1 : @O.simple_radical_step F0 L
    (lazard_four_fifth_field0 B2 source)
    (lazard_four_fifth_field1 B2 source).
  exists (source P.p1), 5.
  split; first by [].
  split.
  - exact: subvP_adjoin (hpow P.p1).
  - reflexivity.
have hrad1 : @O.radical_extension F0 L B
    (lazard_four_fifth_field1 B2 source) :=
  @O.RadicalExtensionStep F0 L B
    (lazard_four_fifth_field0 B2 source)
    (lazard_four_fifth_field1 B2 source) hrad0 hstep1.
have hstep2 : @O.simple_radical_step F0 L
    (lazard_four_fifth_field1 B2 source)
    (lazard_four_fifth_field2 B2 source).
  exists (source P.p2), 5.
  split; first by [].
  split.
  - apply: subvP_adjoin.
    exact: subvP_adjoin (hpow P.p2).
  - reflexivity.
have hrad2 : @O.radical_extension F0 L B
    (lazard_four_fifth_field2 B2 source) :=
  @O.RadicalExtensionStep F0 L B
    (lazard_four_fifth_field1 B2 source)
    (lazard_four_fifth_field2 B2 source) hrad1 hstep2.
have hstep3 : @O.simple_radical_step F0 L
    (lazard_four_fifth_field2 B2 source)
    (lazard_four_fifth_generated_field B2 source).
  exists (source P.p3), 5.
  split; first by [].
  split.
  - apply: subvP_adjoin; apply: subvP_adjoin.
    exact: subvP_adjoin (hpow P.p3).
  - reflexivity.
exact: (@O.RadicalExtensionStep F0 L B
  (lazard_four_fifth_field2 B2 source)
  (lazard_four_fifth_generated_field B2 source) hrad2 hstep3).
Qed.

Theorem lazard_four_fifth_field_with_primitive_root_is_radical
    (B B2 : {subfield L}) (source : 'I_4 -> L)
    (hB2 : @O.radical_extension F0 L B B2)
    (hpow : forall j : 'I_4, source j ^+ 5 \in B2)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  @O.radical_extension F0 L B
    (lazard_four_fifth_field_with_root B2 source omega).
Proof.
have hfour := lazard_four_fifth_generated_field_is_radical hB2 hpow.
have hstep : @O.simple_radical_step F0 L
    (lazard_four_fifth_generated_field B2 source)
    (lazard_four_fifth_field_with_root B2 source omega).
  exists omega, 5.
  split; first by [].
  split.
  - rewrite (prim_expr_order omega_primitive).
    exact: mem1v.
  - reflexivity.
exact: (@O.RadicalExtensionStep F0 L B
  (lazard_four_fifth_generated_field B2 source)
  (lazard_four_fifth_field_with_root B2 source omega) hfour hstep).
Qed.

(** All four Fourier generators and the primitive fifth root lie in the
    final robust field, hence so do all five inverse-Fourier values. *)
Theorem lazard_four_fifth_inverse_fourier_output_mem
    (B2 : {subfield L}) (source : 'I_4 -> L) (omega : L) (k : 'I_5) :
  V.lazard_inverse_fourier_output omega
      (source P.p0) (source P.p1) (source P.p3) (source P.p2) k \in
    lazard_four_fifth_field_with_root B2 source omega.
Proof.
rewrite /V.lazard_inverse_fourier_output
  /V.lazard_inverse_fourier_unscaled.
have homega : omega \in
    lazard_four_fifth_field_with_root B2 source omega := memv_adjoin.
have hsource j : source j \in
    lazard_four_fifth_field_with_root B2 source omega :=
  subvP_adjoin (lazard_four_fifth_source_mem_generated B2 source j).
apply: rpredM.
- exact: rpredV (CRT.lazard_natr_mem _ 5).
- apply: rpredD.
  + apply: rpredD.
    * apply: rpredD.
      -- exact: rpredM (rpredX homega) (hsource P.p0).
      -- exact: rpredM (rpredX homega) (hsource P.p1).
    * exact: rpredM (rpredX homega) (hsource P.p3).
  + exact: rpredM (rpredX homega) (hsource P.p2).
Qed.

End AlternateCertificateTower.

Print Assumptions lazard_coherent_alternate_recover_mem_second.
Print Assumptions
  lazard_alternate_generated_field_has_two_square_fifth_presentation.
Print Assumptions lazard_alternate_generated_field_is_radical.
Print Assumptions lazard_alternate_all_outputs_in_radical_extension.
Print Assumptions lazard_four_fifth_generated_field_is_radical.
Print Assumptions
  lazard_four_fifth_field_with_primitive_root_is_radical.
Print Assumptions lazard_four_fifth_inverse_fourier_output_mem.

End PolynomialFormulasLazardQuinticAlternateCertificateRadicalTower.
