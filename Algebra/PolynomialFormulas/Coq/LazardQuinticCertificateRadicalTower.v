From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticQ1Branches LazardQuinticFourierNumerators
  LazardQuinticVieta LazardOptimality
  LazardOptimalityTheoremFourDegree.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A proof-carrying square/square/fifth-root tower for Lazard's displayed
    quintic formula.  In contrast with the root-origin files, this interface
    does not claim that the supplied radical choices come from polynomial
    roots.  It records their three defining power equations and then proves,
    without assuming any output-membership facts, that every displayed
    formula belongs to the generated radical extension. *)
Module PolynomialFormulasLazardQuinticCertificateRadicalTower.

Import GRing.Theory.
Local Open Scope ring_scope.

Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module Q1 := PolynomialFormulasLazardQuinticQ1Branches.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module V := PolynomialFormulasLazardQuinticVieta.
Module O := PolynomialFormulasLazardOptimality.
Module T4 := PolynomialFormulasLazardOptimalityTheoremFourDegree.

Section CertificateTower.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (B E M : {subfield L}).
Implicit Types (omega x : L).

(** The eight coefficient-side quantities needed by the three power
    equations and the Fourier denominators lie in the base field.  [E] is
    the already defined Coq expression [lazard_invariant_E c i]. *)
Record lazard_radical_invariant_data_in
    (B : {subfield L})
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L)
    (D Finvariant G H I J K : L) : Prop :=
  LazardRadicalInvariantDataIn {
    lazard_D_in_base : D \in B;
    lazard_E_in_base : FN.lazard_invariant_E c i \in B;
    lazard_F_in_base : Finvariant \in B;
    lazard_G_in_base : G \in B;
    lazard_H_in_base : H \in B;
    lazard_I_in_base : I \in B;
    lazard_J_in_base : J \in B;
    lazard_K_in_base : K \in B
  }.

(** The ten coefficient numerators in Lazard's formulas for P4, P3, and P2
    lie in the base field.  These are input-coefficient facts, rather than
    assumptions that the final formula values already lie in the tower. *)
Record lazard_fourier_numerator_data_in
    (B : {subfield L})
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L) : Prop :=
  LazardFourierNumeratorDataIn {
    lazard_p41_in_base : FN.lazard_p41 c \in B;
    lazard_p42_in_base : FN.lazard_p42 c i \in B;
    lazard_p31_in_base : FN.lazard_p31 c \in B;
    lazard_p32_in_base : FN.lazard_p32 c i \in B;
    lazard_p33_in_base : FN.lazard_p33 c i \in B;
    lazard_p34_in_base : FN.lazard_p34 c i \in B;
    lazard_p21_in_base : FN.lazard_p21 c i \in B;
    lazard_p22_in_base : FN.lazard_p22 c i \in B;
    lazard_p23_in_base : FN.lazard_p23 c i \in B;
    lazard_p24_in_base : FN.lazard_p24 c i \in B
  }.

(** A deliberately small certificate.  Besides the three radical power
    equations, the only extra equality defines Lazard's auxiliary [u] from
    the first two radical choices.  In particular, membership of P2/P3/P4
    and of the inverse-Fourier outputs is not stored in this record. *)
Record lazard_radical_certificate
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L)
    (D Finvariant G H I J K : L) :=
  LazardRadicalCertificate {
    lazard_certificate_initial : Q.lazard_quadratic_triple L;
    lazard_certificate_branch : Q.lazard_sign_branch;
    lazard_certificate_p1 : L;
    lazard_certificate_epsilon_square :
      Q.lazard_epsilon lazard_certificate_initial ^+ 2 = 5%:R * D;
    lazard_certificate_t_square :
      Q.lazard_t lazard_certificate_initial ^+ 2 =
        ((5%:R : L) / (2%:R : L)) *
          (FN.lazard_invariant_E c i +
            Finvariant / Q.lazard_epsilon lazard_certificate_initial);
    lazard_certificate_u_formula :
      Q.lazard_u lazard_certificate_initial =
        5%:R * G /
          (Q.lazard_t lazard_certificate_initial *
            Q.lazard_epsilon lazard_certificate_initial);
    lazard_certificate_p1_fifth :
      lazard_certificate_p1 ^+ 5 =
        Q1.lazard_q1 H I J K (FN.lazard_invariant_E c i)
          (Q.lazard_branch_triple lazard_certificate_initial
            lazard_certificate_branch)
  }.

Definition lazard_certificate_chosen c i D Finvariant G H I J K
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
    Q.lazard_quadratic_triple L :=
  Q.lazard_branch_triple (lazard_certificate_initial d)
    (lazard_certificate_branch d).

(** The three actual subfields in the certificate tower. *)
Definition lazard_certificate_first_field c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
    {subfield L} :=
  <<B; Q.lazard_epsilon (lazard_certificate_initial d)>>%AS.

Definition lazard_certificate_second_field c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
    {subfield L} :=
  <<lazard_certificate_first_field B d;
    Q.lazard_t (lazard_certificate_initial d)>>%AS.

Definition lazard_certificate_generated_field c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
    {subfield L} :=
  <<lazard_certificate_second_field B d; lazard_certificate_p1 d>>%AS.

Definition lazard_certificate_field_with_root c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (omega : L) : {subfield L} :=
  <<lazard_certificate_generated_field B d; omega>>%AS.

Record lazard_quadratic_triple_in
    (E : {subfield L}) (v : Q.lazard_quadratic_triple L) : Prop :=
  LazardQuadraticTripleIn {
    lazard_triple_epsilon_in : Q.lazard_epsilon v \in E;
    lazard_triple_t_in : Q.lazard_t v \in E;
    lazard_triple_u_in : Q.lazard_u v \in E
  }.

Lemma lazard_natr_mem (E : {subfield L}) n : (n%:R : L) \in E.
Proof. by rewrite rpred_nat. Qed.

Lemma lazard_quadratic_triple_in_branch E v branch :
  lazard_quadratic_triple_in E v ->
  lazard_quadratic_triple_in E (Q.lazard_branch_triple v branch).
Proof.
case=> he ht hu; case: branch=> /=; constructor=> //; by rewrite rpredN.
Qed.

Lemma lazard_certificate_base_mem_first c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K) (x : L) :
  x \in B -> x \in lazard_certificate_first_field B d.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_certificate_first_mem_second c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K) (x : L) :
  x \in lazard_certificate_first_field B d ->
  x \in lazard_certificate_second_field B d.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_certificate_second_mem_generated c i D Finvariant G H I J K
    (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K) (x : L) :
  x \in lazard_certificate_second_field B d ->
  x \in lazard_certificate_generated_field B d.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_certificate_generated_mem_with_root
    c i D Finvariant G H I J K (B : {subfield L})
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (omega x : L) :
  x \in lazard_certificate_generated_field B d ->
  x \in lazard_certificate_field_with_root B d omega.
Proof. exact: subvP_adjoin. Qed.

Lemma lazard_certificate_base_mem_second c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K) x :
  x \in B -> x \in lazard_certificate_second_field B d.
Proof.
move=> hx.
exact: lazard_certificate_first_mem_second
  (lazard_certificate_base_mem_first d hx).
Qed.

Lemma lazard_certificate_base_mem_generated c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K) x :
  x \in B -> x \in lazard_certificate_generated_field B d.
Proof.
move=> hx.
exact: lazard_certificate_second_mem_generated
  (lazard_certificate_base_mem_second d hx).
Qed.

Lemma lazard_certificate_epsilon_mem_first c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
  Q.lazard_epsilon (lazard_certificate_initial d) \in
    lazard_certificate_first_field B d.
Proof. exact: memv_adjoin. Qed.

Lemma lazard_certificate_t_mem_second c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
  Q.lazard_t (lazard_certificate_initial d) \in
    lazard_certificate_second_field B d.
Proof. exact: memv_adjoin. Qed.

Lemma lazard_certificate_p1_mem_generated c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
  lazard_certificate_p1 d \in lazard_certificate_generated_field B d.
Proof. exact: memv_adjoin. Qed.

(** To place the complete certificate field inside an independently known
    ambient subfield it is enough to place the three actual generators
    there.  This is the elimination rule for the square/square/fifth-root
    tower, factored out so root-origin applications do not need to unfold
    the same three nested adjunctions. *)
Lemma lazard_certificate_generated_field_le
    c i D Finvariant G H I J K B M
    (d : lazard_radical_certificate c i D Finvariant G H I J K) :
  (B <= M)%VS ->
  Q.lazard_epsilon (lazard_certificate_initial d) \in M ->
  Q.lazard_t (lazard_certificate_initial d) \in M ->
  lazard_certificate_p1 d \in M ->
  (lazard_certificate_generated_field B d <= M)%VS.
Proof.
move=> hBM hepsilon ht hp1.
rewrite /lazard_certificate_generated_field
  /lazard_certificate_second_field /lazard_certificate_first_field.
apply/FadjoinP; split.
- apply/FadjoinP; split.
  + apply/FadjoinP; split.
    * exact: hBM.
    * exact: hepsilon.
  + exact: ht.
- exact: hp1.
Qed.

Lemma lazard_certificate_omega_mem_with_root
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    omega :
  omega \in lazard_certificate_field_with_root B d omega.
Proof. exact: memv_adjoin. Qed.

(** The initial triple is present after the two square adjunctions.  The
    proof derives [u]-membership from its defining rational expression. *)
Theorem lazard_certificate_initial_mem_second
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  lazard_quadratic_triple_in
    (lazard_certificate_second_field B d)
    (lazard_certificate_initial d).
Proof.
constructor.
- exact: lazard_certificate_first_mem_second
    (lazard_certificate_epsilon_mem_first B d).
- exact: lazard_certificate_t_mem_second B d.
- rewrite (lazard_certificate_u_formula d).
  apply: rpred_div.
  + apply: rpredM; first exact: lazard_natr_mem.
    exact (lazard_certificate_base_mem_second d (lazard_G_in_base hdata)).
  + apply: rpredM.
    * exact: lazard_certificate_t_mem_second B d.
    * exact: lazard_certificate_first_mem_second
        (lazard_certificate_epsilon_mem_first B d).
Qed.

Theorem lazard_certificate_chosen_mem_second
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  lazard_quadratic_triple_in (lazard_certificate_second_field B d)
    (lazard_certificate_chosen d).
Proof.
exact: lazard_quadratic_triple_in_branch
  (lazard_certificate_initial_mem_second d hdata).
Qed.

(** The selected Q1 value is in the second square-root field, so the stored
    fifth-root equation really is a legal third radical step. *)
Theorem lazard_certificate_p1_fifth_mem_second
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  lazard_certificate_p1 d ^+ 5 \in
    lazard_certificate_second_field B d.
Proof.
rewrite (lazard_certificate_p1_fifth d)
  /Q1.lazard_q1 /Q1.lazard_q1_inner.
have hv := lazard_certificate_chosen_mem_second d hdata.
have hscale : ((5%:R : L) / (4%:R : L)) \in
    lazard_certificate_second_field B d.
  exact: rpred_div (lazard_natr_mem _ 5) (lazard_natr_mem _ 4).
have hH := lazard_certificate_base_mem_second d (lazard_H_in_base hdata).
have hI := lazard_certificate_base_mem_second d (lazard_I_in_base hdata).
have hJ := lazard_certificate_base_mem_second d (lazard_J_in_base hdata).
have hK := lazard_certificate_base_mem_second d (lazard_K_in_base hdata).
have hE := lazard_certificate_base_mem_second d (lazard_E_in_base hdata).
apply: rpredM; first exact hscale.
apply: rpredD.
- apply: rpredD; first exact hH.
  exact: rpred_div hI (lazard_triple_epsilon_in hv).
- apply: rpred_div; last exact hE.
  apply: rpredD.
  + exact: rpredM (lazard_triple_t_in hv) hJ.
  + exact: rpredM (lazard_triple_u_in hv) hK.
Qed.

(** The certificate has the exact presentation asserted by its syntax: two
    square-root adjunctions followed by one fifth-root adjunction.  The count
    is proved from the displayed power equations, not inferred from degree. *)
Theorem lazard_certificate_generated_field_has_two_square_fifth_presentation
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @T4.square_roots_and_fifth_root_presentation F0 L B
    (lazard_certificate_generated_field B d) 2.
Proof.
have hepsilon : Q.lazard_epsilon (lazard_certificate_initial d) ^+ 2 \in B.
  rewrite (lazard_certificate_epsilon_square d).
  exact: rpredM (lazard_natr_mem B 5) (lazard_D_in_base hdata).
have ht : Q.lazard_t (lazard_certificate_initial d) ^+ 2 \in
    lazard_certificate_first_field B d.
  rewrite (lazard_certificate_t_square d).
  apply: rpredM.
  - exact: rpred_div (lazard_natr_mem _ 5) (lazard_natr_mem _ 2).
  - apply: rpredD.
    + exact (lazard_certificate_base_mem_first d
        (lazard_E_in_base hdata)).
    + exact (rpred_div
        (lazard_certificate_base_mem_first d (lazard_F_in_base hdata))
        (lazard_certificate_epsilon_mem_first B d)).
have hzero : @T4.square_radical_tower F0 L B 0 B :=
  @T4.SquareRadicalTowerZero F0 L B.
have hfirst : @T4.square_radical_tower F0 L B 1
    (lazard_certificate_first_field B d).
  rewrite /lazard_certificate_first_field.
  exact: (T4.SquareRadicalTowerStep hzero hepsilon).
have hsecond : @T4.square_radical_tower F0 L B 2
    (lazard_certificate_second_field B d).
  rewrite /lazard_certificate_second_field.
  exact: (T4.SquareRadicalTowerStep hfirst ht).
refine (@T4.SquareRootsAndFifthRootPresentation
  F0 L B (lazard_certificate_generated_field B d) 2
  (lazard_certificate_second_field B d) hsecond
  (lazard_certificate_p1 d)
  (lazard_certificate_p1_fifth_mem_second d hdata) _).
by rewrite /lazard_certificate_generated_field.
Qed.

Theorem lazard_certificate_first_simple_radical_step
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @O.simple_radical_step F0 L B (lazard_certificate_first_field B d).
Proof.
exists (Q.lazard_epsilon (lazard_certificate_initial d)), 2.
split; first by [].
split.
- rewrite (lazard_certificate_epsilon_square d).
  exact: rpredM (lazard_natr_mem B 5) (lazard_D_in_base hdata).
- reflexivity.
Qed.

Theorem lazard_certificate_second_simple_radical_step
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @O.simple_radical_step F0 L
    (lazard_certificate_first_field B d)
    (lazard_certificate_second_field B d).
Proof.
exists (Q.lazard_t (lazard_certificate_initial d)), 2.
split; first by [].
split.
- rewrite (lazard_certificate_t_square d).
  apply: rpredM.
  + exact: rpred_div (lazard_natr_mem _ 5) (lazard_natr_mem _ 2).
  + apply: rpredD.
    * exact (lazard_certificate_base_mem_first d (lazard_E_in_base hdata)).
    * apply: rpred_div.
      -- exact (lazard_certificate_base_mem_first d
          (lazard_F_in_base hdata)).
      -- exact: lazard_certificate_epsilon_mem_first B d.
- reflexivity.
Qed.

Theorem lazard_certificate_third_simple_radical_step
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @O.simple_radical_step F0 L
    (lazard_certificate_second_field B d)
    (lazard_certificate_generated_field B d).
Proof.
exists (lazard_certificate_p1 d), 5.
split; first by [].
split; first exact (lazard_certificate_p1_fifth_mem_second d hdata).
reflexivity.
Qed.

(** The certificate constructs an honest three-step radical extension:
    square root, square root, then fifth root. *)
Theorem lazard_certificate_generated_field_is_radical
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @O.radical_extension F0 L B (lazard_certificate_generated_field B d).
Proof.
exact: T4.square_roots_and_fifth_root_is_radical
  (lazard_certificate_generated_field_has_two_square_fifth_presentation
    d hdata).
Qed.

(** Lazard's displayed P4 is generated by the certificate radicals. *)
Theorem lazard_certificate_P4_mem_generated
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (hnum : lazard_fourier_numerator_data_in B c i) :
  FN.lazard_fourier_P4_formula c i (lazard_certificate_chosen d)
      (lazard_certificate_p1 d) \in
    lazard_certificate_generated_field B d.
Proof.
rewrite /FN.lazard_fourier_P4_formula.
have hv2 := lazard_certificate_chosen_mem_second d hdata.
have he := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_epsilon_in hv2).
have hp := lazard_certificate_p1_mem_generated B d.
apply: rpredD.
- apply: rpred_div.
  + exact (lazard_certificate_base_mem_generated d
      (lazard_p41_in_base hnum)).
  + exact: rpredM (lazard_natr_mem _ 2) hp.
- apply: rpred_div.
  + exact (lazard_certificate_base_mem_generated d
      (lazard_p42_in_base hnum)).
  + exact: rpredM (rpredM (lazard_natr_mem _ 2) he) hp.
Qed.

(** Lazard's displayed P3 is generated by the certificate radicals. *)
Theorem lazard_certificate_P3_mem_generated
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (hnum : lazard_fourier_numerator_data_in B c i) :
  FN.lazard_fourier_P3_formula c i (lazard_certificate_chosen d)
      (lazard_certificate_p1 d) \in
    lazard_certificate_generated_field B d.
Proof.
rewrite /FN.lazard_fourier_P3_formula.
have hv2 := lazard_certificate_chosen_mem_second d hdata.
have he := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_epsilon_in hv2).
have ht := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_t_in hv2).
have hu := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_u_in hv2).
have hp := lazard_certificate_p1_mem_generated B d.
have hp2 : lazard_certificate_p1 d ^+ 2 \in
    lazard_certificate_generated_field B d by exact: rpredX hp.
apply: rpredD.
- apply: rpredD.
  + apply: rpred_div.
    * exact (lazard_certificate_base_mem_generated d
        (lazard_p31_in_base hnum)).
    * exact: rpredM (lazard_natr_mem _ 4) hp2.
  + apply: rpred_div.
    * exact (lazard_certificate_base_mem_generated d
        (lazard_p32_in_base hnum)).
    * exact: rpredM (rpredM (lazard_natr_mem _ 4) he) hp2.
- apply: rpred_div.
  + apply: rpredD.
    * exact (rpredM
        (lazard_certificate_base_mem_generated d
          (lazard_p33_in_base hnum)) ht).
    * exact (rpredM
        (lazard_certificate_base_mem_generated d
          (lazard_p34_in_base hnum)) hu).
  + exact (rpredM
      (rpredM (lazard_natr_mem _ 10)
        (lazard_certificate_base_mem_generated d
          (lazard_E_in_base hdata))) hp2).
Qed.

(** Lazard's corrected displayed P2 is generated by the certificate
    radicals. *)
Theorem lazard_certificate_P2_mem_generated
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (hnum : lazard_fourier_numerator_data_in B c i) :
  FN.lazard_fourier_P2_formula c i (lazard_certificate_chosen d)
      (lazard_certificate_p1 d) \in
    lazard_certificate_generated_field B d.
Proof.
rewrite /FN.lazard_fourier_P2_formula.
have hv2 := lazard_certificate_chosen_mem_second d hdata.
have he := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_epsilon_in hv2).
have ht := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_t_in hv2).
have hu := lazard_certificate_second_mem_generated
  (d := d) (lazard_triple_u_in hv2).
have hp := lazard_certificate_p1_mem_generated B d.
have hp3 : lazard_certificate_p1 d ^+ 3 \in
    lazard_certificate_generated_field B d by exact: rpredX hp.
apply: rpredD.
- apply: rpredD.
  + apply: rpred_div.
    * exact (lazard_certificate_base_mem_generated d
        (lazard_p21_in_base hnum)).
    * exact: rpredM (lazard_natr_mem _ 4) hp3.
  + apply: rpred_div.
    * exact (lazard_certificate_base_mem_generated d
        (lazard_p22_in_base hnum)).
    * exact: rpredM (rpredM (lazard_natr_mem _ 4) he) hp3.
- apply: rpred_div.
  + apply: rpredD.
    * exact (rpredM
        (lazard_certificate_base_mem_generated d
          (lazard_p23_in_base hnum)) ht).
    * exact (rpredM
        (lazard_certificate_base_mem_generated d
          (lazard_p24_in_base hnum)) hu).
  + exact (rpredM
      (rpredM (lazard_natr_mem _ 10)
        (lazard_certificate_base_mem_generated d
          (lazard_E_in_base hdata))) hp3).
Qed.

(** The zero-index inverse-Fourier value needs no adjunction of [omega]:
    every exponent occurring at index zero is zero.  This is the one-root
    membership statement used by Lazard's Theorem 3; the remaining four
    outputs genuinely use the primitive fifth root. *)
Theorem lazard_certificate_inverse_fourier_output_zero_mem_generated
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (hnum : lazard_fourier_numerator_data_in B c i)
    (omega : L) :
  V.lazard_inverse_fourier_output omega
      (lazard_certificate_p1 d)
      (FN.lazard_fourier_P2_formula c i (lazard_certificate_chosen d)
        (lazard_certificate_p1 d))
      (FN.lazard_fourier_P3_formula c i (lazard_certificate_chosen d)
        (lazard_certificate_p1 d))
      (FN.lazard_fourier_P4_formula c i (lazard_certificate_chosen d)
        (lazard_certificate_p1 d)) (@ord0 4) \in
    lazard_certificate_generated_field B d.
Proof.
rewrite /V.lazard_inverse_fourier_output
  /V.lazard_inverse_fourier_unscaled /= !expr0 !mul1r.
have hp1 := lazard_certificate_p1_mem_generated B d.
have hp2 := lazard_certificate_P2_mem_generated d hdata hnum.
have hp3 := lazard_certificate_P3_mem_generated d hdata hnum.
have hp4 := lazard_certificate_P4_mem_generated d hdata hnum.
apply: rpredM.
- rewrite rpredV.
  exact: lazard_natr_mem _ 5.
- exact (rpredD (rpredD (rpredD hp1 hp2) hp3) hp4).
Qed.

(** Adjoining [omega] puts every one of the five inverse-Fourier values in
    a common field.  Primitivity is not needed merely for membership. *)
Theorem lazard_certificate_inverse_fourier_output_mem_with_root
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (hnum : lazard_fourier_numerator_data_in B c i)
    (omega : L) (k : 'I_5) :
  V.lazard_inverse_fourier_output omega
      (lazard_certificate_p1 d)
      (FN.lazard_fourier_P2_formula c i (lazard_certificate_chosen d)
        (lazard_certificate_p1 d))
      (FN.lazard_fourier_P3_formula c i (lazard_certificate_chosen d)
        (lazard_certificate_p1 d))
      (FN.lazard_fourier_P4_formula c i (lazard_certificate_chosen d)
        (lazard_certificate_p1 d)) k \in
    lazard_certificate_field_with_root B d omega.
Proof.
rewrite /V.lazard_inverse_fourier_output
  /V.lazard_inverse_fourier_unscaled.
have homega := lazard_certificate_omega_mem_with_root B d omega.
have hp1 := lazard_certificate_generated_mem_with_root (d := d) omega
  (lazard_certificate_p1_mem_generated B d).
have hp2 := lazard_certificate_generated_mem_with_root (d := d) omega
  (lazard_certificate_P2_mem_generated d hdata hnum).
have hp3 := lazard_certificate_generated_mem_with_root (d := d) omega
  (lazard_certificate_P3_mem_generated d hdata hnum).
have hp4 := lazard_certificate_generated_mem_with_root (d := d) omega
  (lazard_certificate_P4_mem_generated d hdata hnum).
apply: rpredM.
- rewrite rpredV.
  exact: lazard_natr_mem _ 5.
- apply: rpredD.
  + apply: rpredD.
    * apply: rpredD.
      -- apply: rpredM; last exact hp1.
         apply: rpredX; exact homega.
      -- apply: rpredM; last exact hp2.
         apply: rpredX; exact homega.
    * apply: rpredM; last exact hp3.
      apply: rpredX; exact homega.
  + apply: rpredM; last exact hp4.
    apply: rpredX; exact homega.
Qed.

(** A primitive fifth root is itself one more legal fifth-root radical
    adjunction, since its fifth power is 1. *)
Theorem lazard_certificate_field_with_primitive_root_is_radical
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  @O.radical_extension F0 L B
    (lazard_certificate_field_with_root B d omega).
Proof.
have hcert := lazard_certificate_generated_field_is_radical d hdata.
have hstep : @O.simple_radical_step F0 L
    (lazard_certificate_generated_field B d)
    (lazard_certificate_field_with_root B d omega).
  exists omega, 5.
  split; first by [].
  split.
  - rewrite (prim_expr_order omega_primitive).
    exact: mem1v.
  - reflexivity.
exact: (@O.RadicalExtensionStep F0 L B
  (lazard_certificate_generated_field B d)
  (lazard_certificate_field_with_root B d omega) hcert hstep).
Qed.

(** Public aggregate theorem: the generated field is radical over the base
    and contains all five formula outputs after a primitive fifth root is
    adjoined. *)
Theorem lazard_certificate_all_outputs_in_radical_extension
    c i D Finvariant G H I J K B
    (d : lazard_radical_certificate c i D Finvariant G H I J K)
    (hdata : lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K)
    (hnum : lazard_fourier_numerator_data_in B c i)
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  @O.radical_extension F0 L B
      (lazard_certificate_field_with_root B d omega) /\
    forall k : 'I_5,
      V.lazard_inverse_fourier_output omega
          (lazard_certificate_p1 d)
          (FN.lazard_fourier_P2_formula c i (lazard_certificate_chosen d)
            (lazard_certificate_p1 d))
          (FN.lazard_fourier_P3_formula c i (lazard_certificate_chosen d)
            (lazard_certificate_p1 d))
          (FN.lazard_fourier_P4_formula c i (lazard_certificate_chosen d)
            (lazard_certificate_p1 d)) k \in
        lazard_certificate_field_with_root B d omega.
Proof.
split.
- exact (lazard_certificate_field_with_primitive_root_is_radical
    d hdata omega_primitive).
- move=> k.
  exact (lazard_certificate_inverse_fourier_output_mem_with_root
    d hdata hnum omega k).
Qed.

End CertificateTower.

End PolynomialFormulasLazardQuinticCertificateRadicalTower.
