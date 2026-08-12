From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootProjections
  LazardQuinticDeterminantCertificateMatrix
  LazardCubicQuadraticElimination
  LazardQuinticDeterminantCriticalData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Small structural facts used to assemble the thirteen coefficient
    certificates.  This file contains no large scalar normalization. *)
Module PolynomialFormulasLazardQuinticDeterminantCriticalPolynomial.

Import GRing.Theory.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module DM := PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
Module CQ := PolynomialFormulasLazardCubicQuadraticElimination.
Module D := PolynomialFormulasLazardQuinticDeterminantCriticalData.
Local Open Scope ring_scope.

Section PolynomialFacts.

Variable F : fieldType.

Lemma lazard_detcritical_size_add_degree
    (p q : {poly F}) n :
  size p <= n.+1 -> size q <= n.+1 -> size (p + q) <= n.+1.
Proof.
move=> hp hq.
apply: leq_trans (size_polyD p q) _.
by rewrite maxn_leq hp hq.
Qed.

Lemma lazard_detcritical_size_sub_degree
    (p q : {poly F}) n :
  size p <= n.+1 -> size q <= n.+1 -> size (p - q) <= n.+1.
Proof.
move=> hp hq.
apply: leq_trans (size_polyD p (- q)) _.
by rewrite size_polyN maxn_leq hp hq.
Qed.

Lemma lazard_detcritical_size_scale_degree
    (a : F) (p : {poly F}) n :
  size p <= n.+1 -> size (a *: p) <= n.+1.
Proof. exact: leq_trans (size_scale_leq a p). Qed.

Lemma lazard_detcritical_size_mul_degree
    (p q : {poly F}) dp dq :
  size p <= dp.+1 -> size q <= dq.+1 ->
  size (p * q) <= (dp + dq).+1.
Proof.
move=> /leP hp /leP hq.
apply/leP.
have /leP hproduct := size_polyMleq p q.
lia.
Qed.

Lemma lazard_detcritical_size_exp_degree
    (p : {poly F}) dp n :
  size p <= dp.+1 ->
  size (p ^+ n) <= (dp * n).+1.
Proof.
move=> /leP hp.
apply/leP.
have /leP hpower := size_poly_exp_leq p n.
nia.
Qed.

Lemma lazard_detcritical_size_mul3_degree
    (p q r : {poly F}) dp dq dr :
  size p <= dp.+1 -> size q <= dq.+1 -> size r <= dr.+1 ->
  size (p * q * r) <= (dp + dq + dr).+1.
Proof.
move=> hp hq hr.
exact: lazard_detcritical_size_mul_degree
  (lazard_detcritical_size_mul_degree hp hq) hr.
Qed.

Lemma lazard_detcritical_size_mul4_degree
    (p q r t : {poly F}) dp dq dr dt :
  size p <= dp.+1 -> size q <= dq.+1 -> size r <= dr.+1 ->
  size t <= dt.+1 ->
  size (p * q * r * t) <= (dp + dq + dr + dt).+1.
Proof.
move=> hp hq hr ht.
exact: lazard_detcritical_size_mul_degree
  (lazard_detcritical_size_mul3_degree hp hq hr) ht.
Qed.

Lemma lazard_detcritical_size_mul5_degree
    (p q r t u : {poly F}) dp dq dr dt du :
  size p <= dp.+1 -> size q <= dq.+1 -> size r <= dr.+1 ->
  size t <= dt.+1 -> size u <= du.+1 ->
  size (p * q * r * t * u) <= (dp + dq + dr + dt + du).+1.
Proof.
move=> hp hq hr ht hu.
exact: lazard_detcritical_size_mul_degree
  (lazard_detcritical_size_mul4_degree hp hq hr ht) hu.
Qed.

Lemma lazard_detcritical_size_monomial (a : F) n :
  size (a%:P * 'X ^+ n) <= n.+1.
Proof.
rewrite mul_polyC.
apply: leq_trans (size_scale_leq a ('X ^+ n)) _.
by rewrite size_polyXn.
Qed.

Lemma lazard_detcritical_PA0_size c :
  size (D.lazard_detcritical_PA0 c) <= 3.
Proof.
rewrite /D.lazard_detcritical_PA0.
apply: lazard_detcritical_size_add_degree.
- apply: lazard_detcritical_size_add_degree.
  + exact: leq_trans (size_polyC_leq1 _) (isT : 1 <= 3).
  + exact: leq_trans (lazard_detcritical_size_monomial _ 1)
      (isT : 2 <= 3).
- exact: lazard_detcritical_size_monomial _ 2.
Qed.

Lemma lazard_detcritical_PA1_size c :
  size (D.lazard_detcritical_PA1 c) <= 2.
Proof.
rewrite /D.lazard_detcritical_PA1.
apply: lazard_detcritical_size_add_degree.
- exact: leq_trans (size_polyC_leq1 _) (isT : 1 <= 2).
- exact: lazard_detcritical_size_monomial _ 1.
Qed.

Lemma lazard_detcritical_PA2_size c :
  size (D.lazard_detcritical_PA2 c) <= 1.
Proof. exact: size_polyC_leq1 _. Qed.

Lemma lazard_detcritical_PA3_size c :
  size (D.lazard_detcritical_PA3 c) <= 1.
Proof. exact: size_polyC_leq1 _. Qed.

Lemma lazard_detcritical_PB0_size c :
  size (D.lazard_detcritical_PB0 c) <= 5.
Proof.
rewrite /D.lazard_detcritical_PB0.
apply: lazard_detcritical_size_add_degree.
- apply: lazard_detcritical_size_add_degree.
  + apply: lazard_detcritical_size_add_degree.
    * apply: lazard_detcritical_size_add_degree.
      -- exact: leq_trans (size_polyC_leq1 _) (isT : 1 <= 5).
      -- exact: leq_trans (lazard_detcritical_size_monomial _ 1)
           (isT : 2 <= 5).
    * exact: leq_trans (lazard_detcritical_size_monomial _ 2)
        (isT : 3 <= 5).
  + exact: leq_trans (lazard_detcritical_size_monomial _ 3)
      (isT : 4 <= 5).
- exact: lazard_detcritical_size_monomial _ 4.
Qed.

Lemma lazard_detcritical_PB1_size c :
  size (D.lazard_detcritical_PB1 c) <= 3.
Proof.
rewrite /D.lazard_detcritical_PB1.
apply: lazard_detcritical_size_add_degree.
- apply: lazard_detcritical_size_add_degree.
  + exact: leq_trans (size_polyC_leq1 _) (isT : 1 <= 3).
  + exact: leq_trans (lazard_detcritical_size_monomial _ 1)
      (isT : 2 <= 3).
- exact: lazard_detcritical_size_monomial _ 2.
Qed.

Lemma lazard_detcritical_PB2_size c :
  size (D.lazard_detcritical_PB2 c) <= 3.
Proof.
rewrite /D.lazard_detcritical_PB2.
apply: lazard_detcritical_size_add_degree.
- apply: lazard_detcritical_size_add_degree.
  + exact: leq_trans (size_polyC_leq1 _) (isT : 1 <= 3).
  + exact: leq_trans (lazard_detcritical_size_monomial _ 1)
      (isT : 2 <= 3).
- exact: lazard_detcritical_size_monomial _ 2.
Qed.

Lemma lazard_detcritical_N_polynomial_size c :
  size (D.lazard_detcritical_N_polynomial c) <= 7.
Proof.
rewrite /D.lazard_detcritical_N_polynomial.
apply: lazard_detcritical_size_add_degree.
- apply: lazard_detcritical_size_add_degree.
  + apply: lazard_detcritical_size_add_degree.
    * apply: lazard_detcritical_size_add_degree.
      -- apply: lazard_detcritical_size_add_degree.
         ++ exact: leq_trans (size_polyC_leq1 _) (isT : 1 <= 7).
         ++ exact: leq_trans (lazard_detcritical_size_monomial _ 1)
              (isT : 2 <= 7).
      -- exact: leq_trans (lazard_detcritical_size_monomial _ 2)
           (isT : 3 <= 7).
    * exact: leq_trans (lazard_detcritical_size_monomial _ 3)
        (isT : 4 <= 7).
  + exact: leq_trans (lazard_detcritical_size_monomial _ 4)
      (isT : 5 <= 7).
- exact: lazard_detcritical_size_monomial _ 6.
Qed.

Ltac lazard_detcritical_split_sum :=
  match goal with
  | |- size (?p + ?q) <= ?n =>
      apply: lazard_detcritical_size_add_degree;
      [ lazard_detcritical_split_sum | lazard_detcritical_split_sum ]
  | |- size (?p - ?q) <= ?n =>
      apply: lazard_detcritical_size_sub_degree;
      [ lazard_detcritical_split_sum | lazard_detcritical_split_sum ]
  | _ => idtac
  end.

Lemma lazard_detcritical_polynomial_value_size
    (a0 a1 a2 a3 b0 b1 b2 : {poly F})
    (ha0 : size a0 <= 3) (ha1 : size a1 <= 2)
    (ha2 : size a2 <= 1) (ha3 : size a3 <= 1)
    (hb0 : size b0 <= 5) (hb1 : size b1 <= 3)
    (hb2 : size b2 <= 3) :
  size (D.lazard_detcritical_polynomial_value
    a0 a1 a2 a3 b0 b1 b2) <= 13.
Proof.
have ha0_2 : size (a0 ^+ 2) <= 5 :=
  lazard_detcritical_size_exp_degree ha0.
have ha1_2 : size (a1 ^+ 2) <= 3 :=
  lazard_detcritical_size_exp_degree ha1.
have ha2_2 : size (a2 ^+ 2) <= 1 :=
  lazard_detcritical_size_exp_degree ha2.
have ha3_2 : size (a3 ^+ 2) <= 1 :=
  lazard_detcritical_size_exp_degree ha3.
have hb0_2 : size (b0 ^+ 2) <= 9 :=
  lazard_detcritical_size_exp_degree hb0.
have hb0_3 : size (b0 ^+ 3) <= 13 :=
  lazard_detcritical_size_exp_degree hb0.
have hb1_2 : size (b1 ^+ 2) <= 5 :=
  lazard_detcritical_size_exp_degree hb1.
have hb1_3 : size (b1 ^+ 3) <= 7 :=
  lazard_detcritical_size_exp_degree hb1.
have hb2_2 : size (b2 ^+ 2) <= 5 :=
  lazard_detcritical_size_exp_degree hb2.
have hb2_3 : size (b2 ^+ 3) <= 7 :=
  lazard_detcritical_size_exp_degree hb2.
have ht1raw : size (a0 ^+ 2 * b2 ^+ 3) <= 11 :=
  lazard_detcritical_size_mul_degree ha0_2 hb2_3.
have ht1 : size (a0 ^+ 2 * b2 ^+ 3) <= 13 :=
  leq_trans ht1raw (isT : 11 <= 13).
have ht2raw : size (a0 * a1 * b1 * b2 ^+ 2) <= 10 :=
  lazard_detcritical_size_mul4_degree ha0 ha1 hb1 hb2_2.
have ht2 : size (a0 * a1 * b1 * b2 ^+ 2) <= 13 :=
  leq_trans ht2raw (isT : 10 <= 13).
have ht3raw : size (a0 * a2 * b0 * b2 ^+ 2) <= 11 :=
  lazard_detcritical_size_mul4_degree ha0 ha2 hb0 hb2_2.
have ht3 : size (2%:R *: (a0 * a2 * b0 * b2 ^+ 2)) <= 13.
  apply: leq_trans
    (lazard_detcritical_size_scale_degree (a := 2%:R) ht3raw) _.
  exact: (isT : 11 <= 13).
have ht4raw : size (a0 * a2 * b1 ^+ 2 * b2) <= 9 :=
  lazard_detcritical_size_mul4_degree ha0 ha2 hb1_2 hb2.
have ht4 : size (a0 * a2 * b1 ^+ 2 * b2) <= 13 :=
  leq_trans ht4raw (isT : 9 <= 13).
have ht5raw : size (a0 * a3 * b0 * b1 * b2) <= 11 :=
  lazard_detcritical_size_mul5_degree ha0 ha3 hb0 hb1 hb2.
have ht5 : size (3%:R *: (a0 * a3 * b0 * b1 * b2)) <= 13.
  apply: leq_trans
    (lazard_detcritical_size_scale_degree (a := 3%:R) ht5raw) _.
  exact: (isT : 11 <= 13).
have ht6raw : size (a0 * a3 * b1 ^+ 3) <= 9 :=
  lazard_detcritical_size_mul3_degree ha0 ha3 hb1_3.
have ht6 : size (a0 * a3 * b1 ^+ 3) <= 13 :=
  leq_trans ht6raw (isT : 9 <= 13).
have ht7raw : size (a1 ^+ 2 * b0 * b2 ^+ 2) <= 11 :=
  lazard_detcritical_size_mul3_degree ha1_2 hb0 hb2_2.
have ht7 : size (a1 ^+ 2 * b0 * b2 ^+ 2) <= 13 :=
  leq_trans ht7raw (isT : 11 <= 13).
have ht8raw : size (a1 * a2 * b0 * b1 * b2) <= 10 :=
  lazard_detcritical_size_mul5_degree ha1 ha2 hb0 hb1 hb2.
have ht8 : size (a1 * a2 * b0 * b1 * b2) <= 13 :=
  leq_trans ht8raw (isT : 10 <= 13).
have ht9raw : size (a1 * a3 * b0 ^+ 2 * b2) <= 12 :=
  lazard_detcritical_size_mul4_degree ha1 ha3 hb0_2 hb2.
have ht9 : size (2%:R *: (a1 * a3 * b0 ^+ 2 * b2)) <= 13.
  exact: lazard_detcritical_size_scale_degree ht9raw.
have ht10raw : size (a1 * a3 * b0 * b1 ^+ 2) <= 10 :=
  lazard_detcritical_size_mul4_degree ha1 ha3 hb0 hb1_2.
have ht10 : size (a1 * a3 * b0 * b1 ^+ 2) <= 13 :=
  leq_trans ht10raw (isT : 10 <= 13).
have ht11raw : size (a2 ^+ 2 * b0 ^+ 2 * b2) <= 11 :=
  lazard_detcritical_size_mul3_degree ha2_2 hb0_2 hb2.
have ht11 : size (a2 ^+ 2 * b0 ^+ 2 * b2) <= 13 :=
  leq_trans ht11raw (isT : 11 <= 13).
have ht12raw : size (a2 * a3 * b0 ^+ 2 * b1) <= 11 :=
  lazard_detcritical_size_mul4_degree ha2 ha3 hb0_2 hb1.
have ht12 : size (a2 * a3 * b0 ^+ 2 * b1) <= 13 :=
  leq_trans ht12raw (isT : 11 <= 13).
have ht13 : size (a3 ^+ 2 * b0 ^+ 3) <= 13 :=
  lazard_detcritical_size_mul_degree ha3_2 hb0_3.
rewrite /D.lazard_detcritical_polynomial_value.
lazard_detcritical_split_sum; assumption.
Qed.

Theorem lazard_detcritical_V_polynomial_size c :
  size (D.lazard_detcritical_V_polynomial c) <= 13.
Proof.
rewrite /D.lazard_detcritical_V_polynomial.
exact: lazard_detcritical_polynomial_value_size
  (lazard_detcritical_PA0_size c) (lazard_detcritical_PA1_size c)
  (lazard_detcritical_PA2_size c) (lazard_detcritical_PA3_size c)
  (lazard_detcritical_PB0_size c) (lazard_detcritical_PB1_size c)
  (lazard_detcritical_PB2_size c).
Qed.

Theorem lazard_detcritical_target_polynomial_size c :
  size (D.lazard_detcritical_target_polynomial c) <= 13.
Proof.
rewrite /D.lazard_detcritical_target_polynomial size_polyN.
apply: lazard_detcritical_size_scale_degree.
exact: lazard_detcritical_size_exp_degree
  (lazard_detcritical_N_polynomial_size c).
Qed.

Theorem lazard_detcritical_polynomial_value_horner
    (a0 a1 a2 a3 b0 b1 b2 : {poly F}) x :
  (D.lazard_detcritical_polynomial_value
      a0 a1 a2 a3 b0 b1 b2).[x] =
    CQ.lazard_cubic_quadratic_resultant_value
      a0.[x] a1.[x] a2.[x] a3.[x] b0.[x] b1.[x] b2.[x].
Proof.
by rewrite /D.lazard_detcritical_polynomial_value
  /CQ.lazard_cubic_quadratic_resultant_value
  !hornerD !hornerB !hornerM !hornerZ !hornerN !horner_exp.
Qed.

Theorem lazard_detcritical_N_polynomial_horner c :
  (D.lazard_detcritical_N_polynomial c).[RP.lazard_root_s c] =
    DM.lazard_det_certificate_compact_numerator c.
Proof.
by rewrite /D.lazard_detcritical_N_polynomial
  /DM.lazard_det_certificate_compact_numerator !hornerE.
Qed.

End PolynomialFacts.

Print Assumptions lazard_detcritical_V_polynomial_size.
Print Assumptions lazard_detcritical_polynomial_value_horner.
Print Assumptions lazard_detcritical_N_polynomial_horner.

End PolynomialFormulasLazardQuinticDeterminantCriticalPolynomial.
