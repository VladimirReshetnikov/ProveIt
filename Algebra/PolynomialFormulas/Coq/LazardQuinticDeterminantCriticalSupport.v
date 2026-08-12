From Stdlib Require Import Ring Field.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticDeterminantCertificateMatrix
  LazardQuinticCriticalElimination
  LazardQuinticDeterminantCriticalData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Shared numeral and reflection support for the thirteen independent
    coefficient shards.  Each shard still registers the ring/field theories
    locally, because tactic registrations do not cross compiled modules. *)
Module PolynomialFormulasLazardQuinticDeterminantCriticalSupport.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module DM := PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.
Module CE := PolynomialFormulasLazardQuinticCriticalElimination.
Local Open Scope ring_scope.

Section Numerals.

Variable F : fieldType.

Lemma lazard_detcritical_27_natrE : (27%:R : F) = 3%:R * 9%:R.
Proof. exact: (@natrM F 3 9). Qed.
Lemma lazard_detcritical_72_natrE : (72%:R : F) = 6%:R * 12%:R.
Proof. exact: (@natrM F 6 12). Qed.
Lemma lazard_detcritical_108_natrE : (108%:R : F) = 9%:R * 12%:R.
Proof. exact: (@natrM F 9 12). Qed.
Lemma lazard_detcritical_128_natrE : (128%:R : F) = 8%:R * 16%:R.
Proof. exact: (@natrM F 8 16). Qed.
Lemma lazard_detcritical_162_natrE : (162%:R : F) = 18%:R * 9%:R.
Proof. exact: (@natrM F 18 9). Qed.
Lemma lazard_detcritical_250_natrE : (250%:R : F) = 25%:R * 10%:R.
Proof. exact: (@natrM F 25 10). Qed.
Lemma lazard_detcritical_256_natrE : (256%:R : F) = 16%:R * 16%:R.
Proof. exact: (@natrM F 16 16). Qed.
Lemma lazard_detcritical_264_natrE : (264%:R : F) = 24%:R * 11%:R.
Proof. exact: (@natrM F 24 11). Qed.
Lemma lazard_detcritical_320_natrE : (320%:R : F) = 32%:R * 10%:R.
Proof. exact: (@natrM F 32 10). Qed.
Lemma lazard_detcritical_328_natrE :
  (328%:R : F) = 32%:R * 10%:R + 8%:R.
Proof. rewrite -(@natrM F 32 10) -(@natrD F 320 8). reflexivity. Qed.
Lemma lazard_detcritical_360_natrE : (360%:R : F) = 3%:R * 120%:R.
Proof. exact: (@natrM F 3 120). Qed.
Lemma lazard_detcritical_394_natrE : (394%:R : F) = 364%:R + 30%:R.
Proof. exact: (@natrD F 364 30). Qed.
Lemma lazard_detcritical_450_natrE : (450%:R : F) = 45%:R * 10%:R.
Proof. exact: (@natrM F 45 10). Qed.
Lemma lazard_detcritical_500_natrE : (500%:R : F) = 50%:R * 10%:R.
Proof. exact: (@natrM F 50 10). Qed.
Lemma lazard_detcritical_560_natrE : (560%:R : F) = 4%:R * 140%:R.
Proof. exact: (@natrM F 4 140). Qed.
Lemma lazard_detcritical_630_natrE :
  (630%:R : F) = 3%:R * 21%:R * 10%:R.
Proof. rewrite -(@natrM F 3 21) -(@natrM F 63 10). reflexivity. Qed.
Lemma lazard_detcritical_825_natrE : (825%:R : F) = 33%:R * 25%:R.
Proof. exact: (@natrM F 33 25). Qed.
Lemma lazard_detcritical_840_natrE : (840%:R : F) = 2%:R * 420%:R.
Proof. exact: (@natrM F 2 420). Qed.
Lemma lazard_detcritical_1140_natrE :
  (1140%:R : F) = 110%:R * 10%:R + 40%:R.
Proof. rewrite -(@natrM F 110 10) -(@natrD F 1100 40). reflexivity. Qed.
Lemma lazard_detcritical_1200_natrE : (1200%:R : F) = 12%:R * 100%:R.
Proof. exact: (@natrM F 12 100). Qed.
Lemma lazard_detcritical_1220_natrE :
  (1220%:R : F) = 12%:R * 100%:R + 20%:R.
Proof. rewrite -(@natrM F 12 100) -(@natrD F 1200 20). reflexivity. Qed.
Lemma lazard_detcritical_1600_natrE : (1600%:R : F) = 16%:R * 100%:R.
Proof. exact: (@natrM F 16 100). Qed.
Lemma lazard_detcritical_1680_natrE : (1680%:R : F) = 168%:R * 10%:R.
Proof. exact: (@natrM F 168 10). Qed.
Lemma lazard_detcritical_1827_natrE : (1827%:R : F) = 1800%:R + 27%:R.
Proof. exact: (@natrD F 1800 27). Qed.
Lemma lazard_detcritical_2000_natrE : (2000%:R : F) = 2%:R * 1000%:R.
Proof. exact: (@natrM F 2 1000). Qed.
Lemma lazard_detcritical_2124_natrE :
  (2124%:R : F) = 212%:R * 10%:R + 4%:R.
Proof. rewrite -(@natrM F 212 10) -(@natrD F 2120 4). reflexivity. Qed.
Lemma lazard_detcritical_2250_natrE :
  (2250%:R : F) = 9%:R * 25%:R * 10%:R.
Proof. rewrite -(@natrM F 9 25) -(@natrM F 225 10). reflexivity. Qed.
Lemma lazard_detcritical_2705_natrE :
  (2705%:R : F) = 27%:R * 100%:R + 5%:R.
Proof. rewrite -(@natrM F 27 100) -(@natrD F 2700 5). reflexivity. Qed.
Lemma lazard_detcritical_2790_natrE :
  (2790%:R : F) = 27%:R * 100%:R + 90%:R.
Proof. rewrite -(@natrM F 27 100) -(@natrD F 2700 90). reflexivity. Qed.
Lemma lazard_detcritical_3600_natrE : (3600%:R : F) = 36%:R * 100%:R.
Proof. exact: (@natrM F 36 100). Qed.
Lemma lazard_detcritical_3750_natrE :
  (3750%:R : F) = 3%:R * 125%:R * 10%:R.
Proof. rewrite -(@natrM F 3 125) -(@natrM F 375 10). reflexivity. Qed.
Lemma lazard_detcritical_4000_natrE : (4000%:R : F) = 40%:R * 100%:R.
Proof. exact: (@natrM F 40 100). Qed.
Lemma lazard_detcritical_4200_natrE : (4200%:R : F) = 42%:R * 100%:R.
Proof. exact: (@natrM F 42 100). Qed.
Lemma lazard_detcritical_4900_natrE : (4900%:R : F) = 49%:R * 100%:R.
Proof. exact: (@natrM F 49 100). Qed.
Lemma lazard_detcritical_7800_natrE :
  (7800%:R : F) = 76%:R * 100%:R + 200%:R.
Proof. rewrite -(@natrM F 76 100) -(@natrD F 7600 200). reflexivity. Qed.
Lemma lazard_detcritical_11000_natrE : (11000%:R : F) = 11%:R * 1000%:R.
Proof. exact: (@natrM F 11 1000). Qed.
Lemma lazard_detcritical_11400_natrE :
  (11400%:R : F) = 110%:R * 100%:R + 400%:R.
Proof. rewrite -(@natrM F 110 100) -(@natrD F 11000 400). reflexivity. Qed.
Lemma lazard_detcritical_14000_natrE : (14000%:R : F) = 14%:R * 1000%:R.
Proof. exact: (@natrM F 14 1000). Qed.
Lemma lazard_detcritical_14500_natrE :
  (14500%:R : F) = 14%:R * 1000%:R + 500%:R.
Proof. rewrite -(@natrM F 14 1000) -(@natrD F 14000 500). reflexivity. Qed.
Lemma lazard_detcritical_17200_natrE :
  (17200%:R : F) = 17%:R * 1000%:R + 200%:R.
Proof. rewrite -(@natrM F 17 1000) -(@natrD F 17000 200). reflexivity. Qed.
Lemma lazard_detcritical_20000_natrE : (20000%:R : F) = 2%:R * 10000%:R.
Proof. exact: (@natrM F 2 10000). Qed.
Lemma lazard_detcritical_26760_natrE :
  (26760%:R : F) = 26%:R * 1000%:R + 76%:R * 10%:R.
Proof.
rewrite -(@natrM F 26 1000) -(@natrM F 76 10)
  -(@natrD F 26000 760).
reflexivity.
Qed.
Lemma lazard_detcritical_40000_natrE : (40000%:R : F) = 4%:R * 10000%:R.
Proof. exact: (@natrM F 4 10000). Qed.

End Numerals.

End PolynomialFormulasLazardQuinticDeterminantCriticalSupport.

Ltac lazard_detcritical_prepare :=
  repeat first
    [ rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_40000_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_26760_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_20000_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_17200_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_14500_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_14000_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_11400_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_11000_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_7800_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_4900_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_4200_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_4000_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_3750_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_3600_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_2790_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_2705_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_2250_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_2124_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_2000_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_1827_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_1680_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_1600_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_1220_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_1200_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_1140_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_840_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_825_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_630_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_560_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_500_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_450_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_394_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_360_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_328_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_320_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_264_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_256_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_250_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_162_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_128_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_108_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_72_natrE
    | rewrite PolynomialFormulasLazardQuinticDeterminantCriticalSupport.lazard_detcritical_27_natrE ];
  PolynomialFormulasLazardQuinticCriticalElimination.lazard_critical_prepare;
  PolynomialFormulasLazardQuinticDeterminantCertificateMatrix.lazard_det_prepare.

(** Expand a fixed polynomial coefficient entirely into scalar arithmetic.
    Every occurrence of [coefM] has a concrete index in a coefficient shard,
    so the finite convolution is reduced by [big_ord_recl]. *)
Ltac lazard_detcritical_expand_coefficients :=
  repeat first
    [ rewrite coefD
    | rewrite coefB
    | rewrite coefN
    | rewrite coefZ
    | rewrite coefM;
      repeat rewrite big_ord_recl;
      rewrite big_ord0 /=
    | rewrite coefXn
    | rewrite coefX
    | rewrite coefC ];
  simpl.

(** Polynomial powers must be exposed before [coefM] can turn every fixed
    coefficient into a finite convolution.  The same expansion, applied
    after the scalar data have been unfolded, also makes the high powers in
    the compact determinant numerator visible to the reflective field
    normalizer. *)
Ltac lazard_detcritical_expand_powers :=
  repeat first [ rewrite exprSr | rewrite expr1 | rewrite expr0 ].

(** Common closing step for a coefficient shard.  Each client registers the
    numerator ring and critical field locally before invoking this tactic. *)
Ltac finish_lazard_detcritical_coefficient_field :=
  lazard_detcritical_expand_powers;
  lazard_detcritical_prepare;
  repeat first
    [ rewrite PolynomialFormulasLazardQuinticCriticalElimination.lazard_critical_divE
    | rewrite PolynomialFormulasLazardQuinticCriticalElimination.lazard_critical_invE ];
  match goal with
  | |- ?lhs = ?rhs =>
      change
        (PolynomialFormulasLazardQuinticRootFourierNumeratorRing.lazard_numerator_ring_eq
          lhs rhs)
  end;
  field.
