From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootInvariantRelations
  LazardQuinticRootInvariantRelationFifthData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Numeral and linear-assembly support shared by the six independent
    fifth-relation coefficient certificates. *)
Module PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.

Import GRing.Theory.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module D := PolynomialFormulasLazardQuinticRootInvariantRelationFifthData.
Local Open Scope ring_scope.

Section Support.

Variable F : fieldType.

Add Ring lazard_fifth_support_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Lemma lazard_fifth_13_natrE : (13%:R : F) = 12%:R + 1.
Proof. exact: (@natrD F 12 1). Qed.
Lemma lazard_fifth_24_natrE : (24%:R : F) = 12%:R + 12%:R.
Proof. exact: (@natrD F 12 12). Qed.
Lemma lazard_fifth_43_natrE : (43%:R : F) = 42%:R + 1.
Proof. exact: (@natrD F 42 1). Qed.
Lemma lazard_fifth_49_natrE : (49%:R : F) = 7%:R * 7%:R.
Proof. exact: (@natrM F 7 7). Qed.
Lemma lazard_fifth_64_natrE : (64%:R : F) = 8%:R * 8%:R.
Proof. exact: (@natrM F 8 8). Qed.
Lemma lazard_fifth_81_natrE : (81%:R : F) = 9%:R * 9%:R.
Proof. exact: (@natrM F 9 9). Qed.
Lemma lazard_fifth_83_natrE : (83%:R : F) = 76%:R + 7%:R.
Proof. exact: (@natrD F 76 7). Qed.
Lemma lazard_fifth_90_natrE : (90%:R : F) = 9%:R * 10%:R.
Proof. exact: (@natrM F 9 10). Qed.
Lemma lazard_fifth_95_natrE : (95%:R : F) = 76%:R + 19%:R.
Proof. exact: (@natrD F 76 19). Qed.
Lemma lazard_fifth_110_natrE : (110%:R : F) = 11%:R * 10%:R.
Proof. exact: (@natrM F 11 10). Qed.
Lemma lazard_fifth_120_natrE : (120%:R : F) = 12%:R * 10%:R.
Proof. exact: (@natrM F 12 10). Qed.
Lemma lazard_fifth_124_natrE : (124%:R : F) = 100%:R + 24%:R.
Proof. exact: (@natrD F 100 24). Qed.
Lemma lazard_fifth_144_natrE : (144%:R : F) = 12%:R * 12%:R.
Proof. exact: (@natrM F 12 12). Qed.
Lemma lazard_fifth_147_natrE : (147%:R : F) = 140%:R + 7%:R.
Proof. exact: (@natrD F 140 7). Qed.
Lemma lazard_fifth_152_natrE : (152%:R : F) = 76%:R * 2%:R.
Proof. exact: (@natrM F 76 2). Qed.
Lemma lazard_fifth_156_natrE : (156%:R : F) = 140%:R + 16%:R.
Proof. exact: (@natrD F 140 16). Qed.
Lemma lazard_fifth_168_natrE : (168%:R : F) = 14%:R * 12%:R.
Proof. exact: (@natrM F 14 12). Qed.
Lemma lazard_fifth_176_natrE : (176%:R : F) = 16%:R * 11%:R.
Proof. exact: (@natrM F 16 11). Qed.
Lemma lazard_fifth_180_natrE : (180%:R : F) = 18%:R * 10%:R.
Proof. exact: (@natrM F 18 10). Qed.
Lemma lazard_fifth_181_natrE : (181%:R : F) = 180%:R + 1.
Proof. exact: (@natrD F 180 1). Qed.
Lemma lazard_fifth_198_natrE : (198%:R : F) = 18%:R * 11%:R.
Proof. exact: (@natrM F 18 11). Qed.
Lemma lazard_fifth_200_natrE : (200%:R : F) = 20%:R * 10%:R.
Proof. exact: (@natrM F 20 10). Qed.
Lemma lazard_fifth_212_natrE : (212%:R : F) = 200%:R + 12%:R.
Proof. exact: (@natrD F 200 12). Qed.
Lemma lazard_fifth_215_natrE : (215%:R : F) = 200%:R + 15%:R.
Proof. exact: (@natrD F 200 15). Qed.
Lemma lazard_fifth_220_natrE : (220%:R : F) = 22%:R * 10%:R.
Proof. exact: (@natrM F 22 10). Qed.
Lemma lazard_fifth_240_natrE : (240%:R : F) = 12%:R * 20%:R.
Proof. exact: (@natrM F 12 20). Qed.
Lemma lazard_fifth_286_natrE : (286%:R : F) = 26%:R * 11%:R.
Proof. exact: (@natrM F 26 11). Qed.
Lemma lazard_fifth_290_natrE : (290%:R : F) = 29%:R * 10%:R.
Proof. exact: (@natrM F 29 10). Qed.
Lemma lazard_fifth_300_natrE : (300%:R : F) = 30%:R * 10%:R.
Proof. exact: (@natrM F 30 10). Qed.
Lemma lazard_fifth_325_natrE : (325%:R : F) = 300%:R + 25%:R.
Proof. exact: (@natrD F 300 25). Qed.
Lemma lazard_fifth_350_natrE : (350%:R : F) = 35%:R * 10%:R.
Proof. exact: (@natrM F 35 10). Qed.
Lemma lazard_fifth_351_natrE : (351%:R : F) = 350%:R + 1.
Proof. exact: (@natrD F 350 1). Qed.
Lemma lazard_fifth_355_natrE : (355%:R : F) = 350%:R + 5%:R.
Proof. exact: (@natrD F 350 5). Qed.
Lemma lazard_fifth_364_natrE : (364%:R : F) = 28%:R * 13%:R.
Proof. exact: (@natrM F 28 13). Qed.
Lemma lazard_fifth_420_natrE : (420%:R : F) = 42%:R * 10%:R.
Proof. exact: (@natrM F 42 10). Qed.
Lemma lazard_fifth_432_natrE : (432%:R : F) = 12%:R * 36%:R.
Proof. exact: (@natrM F 12 36). Qed.
Lemma lazard_fifth_490_natrE : (490%:R : F) = 49%:R * 10%:R.
Proof. exact: (@natrM F 49 10). Qed.
Lemma lazard_fifth_491_natrE : (491%:R : F) = 490%:R + 1.
Proof. exact: (@natrD F 490 1). Qed.
Lemma lazard_fifth_500_natrE : (500%:R : F) = 50%:R * 10%:R.
Proof. exact: (@natrM F 50 10). Qed.
Lemma lazard_fifth_512_natrE : (512%:R : F) = 64%:R * 8%:R.
Proof. exact: (@natrM F 64 8). Qed.
Lemma lazard_fifth_530_natrE : (530%:R : F) = 500%:R + 30%:R.
Proof. exact: (@natrD F 500 30). Qed.
Lemma lazard_fifth_600_natrE : (600%:R : F) = 30%:R * 20%:R.
Proof. exact: (@natrM F 30 20). Qed.
Lemma lazard_fifth_612_natrE : (612%:R : F) = 600%:R + 12%:R.
Proof. exact: (@natrD F 600 12). Qed.
Lemma lazard_fifth_620_natrE : (620%:R : F) = 600%:R + 20%:R.
Proof. exact: (@natrD F 600 20). Qed.
Lemma lazard_fifth_625_natrE : (625%:R : F) = 25%:R * 25%:R.
Proof. exact: (@natrM F 25 25). Qed.
Lemma lazard_fifth_700_natrE : (700%:R : F) = 70%:R * 10%:R.
Proof. exact: (@natrM F 70 10). Qed.
Lemma lazard_fifth_752_natrE : (752%:R : F) = 700%:R + 52%:R.
Proof. exact: (@natrD F 700 52). Qed.
Lemma lazard_fifth_800_natrE : (800%:R : F) = 8%:R * 100%:R.
Proof. exact: (@natrM F 8 100). Qed.
Lemma lazard_fifth_810_natrE : (810%:R : F) = 81%:R * 10%:R.
Proof. exact: (@natrM F 81 10). Qed.
Lemma lazard_fifth_858_natrE : (858%:R : F) = 800%:R + 58%:R.
Proof. exact: (@natrD F 800 58). Qed.
Lemma lazard_fifth_900_natrE : (900%:R : F) = 30%:R * 30%:R.
Proof. exact: (@natrM F 30 30). Qed.
Lemma lazard_fifth_960_natrE : (960%:R : F) = 12%:R * 80%:R.
Proof. exact: (@natrM F 12 80). Qed.
Lemma lazard_fifth_1000_natrE : (1000%:R : F) = 10%:R * 100%:R.
Proof. exact: (@natrM F 10 100). Qed.
Lemma lazard_fifth_1088_natrE : (1088%:R : F) = 68%:R * 16%:R.
Proof. exact: (@natrM F 68 16). Qed.
Lemma lazard_fifth_1375_natrE : (1375%:R : F) = 125%:R * 11%:R.
Proof. exact: (@natrM F 125 11). Qed.
Lemma lazard_fifth_1500_natrE : (1500%:R : F) = 15%:R * 100%:R.
Proof. exact: (@natrM F 15 100). Qed.
Lemma lazard_fifth_1560_natrE : (1560%:R : F) = 156%:R * 10%:R.
Proof. exact: (@natrM F 156 10). Qed.
Lemma lazard_fifth_1728_natrE : (1728%:R : F) = 144%:R * 12%:R.
Proof. exact: (@natrM F 144 12). Qed.
Lemma lazard_fifth_1800_natrE : (1800%:R : F) = 18%:R * 100%:R.
Proof. exact: (@natrM F 18 100). Qed.
Lemma lazard_fifth_1825_natrE : (1825%:R : F) = 1800%:R + 25%:R.
Proof. exact: (@natrD F 1800 25). Qed.
Lemma lazard_fifth_2375_natrE : (2375%:R : F) = 125%:R * 19%:R.
Proof. exact: (@natrM F 125 19). Qed.
Lemma lazard_fifth_2600_natrE : (2600%:R : F) = 26%:R * 100%:R.
Proof. exact: (@natrM F 26 100). Qed.
Lemma lazard_fifth_2640_natrE : (2640%:R : F) = 2600%:R + 40%:R.
Proof. exact: (@natrD F 2600 40). Qed.
Lemma lazard_fifth_3000_natrE : (3000%:R : F) = 30%:R * 100%:R.
Proof. exact: (@natrM F 30 100). Qed.
Lemma lazard_fifth_3005_natrE : (3005%:R : F) = 3000%:R + 5%:R.
Proof. exact: (@natrD F 3000 5). Qed.
Lemma lazard_fifth_3125_natrE : (3125%:R : F) = 125%:R * 25%:R.
Proof. exact: (@natrM F 125 25). Qed.
Lemma lazard_fifth_3175_natrE : (3175%:R : F) = 3125%:R + 50%:R.
Proof. exact: (@natrD F 3125 50). Qed.
Lemma lazard_fifth_4000_natrE : (4000%:R : F) = 40%:R * 100%:R.
Proof. exact: (@natrM F 40 100). Qed.
Lemma lazard_fifth_4095_natrE : (4095%:R : F) = 4000%:R + 95%:R.
Proof. exact: (@natrD F 4000 95). Qed.
Lemma lazard_fifth_4120_natrE : (4120%:R : F) = 4000%:R + 120%:R.
Proof. exact: (@natrD F 4000 120). Qed.
Lemma lazard_fifth_6000_natrE : (6000%:R : F) = 60%:R * 100%:R.
Proof. exact: (@natrM F 60 100). Qed.
Lemma lazard_fifth_6240_natrE : (6240%:R : F) = 6000%:R + 240%:R.
Proof. exact: (@natrD F 6000 240). Qed.
Lemma lazard_fifth_6250_natrE : (6250%:R : F) = 25%:R * 250%:R.
Proof. exact: (@natrM F 25 250). Qed.
Lemma lazard_fifth_10000_natrE : (10000%:R : F) = 100%:R * 100%:R.
Proof. exact: (@natrM F 100 100). Qed.
Lemma lazard_fifth_10700_natrE : (10700%:R : F) = 10000%:R + 700%:R.
Proof. exact: (@natrD F 10000 700). Qed.
Lemma lazard_fifth_15625_natrE : (15625%:R : F) = 125%:R * 125%:R.
Proof. exact: (@natrM F 125 125). Qed.
Lemma lazard_fifth_15875_natrE : (15875%:R : F) = 15625%:R + 250%:R.
Proof. exact: (@natrD F 15625 250). Qed.

Lemma lazard_fifth_expr6 (x : F) :
  x ^+ 6 = x * x * x * x * x * x.
Proof. by rewrite exprSr NR.lazard_numerator_expr5. Qed.

(** Purely linear assembly.  All expensive polynomial content is confined
    to the six equalities supplied by the coefficient shards. *)
Lemma lazard_fifth_linear_residual
    (i4 i5 i6 i7 i8
     a8 a7 a6 a5 a4 a0
     s8 s7 s6 s5 s4 s0
     p58 p57 p56 p55 p54 p50
     p68 p67 p66 p65 p64 p60
     p78 p77 p76 p75 p74 p70
     p88 p87 p86 p85 p84 p80
     n8 n7 n6 n5 n4 n0 : F)
    (hn8 : n8 = a8 * p88 + 2%:R * a7 * p78 + a6 * p68 +
      2%:R * a5 * p58 + 2%:R * a4 * s8)
    (hn7 : n7 = a8 * p87 + 2%:R * a7 * p77 + a6 * p67 +
      2%:R * a5 * p57 + 2%:R * a4 * s7)
    (hn6 : n6 = a8 * p86 + 2%:R * a7 * p76 + a6 * p66 +
      2%:R * a5 * p56 + 2%:R * a4 * s6)
    (hn5 : n5 = a8 * p85 + 2%:R * a7 * p75 + a6 * p65 +
      2%:R * a5 * p55 + 2%:R * a4 * s5)
    (hn4 : n4 = 2%:R * a0 + a8 * p84 + 2%:R * a7 * p74 +
      a6 * p64 + 2%:R * a5 * p54 + 2%:R * a4 * s4)
    (hn0 : n0 = a8 * p80 + 2%:R * a7 * p70 + a6 * p60 +
      2%:R * a5 * p50 + 2%:R * a4 * s0) :
  2%:R * i4 ^+ 5 -
      (n8 * i8 + n7 * i7 + n6 * i6 + n5 * i5 + n4 * i4 + n0) =
    2%:R * i4 *
      (i4 ^+ 4 - (a8 * i8 + a7 * i7 + a6 * i6 + a5 * i5 +
        a4 * i4 + a0)) +
    a8 * (2%:R * (i4 * i8) -
      (p88 * i8 + p87 * i7 + p86 * i6 + p85 * i5 + p84 * i4 + p80)) +
    2%:R * a7 * (i4 * i7 -
      (p78 * i8 + p77 * i7 + p76 * i6 + p75 * i5 + p74 * i4 + p70)) +
    a6 * (2%:R * (i4 * i6) -
      (p68 * i8 + p67 * i7 + p66 * i6 + p65 * i5 + p64 * i4 + p60)) +
    2%:R * a5 * (i4 * i5 -
      (p58 * i8 + p57 * i7 + p56 * i6 + p55 * i5 + p54 * i4 + p50)) +
    2%:R * a4 * (i4 ^+ 2 -
      (s8 * i8 + s7 * i7 + s6 * i6 + s5 * i5 + s4 * i4 + s0)).
Proof.
rewrite hn8 hn7 hn6 hn5 hn4 hn0.
lazard_numerator_prepare.
match goal with
| |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
end.
ring.
Qed.

End Support.

End PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.

(** Numeral preparation stays outside the module so clients can invoke it
    without depending on tactic-registration export behavior. *)
Ltac lazard_fifth_coefficient_prepare :=
  repeat first
    [ rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_15875_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_15625_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_10700_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_10000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_6250_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_6240_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_6000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_4120_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_4095_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_4000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_3175_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_3125_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_3005_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_3000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_2640_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_2600_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_2375_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1825_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1800_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1728_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1560_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1500_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1375_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1088_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_1000_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_960_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_900_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_858_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_810_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_800_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_752_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_700_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_625_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_620_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_612_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_600_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_530_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_512_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_500_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_491_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_490_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_432_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_420_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_364_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_355_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_351_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_350_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_325_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_300_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_290_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_286_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_240_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_220_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_215_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_212_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_200_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_198_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_181_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_180_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_176_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_168_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_156_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_152_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_147_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_144_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_124_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_120_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_110_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_95_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_90_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_83_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_81_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_64_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_49_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_43_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_24_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_13_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_five_hundred_fifty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_four_hundred_four_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_two_hundred_fifty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_two_hundred_twenty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_hundred_fifty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_hundred_thirty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_eighty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_seventy_nine_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_sixty_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_fifty_four_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_fifty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_forty_five_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_forty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_forty_one_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_thirty_six_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_thirty_two_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_twenty_nine_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_twenty_seven_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_nineteen_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelations.lazard_invariant_relations_nine_natrE
    | rewrite PolynomialFormulasLazardQuinticRootInvariantRelationFifthSupport.lazard_fifth_expr6 ];
  lazard_numerator_prepare.
