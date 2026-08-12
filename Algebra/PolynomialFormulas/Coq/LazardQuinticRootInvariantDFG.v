From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Coefficient-side definitions and root reductions for Lazard's displayed
    invariants D, F, and G.  The corresponding E reduction already lives in
    [LazardQuinticRootInvariantE].

    These are deliberately stated as polynomial identities on a depressed
    ordered root tuple.  Consequently the rationality/descent proof for the
    root expressions and the claim that the displayed coefficient formulas
    denote those expressions are separate, independently auditable facts. *)
Module PolynomialFormulasLazardQuinticRootInvariantDFG.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.

Local Open Scope ring_scope.

Section RootInvariantDFG.

Variable F : fieldType.

(** Additional numeral decompositions used only by D/F/G.  The shared
    numerator-ring preparation handles the smaller common coefficients;
    these equations reduce every remaining printed coefficient to those
    common ones before reflective normalization. *)
Lemma lazard_dfg_19_natrE : (19%:R : F) = 18%:R + 1.
Proof. exact: (@natrD F 18 1). Qed.
Lemma lazard_dfg_24_natrE : (24%:R : F) = 12%:R + 12%:R.
Proof. exact: (@natrD F 12 12). Qed.
Lemma lazard_dfg_27_natrE : (27%:R : F) = 12%:R + 15%:R.
Proof. exact: (@natrD F 12 15). Qed.
Lemma lazard_dfg_32_natrE : (32%:R : F) = 16%:R + 16%:R.
Proof. exact: (@natrD F 16 16). Qed.
Lemma lazard_dfg_41_natrE : (41%:R : F) = 40%:R + 1.
Proof. exact: (@natrD F 40 1). Qed.
Lemma lazard_dfg_42_natrE : (42%:R : F) = 40%:R + 2%:R.
Proof. exact: (@natrD F 40 2). Qed.
Lemma lazard_dfg_46_natrE : (46%:R : F) = 24%:R + 22%:R.
Proof. exact: (@natrD F 24 22). Qed.
Lemma lazard_dfg_48_natrE : (48%:R : F) = 24%:R + 24%:R.
Proof. exact: (@natrD F 24 24). Qed.
Lemma lazard_dfg_52_natrE : (52%:R : F) = 26%:R + 26%:R.
Proof. exact: (@natrD F 26 26). Qed.
Lemma lazard_dfg_56_natrE : (56%:R : F) = 28%:R + 28%:R.
Proof. exact: (@natrD F 28 28). Qed.
Lemma lazard_dfg_62_natrE : (62%:R : F) = 42%:R + 20%:R.
Proof. exact: (@natrD F 42 20). Qed.
Lemma lazard_dfg_65_natrE : (65%:R : F) = 50%:R + 15%:R.
Proof. exact: (@natrD F 50 15). Qed.
Lemma lazard_dfg_66_natrE : (66%:R : F) = 33%:R + 33%:R.
Proof. exact: (@natrD F 33 33). Qed.
Lemma lazard_dfg_73_natrE : (73%:R : F) = 70%:R + 3%:R.
Proof. exact: (@natrD F 70 3). Qed.
Lemma lazard_dfg_80_natrE : (80%:R : F) = 40%:R + 40%:R.
Proof. exact: (@natrD F 40 40). Qed.
Lemma lazard_dfg_85_natrE : (85%:R : F) = 70%:R + 15%:R.
Proof. exact: (@natrD F 70 15). Qed.
Lemma lazard_dfg_88_natrE : (88%:R : F) = 48%:R + 40%:R.
Proof. exact: (@natrD F 48 40). Qed.
Lemma lazard_dfg_95_natrE : (95%:R : F) = 80%:R + 15%:R.
Proof. exact: (@natrD F 80 15). Qed.
Lemma lazard_dfg_96_natrE : (96%:R : F) = 48%:R + 48%:R.
Proof. exact: (@natrD F 48 48). Qed.
Lemma lazard_dfg_120_natrE : (120%:R : F) = 100%:R + 20%:R.
Proof. exact: (@natrD F 100 20). Qed.
Lemma lazard_dfg_142_natrE : (142%:R : F) = 140%:R + 2%:R.
Proof. exact: (@natrD F 140 2). Qed.
Lemma lazard_dfg_156_natrE : (156%:R : F) = 140%:R + 16%:R.
Proof. exact: (@natrD F 140 16). Qed.
Lemma lazard_dfg_158_natrE : (158%:R : F) = 140%:R + 18%:R.
Proof. exact: (@natrD F 140 18). Qed.
Lemma lazard_dfg_159_natrE : (159%:R : F) = 140%:R + 19%:R.
Proof. exact: (@natrD F 140 19). Qed.
Lemma lazard_dfg_160_natrE : (160%:R : F) = 140%:R + 20%:R.
Proof. exact: (@natrD F 140 20). Qed.
Lemma lazard_dfg_175_natrE : (175%:R : F) = 140%:R + 35%:R.
Proof. exact: (@natrD F 140 35). Qed.
Lemma lazard_dfg_182_natrE : (182%:R : F) = 140%:R + 42%:R.
Proof. exact: (@natrD F 140 42). Qed.
Lemma lazard_dfg_184_natrE : (184%:R : F) = 160%:R + 24%:R.
Proof. exact: (@natrD F 160 24). Qed.
Lemma lazard_dfg_190_natrE : (190%:R : F) = 175%:R + 15%:R.
Proof. exact: (@natrD F 175 15). Qed.
Lemma lazard_dfg_195_natrE : (195%:R : F) = 175%:R + 20%:R.
Proof. exact: (@natrD F 175 20). Qed.
Lemma lazard_dfg_200_natrE : (200%:R : F) = 100%:R + 100%:R.
Proof. exact: (@natrD F 100 100). Qed.
Lemma lazard_dfg_213_natrE : (213%:R : F) = 195%:R + 18%:R.
Proof. exact: (@natrD F 195 18). Qed.
Lemma lazard_dfg_232_natrE : (232%:R : F) = 200%:R + 32%:R.
Proof. exact: (@natrD F 200 32). Qed.
Lemma lazard_dfg_246_natrE : (246%:R : F) = 200%:R + 46%:R.
Proof. exact: (@natrD F 200 46). Qed.
Lemma lazard_dfg_250_natrE : (250%:R : F) = 200%:R + 50%:R.
Proof. exact: (@natrD F 200 50). Qed.
Lemma lazard_dfg_270_natrE : (270%:R : F) = 250%:R + 20%:R.
Proof. exact: (@natrD F 250 20). Qed.
Lemma lazard_dfg_275_natrE : (275%:R : F) = 250%:R + 25%:R.
Proof. exact: (@natrD F 250 25). Qed.
Lemma lazard_dfg_280_natrE : (280%:R : F) = 140%:R + 140%:R.
Proof. exact: (@natrD F 140 140). Qed.
Lemma lazard_dfg_298_natrE : (298%:R : F) = 280%:R + 18%:R.
Proof. exact: (@natrD F 280 18). Qed.
Lemma lazard_dfg_300_natrE : (300%:R : F) = 250%:R + 50%:R.
Proof. exact: (@natrD F 250 50). Qed.
Lemma lazard_dfg_332_natrE : (332%:R : F) = 300%:R + 32%:R.
Proof. exact: (@natrD F 300 32). Qed.
Lemma lazard_dfg_350_natrE : (350%:R : F) = 300%:R + 50%:R.
Proof. exact: (@natrD F 300 50). Qed.
Lemma lazard_dfg_358_natrE : (358%:R : F) = 300%:R + 58%:R.
Proof. exact: (@natrD F 300 58). Qed.
Lemma lazard_dfg_366_natrE : (366%:R : F) = 300%:R + 66%:R.
Proof. exact: (@natrD F 300 66). Qed.
Lemma lazard_dfg_400_natrE : (400%:R : F) = 200%:R + 200%:R.
Proof. exact: (@natrD F 200 200). Qed.
Lemma lazard_dfg_402_natrE : (402%:R : F) = 400%:R + 2%:R.
Proof. exact: (@natrD F 400 2). Qed.
Lemma lazard_dfg_418_natrE : (418%:R : F) = 400%:R + 18%:R.
Proof. exact: (@natrD F 400 18). Qed.
Lemma lazard_dfg_419_natrE : (419%:R : F) = 400%:R + 19%:R.
Proof. exact: (@natrD F 400 19). Qed.
Lemma lazard_dfg_440_natrE : (440%:R : F) = 400%:R + 40%:R.
Proof. exact: (@natrD F 400 40). Qed.
Lemma lazard_dfg_448_natrE : (448%:R : F) = 400%:R + 48%:R.
Proof. exact: (@natrD F 400 48). Qed.
Lemma lazard_dfg_450_natrE : (450%:R : F) = 400%:R + 50%:R.
Proof. exact: (@natrD F 400 50). Qed.
Lemma lazard_dfg_480_natrE : (480%:R : F) = 400%:R + 80%:R.
Proof. exact: (@natrD F 400 80). Qed.
Lemma lazard_dfg_492_natrE : (492%:R : F) = 440%:R + 52%:R.
Proof. exact: (@natrD F 440 52). Qed.
Lemma lazard_dfg_500_natrE : (500%:R : F) = 250%:R + 250%:R.
Proof. exact: (@natrD F 250 250). Qed.
Lemma lazard_dfg_515_natrE : (515%:R : F) = 500%:R + 15%:R.
Proof. exact: (@natrD F 500 15). Qed.
Lemma lazard_dfg_520_natrE : (520%:R : F) = 480%:R + 40%:R.
Proof. exact: (@natrD F 480 40). Qed.
Lemma lazard_dfg_524_natrE : (524%:R : F) = 500%:R + 24%:R.
Proof. exact: (@natrD F 500 24). Qed.
Lemma lazard_dfg_550_natrE : (550%:R : F) = 500%:R + 50%:R.
Proof. exact: (@natrD F 500 50). Qed.
Lemma lazard_dfg_650_natrE : (650%:R : F) = 550%:R + 100%:R.
Proof. exact: (@natrD F 550 100). Qed.
Lemma lazard_dfg_700_natrE : (700%:R : F) = 350%:R + 350%:R.
Proof. exact: (@natrD F 350 350). Qed.
Lemma lazard_dfg_748_natrE : (748%:R : F) = 700%:R + 48%:R.
Proof. exact: (@natrD F 700 48). Qed.
Lemma lazard_dfg_825_natrE : (825%:R : F) = 650%:R + 175%:R.
Proof. exact: (@natrD F 650 175). Qed.
Lemma lazard_dfg_875_natrE : (875%:R : F) = 700%:R + 175%:R.
Proof. exact: (@natrD F 700 175). Qed.
Lemma lazard_dfg_896_natrE : (896%:R : F) = 448%:R + 448%:R.
Proof. exact: (@natrD F 448 448). Qed.
Lemma lazard_dfg_940_natrE : (940%:R : F) = 500%:R + 440%:R.
Proof. exact: (@natrD F 500 440). Qed.
Lemma lazard_dfg_1000_natrE : (1000%:R : F) = 500%:R + 500%:R.
Proof. exact: (@natrD F 500 500). Qed.
Lemma lazard_dfg_1040_natrE : (1040%:R : F) = 1000%:R + 40%:R.
Proof. exact: (@natrD F 1000 40). Qed.
Lemma lazard_dfg_1100_natrE : (1100%:R : F) = 1000%:R + 100%:R.
Proof. exact: (@natrD F 1000 100). Qed.
Lemma lazard_dfg_1250_natrE : (1250%:R : F) = 1000%:R + 250%:R.
Proof. exact: (@natrD F 1000 250). Qed.
Lemma lazard_dfg_1400_natrE : (1400%:R : F) = 700%:R + 700%:R.
Proof. exact: (@natrD F 700 700). Qed.
Lemma lazard_dfg_1462_natrE : (1462%:R : F) = 1400%:R + 62%:R.
Proof. exact: (@natrD F 1400 62). Qed.
Lemma lazard_dfg_1500_natrE : (1500%:R : F) = 1000%:R + 500%:R.
Proof. exact: (@natrD F 1000 500). Qed.
Lemma lazard_dfg_1590_natrE : (1590%:R : F) = 1400%:R + 190%:R.
Proof. exact: (@natrD F 1400 190). Qed.
Lemma lazard_dfg_1875_natrE : (1875%:R : F) = 1000%:R + 875%:R.
Proof. exact: (@natrD F 1000 875). Qed.
Lemma lazard_dfg_1925_natrE : (1925%:R : F) = 1875%:R + 50%:R.
Proof. exact: (@natrD F 1875 50). Qed.
Lemma lazard_dfg_2000_natrE : (2000%:R : F) = 1000%:R + 1000%:R.
Proof. exact: (@natrD F 1000 1000). Qed.
Lemma lazard_dfg_2095_natrE : (2095%:R : F) = 2000%:R + 95%:R.
Proof. exact: (@natrD F 2000 95). Qed.
Lemma lazard_dfg_2100_natrE : (2100%:R : F) = 2000%:R + 100%:R.
Proof. exact: (@natrD F 2000 100). Qed.
Lemma lazard_dfg_2825_natrE : (2825%:R : F) = 2000%:R + 825%:R.
Proof. exact: (@natrD F 2000 825). Qed.
Lemma lazard_dfg_2900_natrE : (2900%:R : F) = 1500%:R + 1400%:R.
Proof. exact: (@natrD F 1500 1400). Qed.
Lemma lazard_dfg_3000_natrE : (3000%:R : F) = 1500%:R + 1500%:R.
Proof. exact: (@natrD F 1500 1500). Qed.
Lemma lazard_dfg_4000_natrE : (4000%:R : F) = 2000%:R + 2000%:R.
Proof. exact: (@natrD F 2000 2000). Qed.
Lemma lazard_dfg_4875_natrE : (4875%:R : F) = 4000%:R + 875%:R.
Proof. exact: (@natrD F 4000 875). Qed.

(** Lazard's displayed invariant D. *)
Definition lazard_invariant_D
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  40%:R * RP.lazard_root_p c * RP.lazard_root_i8 i -
  120%:R * RP.lazard_root_q c * RP.lazard_root_i7 i +
  (- 24%:R * RP.lazard_root_p c ^+ 2 +
      100%:R * RP.lazard_root_r c) * RP.lazard_root_i6 i +
  (88%:R * RP.lazard_root_p c * RP.lazard_root_q c -
      300%:R * RP.lazard_root_s c) * RP.lazard_root_i5 i +
  (- 24%:R * RP.lazard_root_p c ^+ 3 +
      100%:R * RP.lazard_root_p c * RP.lazard_root_r c +
      24%:R * RP.lazard_root_q c ^+ 2) * RP.lazard_root_i4 i -
  80%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c +
  40%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
  480%:R * RP.lazard_root_p c * RP.lazard_root_q c *
    RP.lazard_root_s c +
  160%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 +
  332%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c +
  125%:R * RP.lazard_root_s c ^+ 2.

(** Lazard's displayed invariant F. *)
Definition lazard_invariant_F
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  (- 65%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c +
      875%:R * RP.lazard_root_p c * RP.lazard_root_s c -
      550%:R * RP.lazard_root_q c * RP.lazard_root_r c) *
    RP.lazard_root_i8 i +
  (- 58%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
      41%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 -
      275%:R * RP.lazard_root_q c * RP.lazard_root_s c +
      440%:R * RP.lazard_root_r c ^+ 2) * RP.lazard_root_i7 i +
  (85%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c -
      520%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
      298%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c +
      366%:R * RP.lazard_root_q c ^+ 3 +
      2100%:R * RP.lazard_root_r c * RP.lazard_root_s c) *
    RP.lazard_root_i6 i +
  (4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c -
      73%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 +
      2095%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_s c -
      56%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 -
      748%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c -
      4875%:R * RP.lazard_root_s c ^+ 2) * RP.lazard_root_i5 i +
  (85%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c -
      418%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c -
      440%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_r c +
      419%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 +
      1590%:R * RP.lazard_root_p c * RP.lazard_root_r c *
        RP.lazard_root_s c -
      1040%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c +
      524%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2) *
    RP.lazard_root_i4 i -
  12%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_s c +
  158%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
    RP.lazard_root_r c -
  85%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 3 -
  1462%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c *
    RP.lazard_root_s c -
  159%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_s c +
  142%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
    RP.lazard_root_r c ^+ 2 +
  896%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
    RP.lazard_root_r c +
  175%:R * RP.lazard_root_p c * RP.lazard_root_q c *
    RP.lazard_root_s c ^+ 2 +
  2900%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 *
    RP.lazard_root_s c -
  402%:R * RP.lazard_root_q c ^+ 5 -
  1925%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c *
    RP.lazard_root_s c -
  448%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 3 -
  1875%:R * RP.lazard_root_s c ^+ 3.

(** Lazard's displayed invariant G. *)
Definition lazard_invariant_G
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  (- 35%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c -
      250%:R * RP.lazard_root_p c * RP.lazard_root_s c -
      200%:R * RP.lazard_root_q c * RP.lazard_root_r c) *
    RP.lazard_root_i8 i +
  (- 22%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_r c +
      19%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 2 +
      650%:R * RP.lazard_root_q c * RP.lazard_root_s c -
      40%:R * RP.lazard_root_r c ^+ 2) * RP.lazard_root_i7 i +
  (15%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c +
      195%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c +
      68%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c -
      6%:R * RP.lazard_root_q c ^+ 3 -
      1100%:R * RP.lazard_root_r c * RP.lazard_root_s c) *
    RP.lazard_root_i6 i +
  (- 4%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c -
      27%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 -
      270%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_s c +
      96%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 -
      182%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c +
      3000%:R * RP.lazard_root_s c ^+ 2) * RP.lazard_root_i5 i +
  (15%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c +
      213%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_s c +
      50%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
        RP.lazard_root_r c +
      RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 -
      940%:R * RP.lazard_root_p c * RP.lazard_root_r c *
        RP.lazard_root_s c +
      515%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_s c -
      184%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 2) *
    RP.lazard_root_i4 i +
  12%:R * RP.lazard_root_p c ^+ 5 * RP.lazard_root_s c +
  42%:R * RP.lazard_root_p c ^+ 4 * RP.lazard_root_q c *
    RP.lazard_root_r c -
  15%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_q c ^+ 3 +
  492%:R * RP.lazard_root_p c ^+ 3 * RP.lazard_root_r c *
    RP.lazard_root_s c -
  156%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c ^+ 2 *
    RP.lazard_root_s c +
  358%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_q c *
    RP.lazard_root_r c ^+ 2 -
  246%:R * RP.lazard_root_p c * RP.lazard_root_q c ^+ 3 *
    RP.lazard_root_r c +
  2825%:R * RP.lazard_root_p c * RP.lazard_root_q c *
    RP.lazard_root_s c ^+ 2 -
  1400%:R * RP.lazard_root_p c * RP.lazard_root_r c ^+ 2 *
    RP.lazard_root_s c +
  42%:R * RP.lazard_root_q c ^+ 5 +
  550%:R * RP.lazard_root_q c ^+ 2 * RP.lazard_root_r c *
    RP.lazard_root_s c -
  232%:R * RP.lazard_root_q c * RP.lazard_root_r c ^+ 3 -
  1250%:R * RP.lazard_root_s c ^+ 3.

Add Ring lazard_root_invariant_DFG_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_invariant_DFG_ring :=
  repeat first
    [ rewrite lazard_dfg_4875_natrE
    | rewrite lazard_dfg_4000_natrE
    | rewrite lazard_dfg_3000_natrE
    | rewrite lazard_dfg_2900_natrE
    | rewrite lazard_dfg_2825_natrE
    | rewrite lazard_dfg_2100_natrE
    | rewrite lazard_dfg_2095_natrE
    | rewrite lazard_dfg_2000_natrE
    | rewrite lazard_dfg_1925_natrE
    | rewrite lazard_dfg_1875_natrE
    | rewrite lazard_dfg_1590_natrE
    | rewrite lazard_dfg_1500_natrE
    | rewrite lazard_dfg_1462_natrE
    | rewrite lazard_dfg_1400_natrE
    | rewrite lazard_dfg_1250_natrE
    | rewrite lazard_dfg_1100_natrE
    | rewrite lazard_dfg_1040_natrE
    | rewrite lazard_dfg_1000_natrE
    | rewrite lazard_dfg_940_natrE
    | rewrite lazard_dfg_896_natrE
    | rewrite lazard_dfg_875_natrE
    | rewrite lazard_dfg_825_natrE
    | rewrite lazard_dfg_748_natrE
    | rewrite lazard_dfg_700_natrE
    | rewrite lazard_dfg_650_natrE
    | rewrite lazard_dfg_550_natrE
    | rewrite lazard_dfg_524_natrE
    | rewrite lazard_dfg_520_natrE
    | rewrite lazard_dfg_515_natrE
    | rewrite lazard_dfg_500_natrE
    | rewrite lazard_dfg_492_natrE
    | rewrite lazard_dfg_480_natrE
    | rewrite lazard_dfg_450_natrE
    | rewrite lazard_dfg_448_natrE
    | rewrite lazard_dfg_440_natrE
    | rewrite lazard_dfg_419_natrE
    | rewrite lazard_dfg_418_natrE
    | rewrite lazard_dfg_402_natrE
    | rewrite lazard_dfg_400_natrE
    | rewrite lazard_dfg_366_natrE
    | rewrite lazard_dfg_358_natrE
    | rewrite lazard_dfg_350_natrE
    | rewrite lazard_dfg_332_natrE
    | rewrite lazard_dfg_300_natrE
    | rewrite lazard_dfg_298_natrE
    | rewrite lazard_dfg_280_natrE
    | rewrite lazard_dfg_275_natrE
    | rewrite lazard_dfg_270_natrE
    | rewrite lazard_dfg_250_natrE
    | rewrite lazard_dfg_246_natrE
    | rewrite lazard_dfg_232_natrE
    | rewrite lazard_dfg_213_natrE
    | rewrite lazard_dfg_200_natrE
    | rewrite lazard_dfg_195_natrE
    | rewrite lazard_dfg_190_natrE
    | rewrite lazard_dfg_184_natrE
    | rewrite lazard_dfg_182_natrE
    | rewrite lazard_dfg_175_natrE
    | rewrite lazard_dfg_160_natrE
    | rewrite lazard_dfg_159_natrE
    | rewrite lazard_dfg_158_natrE
    | rewrite lazard_dfg_156_natrE
    | rewrite lazard_dfg_142_natrE
    | rewrite lazard_dfg_120_natrE
    | rewrite lazard_dfg_96_natrE
    | rewrite lazard_dfg_95_natrE
    | rewrite lazard_dfg_88_natrE
    | rewrite lazard_dfg_85_natrE
    | rewrite lazard_dfg_80_natrE
    | rewrite lazard_dfg_73_natrE
    | rewrite lazard_dfg_66_natrE
    | rewrite lazard_dfg_65_natrE
    | rewrite lazard_dfg_62_natrE
    | rewrite lazard_dfg_56_natrE
    | rewrite lazard_dfg_52_natrE
    | rewrite lazard_dfg_48_natrE
    | rewrite lazard_dfg_46_natrE
    | rewrite lazard_dfg_42_natrE
    | rewrite lazard_dfg_41_natrE
    | rewrite lazard_dfg_32_natrE
    | rewrite lazard_dfg_27_natrE
    | rewrite lazard_dfg_24_natrE
    | rewrite lazard_dfg_19_natrE ];
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The displayed D polynomial is the square of the cyclic epsilon
    product. *)
Theorem lazard_root_invariant_D_eq
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_invariant_D (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots) =
    Q.lazard_root_D roots.
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
rewrite /lazard_invariant_D /RP.lazard_depressed_of_roots
  /RP.lazard_root_invariants /RP.lazard_root_orbit_formula
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5
  /Q.lazard_root_D /RR.lazard_epsilon_product hx4 /=.
finish_lazard_root_invariant_DFG_ring.
Qed.

(** The displayed F polynomial is the first cyclic epsilon-weighted
    quadratic form. *)
Theorem lazard_root_invariant_F_eq
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_invariant_F (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots) =
    Q.lazard_root_F roots.
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
rewrite /lazard_invariant_F /RP.lazard_depressed_of_roots
  /RP.lazard_root_invariants /RP.lazard_root_orbit_formula
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5
  /Q.lazard_root_F /RR.lazard_epsilon_product
  /RR.lazard_root_T_prime /RR.lazard_root_U_prime hx4 /=.
finish_lazard_root_invariant_DFG_ring.
Qed.

(** The displayed G polynomial is the second cyclic epsilon-weighted
    quadratic form. *)
Theorem lazard_root_invariant_G_eq
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_invariant_G (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_invariants roots) =
    Q.lazard_root_G roots.
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
rewrite /lazard_invariant_G /RP.lazard_depressed_of_roots
  /RP.lazard_root_invariants /RP.lazard_root_orbit_formula
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5
  /Q.lazard_root_G /RR.lazard_epsilon_product
  /RR.lazard_root_T_prime /RR.lazard_root_U_prime hx4 /=.
finish_lazard_root_invariant_DFG_ring.
Qed.

(** Aggregate coefficient/root bridge used when instantiating the radical
    certificate with the displayed formulas rather than their shorter root
    normal forms. *)
Theorem lazard_root_invariant_DFG_eq
    (roots : 5.-tuple F) (hsum : RP.lazard_root_esymm1 roots = 0) :
  [/
    lazard_invariant_D (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_D roots,
    lazard_invariant_F (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_F roots
  & lazard_invariant_G (RP.lazard_depressed_of_roots roots)
        (RP.lazard_root_invariants roots) = Q.lazard_root_G roots].
Proof.
split.
- exact: lazard_root_invariant_D_eq hsum.
- exact: lazard_root_invariant_F_eq hsum.
- exact: lazard_root_invariant_G_eq hsum.
Qed.

End RootInvariantDFG.

End PolynomialFormulasLazardQuinticRootInvariantDFG.
