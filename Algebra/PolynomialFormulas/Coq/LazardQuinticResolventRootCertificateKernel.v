From Stdlib Require Import Ring Lia.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data
  LazardQuinticRootProjections
  LazardQuinticCayleyTranslation
  LazardQuinticResolventPolynomial
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root-level correctness of Lazard's displayed monic sextic.

    The proof below does not assume Lazard's Vieta identity as a supplied
    certificate.  It expands the depressed elementary coefficients and the
    ten-term definition of [i4], eliminates the fifth root with the depressed
    sum relation, and lets the kernel-checked reflective ring tactic verify
    the resulting four-variable polynomial identity. *)
Module PolynomialFormulasLazardQuinticResolventRootCertificateKernel.

Import GRing.Theory.
Module F20 := PolynomialFormulasQuinticF20Data.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module CT := PolynomialFormulasLazardQuinticCayleyTranslation.
Module LR := PolynomialFormulasLazardQuinticResolventPolynomial.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section RootCertificate.

Variable F : fieldType.

Add Ring lazard_resolvent_root_certificate_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

(** Only the numerals occurring in the displayed discriminant and core are
    added here.  Keeping these decompositions local avoids making this root
    certificate depend on the independent determinant-certificate chain. *)
Lemma lazard_resolvent_root_9_natrE : (9%:R : F) = 8%:R + 1.
Proof. exact: (@natrD F 8 1). Qed.
Lemma lazard_resolvent_root_13_natrE : (13%:R : F) = 12%:R + 1.
Proof. exact: (@natrD F 12 1). Qed.
Lemma lazard_resolvent_root_24_natrE : (24%:R : F) = 12%:R * 2%:R.
Proof. exact: (@natrM F 12 2). Qed.
Lemma lazard_resolvent_root_27_natrE : (27%:R : F) = 3%:R * 9%:R.
Proof. exact: (@natrM F 3 9). Qed.
Lemma lazard_resolvent_root_64_natrE : (64%:R : F) = 8%:R * 8%:R.
Proof. exact: (@natrM F 8 8). Qed.
Lemma lazard_resolvent_root_72_natrE : (72%:R : F) = 6%:R * 12%:R.
Proof. exact: (@natrM F 6 12). Qed.
Lemma lazard_resolvent_root_108_natrE : (108%:R : F) = 9%:R * 12%:R.
Proof. exact: (@natrM F 9 12). Qed.
Lemma lazard_resolvent_root_128_natrE : (128%:R : F) = 8%:R * 16%:R.
Proof. exact: (@natrM F 8 16). Qed.
Lemma lazard_resolvent_root_144_natrE : (144%:R : F) = 12%:R * 12%:R.
Proof. exact: (@natrM F 12 12). Qed.
Lemma lazard_resolvent_root_200_natrE : (200%:R : F) = 20%:R * 10%:R.
Proof. exact: (@natrM F 20 10). Qed.
Lemma lazard_resolvent_root_256_natrE : (256%:R : F) = 16%:R * 16%:R.
Proof. exact: (@natrM F 16 16). Qed.
Lemma lazard_resolvent_root_560_natrE : (560%:R : F) = 4%:R * 140%:R.
Proof. exact: (@natrM F 4 140). Qed.
Lemma lazard_resolvent_root_630_natrE :
  (630%:R : F) = 3%:R * 21%:R * 10%:R.
Proof. rewrite -(@natrM F 3 21) -(@natrM F 63 10). reflexivity. Qed.
Lemma lazard_resolvent_root_825_natrE : (825%:R : F) = 33%:R * 25%:R.
Proof. exact: (@natrM F 33 25). Qed.
Lemma lazard_resolvent_root_900_natrE : (900%:R : F) = 9%:R * 100%:R.
Proof. exact: (@natrM F 9 100). Qed.
Lemma lazard_resolvent_root_1600_natrE : (1600%:R : F) = 16%:R * 100%:R.
Proof. exact: (@natrM F 16 100). Qed.
Lemma lazard_resolvent_root_2000_natrE : (2000%:R : F) = 20%:R * 100%:R.
Proof. exact: (@natrM F 20 100). Qed.
Lemma lazard_resolvent_root_2250_natrE :
  (2250%:R : F) = 18%:R * 125%:R.
Proof. exact: (@natrM F 18 125). Qed.
Lemma lazard_resolvent_root_3125_natrE :
  (3125%:R : F) = 25%:R * 125%:R.
Proof. exact: (@natrM F 25 125). Qed.
Lemma lazard_resolvent_root_3750_natrE :
  (3750%:R : F) = 30%:R * 125%:R.
Proof. exact: (@natrM F 30 125). Qed.

Create HintDb lazard_resolvent_root_numerals_db.
#[local] Hint Rewrite
  lazard_resolvent_root_3750_natrE
  lazard_resolvent_root_3125_natrE
  lazard_resolvent_root_2250_natrE
  lazard_resolvent_root_2000_natrE
  lazard_resolvent_root_1600_natrE
  lazard_resolvent_root_900_natrE
  lazard_resolvent_root_825_natrE
  lazard_resolvent_root_630_natrE
  lazard_resolvent_root_560_natrE
  lazard_resolvent_root_256_natrE
  lazard_resolvent_root_200_natrE
  lazard_resolvent_root_144_natrE
  lazard_resolvent_root_128_natrE
  lazard_resolvent_root_108_natrE
  lazard_resolvent_root_72_natrE
  lazard_resolvent_root_64_natrE
  lazard_resolvent_root_27_natrE
  lazard_resolvent_root_24_natrE
  lazard_resolvent_root_13_natrE
  lazard_resolvent_root_9_natrE
  NR.lazard_numerator_hundred_forty_natrE
  NR.lazard_numerator_hundred_twenty_five_natrE
  NR.lazard_numerator_hundred_five_natrE
  NR.lazard_numerator_hundred_natrE
  NR.lazard_numerator_seventy_six_natrE
  NR.lazard_numerator_seventy_natrE
  NR.lazard_numerator_sixty_eight_natrE
  NR.lazard_numerator_fifty_eight_natrE
  NR.lazard_numerator_fifty_natrE
  NR.lazard_numerator_forty_natrE
  NR.lazard_numerator_thirty_five_natrE
  NR.lazard_numerator_thirty_four_natrE
  NR.lazard_numerator_thirty_three_natrE
  NR.lazard_numerator_thirty_natrE
  NR.lazard_numerator_twenty_eight_natrE
  NR.lazard_numerator_twenty_six_natrE
  NR.lazard_numerator_twenty_five_natrE
  NR.lazard_numerator_twenty_three_natrE
  NR.lazard_numerator_twenty_two_natrE
  NR.lazard_numerator_twenty_one_natrE
  NR.lazard_numerator_twenty_natrE
  NR.lazard_numerator_eighteen_natrE
  NR.lazard_numerator_seventeen_natrE
  NR.lazard_numerator_sixteen_natrE
  NR.lazard_numerator_fifteen_natrE
  NR.lazard_numerator_fourteen_natrE
  NR.lazard_numerator_twelve_natrE
  NR.lazard_numerator_eleven_natrE
  NR.lazard_numerator_ten_natrE
  NR.lazard_numerator_eight_natrE
  NR.lazard_numerator_seven_natrE
  NR.lazard_numerator_six_natrE
  NR.lazard_numerator_five_natrE
  NR.lazard_numerator_four_natrE
  NR.lazard_numerator_three_natrE
  NR.lazard_numerator_two_natrE
  : lazard_resolvent_root_numerals_db.

Create HintDb lazard_resolvent_root_exponents_db.
#[local] Hint Rewrite
  NR.lazard_numerator_expr5
  NR.lazard_numerator_expr4
  NR.lazard_numerator_expr3
  NR.lazard_numerator_expr2
  NR.lazard_numerator_expr1
  : lazard_resolvent_root_exponents_db.

Create HintDb lazard_resolvent_root_operations_db.
#[local] Hint Rewrite
  NR.lazard_numerator_ring_addE
  NR.lazard_numerator_ring_mulE
  NR.lazard_numerator_ring_subE
  NR.lazard_numerator_ring_oppE
  NR.lazard_numerator_ring_zeroE
  NR.lazard_numerator_ring_oneE
  : lazard_resolvent_root_operations_db.

Create HintDb lazard_resolvent_root_orbit_exponents_db.
#[local] Hint Rewrite
  NR.lazard_numerator_expr2
  NR.lazard_numerator_expr1
  : lazard_resolvent_root_orbit_exponents_db.

(** Indexed rewriting avoids rescanning this large identity after every
    individual numeral occurrence. *)
Ltac lazard_resolvent_root_prepare :=
  autorewrite with lazard_resolvent_root_numerals_db;
  autorewrite with lazard_resolvent_root_exponents_db;
  autorewrite with lazard_resolvent_root_operations_db.

Ltac lazard_resolvent_root_large_numerals_prepare :=
  repeat first
    [ rewrite lazard_resolvent_root_3750_natrE
    | rewrite lazard_resolvent_root_3125_natrE
    | rewrite lazard_resolvent_root_2250_natrE
    | rewrite lazard_resolvent_root_2000_natrE
    | rewrite lazard_resolvent_root_1600_natrE
    | rewrite lazard_resolvent_root_900_natrE
    | rewrite lazard_resolvent_root_825_natrE
    | rewrite lazard_resolvent_root_630_natrE
    | rewrite lazard_resolvent_root_560_natrE
    | rewrite lazard_resolvent_root_256_natrE
    | rewrite lazard_resolvent_root_200_natrE
    | rewrite lazard_resolvent_root_144_natrE
    | rewrite lazard_resolvent_root_128_natrE
    | rewrite lazard_resolvent_root_108_natrE
    | rewrite lazard_resolvent_root_72_natrE
    | rewrite lazard_resolvent_root_64_natrE
    | rewrite lazard_resolvent_root_27_natrE
    | rewrite lazard_resolvent_root_24_natrE
    | rewrite lazard_resolvent_root_13_natrE
    | rewrite lazard_resolvent_root_9_natrE ];
  repeat first
    [ rewrite NR.lazard_numerator_hundred_forty_natrE
    | rewrite NR.lazard_numerator_hundred_twenty_five_natrE
    | rewrite NR.lazard_numerator_hundred_five_natrE
    | rewrite NR.lazard_numerator_hundred_natrE
    | rewrite NR.lazard_numerator_seventy_six_natrE
    | rewrite NR.lazard_numerator_seventy_natrE
    | rewrite NR.lazard_numerator_sixty_eight_natrE
    | rewrite NR.lazard_numerator_fifty_eight_natrE
    | rewrite NR.lazard_numerator_fifty_natrE
    | rewrite NR.lazard_numerator_forty_natrE
    | rewrite NR.lazard_numerator_thirty_five_natrE
    | rewrite NR.lazard_numerator_thirty_four_natrE
    | rewrite NR.lazard_numerator_thirty_three_natrE
    | rewrite NR.lazard_numerator_thirty_natrE
    | rewrite NR.lazard_numerator_twenty_eight_natrE
    | rewrite NR.lazard_numerator_twenty_six_natrE
    | rewrite NR.lazard_numerator_twenty_five_natrE
    | rewrite NR.lazard_numerator_twenty_three_natrE
    | rewrite NR.lazard_numerator_twenty_two_natrE
    | rewrite NR.lazard_numerator_twenty_one_natrE
    | rewrite NR.lazard_numerator_twenty_natrE
    | rewrite NR.lazard_numerator_eighteen_natrE
    | rewrite NR.lazard_numerator_seventeen_natrE
    | rewrite NR.lazard_numerator_sixteen_natrE
    | rewrite NR.lazard_numerator_fifteen_natrE
    | rewrite NR.lazard_numerator_fourteen_natrE
    | rewrite NR.lazard_numerator_twelve_natrE
    | rewrite NR.lazard_numerator_eleven_natrE
    | rewrite NR.lazard_numerator_ten_natrE
    | rewrite NR.lazard_numerator_eight_natrE
    | rewrite NR.lazard_numerator_seven_natrE
    | rewrite NR.lazard_numerator_six_natrE
    | rewrite NR.lazard_numerator_five_natrE
    | rewrite NR.lazard_numerator_four_natrE
    | rewrite NR.lazard_numerator_three_natrE
    | rewrite NR.lazard_numerator_two_natrE ].

Ltac finish_lazard_resolvent_root_certificate_ring :=
  lazard_resolvent_root_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The ordered Vandermonde product, using the orientation [xi - xj] for
    [i < j]. *)
Definition lazard_root_discriminant_delta (roots : 5.-tuple F) : F :=
  (tnth roots F20.o0 - tnth roots F20.o1) *
  (tnth roots F20.o0 - tnth roots F20.o2) *
  (tnth roots F20.o0 - tnth roots F20.o3) *
  (tnth roots F20.o0 - tnth roots F20.o4) *
  (tnth roots F20.o1 - tnth roots F20.o2) *
  (tnth roots F20.o1 - tnth roots F20.o3) *
  (tnth roots F20.o1 - tnth roots F20.o4) *
  (tnth roots F20.o2 - tnth roots F20.o3) *
  (tnth roots F20.o2 - tnth roots F20.o4) *
  (tnth roots F20.o3 - tnth roots F20.o4).

Ltac finish_lazard_resolvent_root_factor_ring :=
  lazard_resolvent_root_prepare;
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The displayed coefficient discriminant is the square of the ordered
    root-difference product. *)
Lemma lazard_resolvent_discriminant_root_factor
    (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  LR.lazard_resolvent_discriminant
      (RP.lazard_depressed_of_roots roots) =
    lazard_root_discriminant_delta roots ^+ 2.
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
pose c := RP.lazard_depressed_of_roots roots.
change
  (LR.lazard_resolvent_discriminant c =
    lazard_root_discriminant_delta roots ^+ 2).
rewrite /LR.lazard_resolvent_discriminant.
lazard_resolvent_root_large_numerals_prepare.
rewrite /c /RP.lazard_depressed_of_roots /=
  /lazard_root_discriminant_delta
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5 hx4 /=.
finish_lazard_resolvent_root_factor_ring.
Qed.

(** The fraction-free cubic core factors as Cayley's alternating quadratic
    factor times the ordered Vandermonde product. *)
Lemma lazard_resolvent_core_root_factor
    (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  LR.lazard_resolvent_core
      (RP.lazard_depressed_of_roots roots)
      (RP.lazard_root_i4 (RP.lazard_root_invariants roots)) =
    (CT.lazard_root_cayley_V roots - CT.lazard_root_cayley_W roots) *
      lazard_root_discriminant_delta roots.
Proof.
have hx4 := RP.lazard_root_sum_zero_last hsum.
pose c := RP.lazard_depressed_of_roots roots.
pose z := RP.lazard_root_i4 (RP.lazard_root_invariants roots).
change
  (LR.lazard_resolvent_core c z =
    (CT.lazard_root_cayley_V roots - CT.lazard_root_cayley_W roots) *
      lazard_root_discriminant_delta roots).
rewrite /LR.lazard_resolvent_core
  /LR.lazard_resolvent_core_linear
  /LR.lazard_resolvent_core_constant.
lazard_resolvent_root_large_numerals_prepare.
rewrite /c /z /RP.lazard_depressed_of_roots /=
  /RP.lazard_root_invariants /= /RP.lazard_root_orbit_formula
  /CT.lazard_root_cayley_V /CT.lazard_root_cayley_W
  /lazard_root_discriminant_delta
  /RP.lazard_root_esymm2 /RP.lazard_root_esymm3
  /RP.lazard_root_esymm4 /RP.lazard_root_esymm5 hx4 /=.
finish_lazard_resolvent_root_factor_ring.
Qed.
End RootCertificate.

Print Assumptions lazard_resolvent_discriminant_root_factor.
Print Assumptions lazard_resolvent_core_root_factor.

End PolynomialFormulasLazardQuinticResolventRootCertificateKernel.
