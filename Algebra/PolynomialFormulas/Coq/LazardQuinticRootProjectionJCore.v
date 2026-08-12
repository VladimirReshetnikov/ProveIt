From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticFourier
  LazardQuinticProjection LazardQuinticRootProjections
  LazardQuinticRootProjectionJKCommon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The isolated degree-ten root coefficient certificate for Lazard's third
    standard projection. *)
Module PolynomialFormulasLazardQuinticRootProjectionJCore.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootRadicals.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticRootProjectionJKCommon.
Local Open Scope ring_scope.

Section RootProjectionJ.

Variable F : fieldType.

Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma lazard_root_projection_J_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_J_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_J_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_J_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_root_projection_J_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_root_projection_J_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_root_projection_J_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring lazard_root_projection_J_ring : lazard_root_projection_J_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_root_projection_nine_natrE :
  (9%:R : F) = 7%:R + 2%:R.
Proof. exact: (@natrD F 7 2). Qed.
Lemma lazard_root_projection_eleven_natrE :
  (11%:R : F) = 10%:R + 1.
Proof. exact: (@natrD F 10 1). Qed.
Lemma lazard_root_projection_sixty_natrE :
  (60%:R : F) = 3%:R * 20%:R.
Proof. exact: (@natrM F 3 20). Qed.
Lemma lazard_root_projection_ninety_six_natrE :
  (96%:R : F) = 24%:R * 4%:R.
Proof. exact: (@natrM F 24 4). Qed.
Lemma lazard_root_projection_hundred_twenty_eight_natrE :
  (128%:R : F) = 16%:R * 8%:R.
Proof. exact: (@natrM F 16 8). Qed.
Lemma lazard_root_projection_hundred_forty_five_natrE :
  (145%:R : F) = 125%:R + 20%:R.
Proof. exact: (@natrD F 125 20). Qed.
Lemma lazard_root_projection_three_hundred_eight_natrE :
  (308%:R : F) = 300%:R + 8%:R.
Proof. exact: (@natrD F 300 8). Qed.
Lemma lazard_root_projection_five_hundred_twenty_five_natrE :
  (525%:R : F) = 5%:R * (100%:R + 5%:R).
Proof.
rewrite -(@natrD F 100 5).
exact: (@natrM F 5 105).
Qed.
Lemma lazard_root_projection_one_thousand_natrE :
  (1000%:R : F) = 10%:R * 100%:R.
Proof. exact: (@natrM F 10 100). Qed.

Ltac finish_lazard_root_projection_J_ring :=
  repeat first
    [ rewrite lazard_root_projection_one_thousand_natrE
    | rewrite lazard_root_projection_five_hundred_twenty_five_natrE
    | rewrite lazard_root_projection_three_hundred_eight_natrE
    | rewrite lazard_root_projection_hundred_forty_five_natrE
    | rewrite lazard_root_projection_hundred_twenty_eight_natrE
    | rewrite lazard_root_projection_ninety_six_natrE
    | rewrite lazard_root_projection_sixty_natrE
    | rewrite lazard_root_projection_eleven_natrE
    | rewrite lazard_root_projection_nine_natrE
    | rewrite lazard_root_projection_three_hundred_natrE
    | rewrite lazard_root_projection_hundred_twenty_five_natrE
    | rewrite lazard_root_projection_hundred_natrE
    | rewrite lazard_root_projection_fifty_natrE
    | rewrite lazard_root_projection_twenty_five_natrE
    | rewrite lazard_root_projection_twenty_four_natrE
    | rewrite lazard_root_projection_twenty_natrE
    | rewrite lazard_root_projection_sixteen_natrE
    | rewrite lazard_root_projection_ten_natrE
    | rewrite lazard_root_projection_eight_natrE
    | rewrite lazard_root_projection_seven_natrE
    | rewrite lazard_root_projection_three_natrE
    | rewrite lazard_root_projection_five_natrE
    | rewrite lazard_root_projection_four_natrE
    | rewrite lazard_root_projection_two_natrE
    | rewrite lazard_root_projection_expr5
    | rewrite lazard_root_projection_expr8
    | rewrite lazard_root_projection_expr7
    | rewrite lazard_root_projection_expr6
    | rewrite lazard_root_projection_expr4
    | rewrite lazard_root_projection_expr3
    | rewrite lazard_root_projection_expr2
    | rewrite expr1
    | rewrite lazard_root_projection_J_ring_addE
    | rewrite lazard_root_projection_J_ring_mulE
    | rewrite lazard_root_projection_J_ring_subE
    | rewrite lazard_root_projection_J_ring_oppE
    | rewrite lazard_root_projection_J_ring_zeroE
    | rewrite lazard_root_projection_J_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** Root-only coefficient identity underlying the J projection. *)
Lemma lazard_root_J_component_core roots
    (hsum : lazard_root_esymm1 roots = 0) :
  2%:R * lazard_root_J_component roots =
    5%:R * lazard_root_invariant_J
      (@lazard_depressed_of_roots F roots) (@lazard_root_invariants F roots).
Proof.
have hx4 := lazard_root_sum_zero_last hsum.
rewrite /lazard_root_J_component /lazard_cyclic_fourier_seed.
pose a := lazard_cyclic_fourier_P1 roots.
pose square := lazard_cyclic_mul a a.
pose cube := lazard_cyclic_mul square a.
have hpower : lazard_cyclic_fifth_power
    (lazard_cyclic_fourier_P1 roots) = lazard_cyclic_mul square cube.
  reflexivity.
rewrite hpower.
have ha0 : lazard_cyclic0 a = tnth roots o0 by reflexivity.
have ha1 : lazard_cyclic1 a = tnth roots o1 by reflexivity.
have ha2 : lazard_cyclic2 a = tnth roots o2 by reflexivity.
have ha3 : lazard_cyclic3 a = tnth roots o3 by reflexivity.
have ha4 : lazard_cyclic4 a = tnth roots o4 by reflexivity.
have hs0 := lazard_cyclic_mul0E a a.
have hs1 := lazard_cyclic_mul1E a a.
have hs2 := lazard_cyclic_mul2E a a.
have hs3 := lazard_cyclic_mul3E a a.
have hs4 := lazard_cyclic_mul4E a a.
fold square in hs0, hs1, hs2, hs3, hs4.
have hc0 := lazard_cyclic_mul0E square a.
have hc1 := lazard_cyclic_mul1E square a.
have hc2 := lazard_cyclic_mul2E square a.
have hc3 := lazard_cyclic_mul3E square a.
have hc4 := lazard_cyclic_mul4E square a.
fold cube in hc0, hc1, hc2, hc3, hc4.
clearbody cube; clearbody square; clearbody a.
rewrite lazard_cyclic_mul1E lazard_cyclic_mul2E
  lazard_cyclic_mul3E lazard_cyclic_mul4E
  hc0 hc1 hc2 hc3 hc4 hs0 hs1 hs2 hs3 hs4
  ha0 ha1 ha2 ha3 ha4.
rewrite /lazard_root_T_prime /lazard_root_U_prime
  /lazard_root_invariant_J /lazard_depressed_of_roots /=
  /lazard_root_invariants /= /lazard_root_orbit_formula
  /lazard_root_esymm2 /lazard_root_esymm3 /lazard_root_esymm4
  /lazard_root_esymm5 hx4.
finish_lazard_root_projection_J_ring.
Qed.


End RootProjectionJ.

End PolynomialFormulasLazardQuinticRootProjectionJCore.
