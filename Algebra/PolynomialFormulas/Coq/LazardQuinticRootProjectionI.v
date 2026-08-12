From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticFourier LazardQuinticProjection
  LazardQuinticRootProjections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The second raw root projection is kept separate because its final
    degree-ten coefficient certificate is substantially larger than H. *)
Module PolynomialFormulasLazardQuinticRootProjectionI.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticRootProjections.
Local Open Scope ring_scope.

Section RootProjectionI.

Variable F : fieldType.

(** Local bridge from MathComp operations to the reflective [ring] tactic.
    Tactic registrations are not exported across compiled modules. *)
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

Lemma lazard_root_projection_I_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_I_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_I_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_I_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_root_projection_I_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_root_projection_I_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_root_projection_I_ring_theory :
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

Add Ring lazard_root_projection_I_ring : lazard_root_projection_I_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_lazard_root_projection_I_ring :=
  repeat first
    [ rewrite lazard_root_projection_three_hundred_natrE
    | rewrite lazard_root_projection_two_hundred_fifty_five_natrE
    | rewrite lazard_root_projection_hundred_sixty_natrE
    | rewrite lazard_root_projection_hundred_twenty_five_natrE
    | rewrite lazard_root_projection_hundred_natrE
    | rewrite lazard_root_projection_eighty_natrE
    | rewrite lazard_root_projection_seventy_natrE
    | rewrite lazard_root_projection_sixty_eight_natrE
    | rewrite lazard_root_projection_fifty_one_natrE
    | rewrite lazard_root_projection_fifty_natrE
    | rewrite lazard_root_projection_forty_six_natrE
    | rewrite lazard_root_projection_forty_natrE
    | rewrite lazard_root_projection_twenty_eight_natrE
    | rewrite lazard_root_projection_twenty_four_natrE
    | rewrite lazard_root_projection_twenty_three_natrE
    | rewrite lazard_root_projection_twenty_five_natrE
    | rewrite lazard_root_projection_twenty_natrE
    | rewrite lazard_root_projection_seventeen_natrE
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
    | rewrite lazard_root_projection_I_ring_addE
    | rewrite lazard_root_projection_I_ring_mulE
    | rewrite lazard_root_projection_I_ring_subE
    | rewrite lazard_root_projection_I_ring_oppE
    | rewrite lazard_root_projection_I_ring_zeroE
    | rewrite lazard_root_projection_I_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** Alternating orbit and the fifth-root discriminant factor for I. *)
Definition lazard_cyclic_fourier_fifth_alternating (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_add
    (lazard_cyclic_sub
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots))
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P2 roots)))
    (lazard_cyclic_sub
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P4 roots))
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P3 roots))).

Definition lazard_cyclic_discriminant : LazardCyclicFive F :=
  {| lazard_cyclic0 := 0;
     lazard_cyclic1 := 1;
     lazard_cyclic2 := - 1;
     lazard_cyclic3 := - 1;
     lazard_cyclic4 := 1 |}.

Definition lazard_cyclic_I_vector (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_scale (lazard_root_epsilon_product roots)
    (lazard_cyclic_mul lazard_cyclic_discriminant
      (lazard_cyclic_fourier_fifth_alternating roots)).

Lemma lazard_cyclic_fourier_fifth_alternating_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_fourier_fifth_alternating roots) =
    lazard_root_fourier_P1 omega roots ^+ 5 -
    lazard_root_fourier_P2 omega roots ^+ 5 +
    lazard_root_fourier_P4 omega roots ^+ 5 -
    lazard_root_fourier_P3 omega roots ^+ 5.
Proof.
rewrite /lazard_cyclic_fourier_fifth_alternating /lazard_cyclic_sub
  !lazard_cyclic_eval_add !lazard_cyclic_eval_neg
  !lazard_cyclic_eval_fifth_power //
  lazard_cyclic_fourier_P1_eval lazard_cyclic_fourier_P2_eval
  lazard_cyclic_fourier_P4_eval lazard_cyclic_fourier_P3_eval.
finish_lazard_root_projection_I_ring.
Qed.

Lemma lazard_cyclic_discriminant_eval omega :
  lazard_cyclic_eval omega lazard_cyclic_discriminant =
    lazard_root_discriminant_factor omega.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_discriminant
  /lazard_root_discriminant_factor /=.
finish_lazard_root_projection_I_ring.
Qed.

Lemma lazard_cyclic_I_vector_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_I_vector roots) =
    lazard_root_epsilon omega roots *
      (lazard_root_fourier_P1 omega roots ^+ 5 -
       lazard_root_fourier_P2 omega roots ^+ 5 +
       lazard_root_fourier_P4 omega roots ^+ 5 -
       lazard_root_fourier_P3 omega roots ^+ 5).
Proof.
rewrite /lazard_cyclic_I_vector lazard_cyclic_eval_scale
  lazard_cyclic_eval_mul // lazard_cyclic_discriminant_eval
  lazard_cyclic_fourier_fifth_alternating_eval //
  /lazard_root_epsilon.
finish_lazard_root_projection_I_ring.
Qed.

Definition lazard_cyclic_alternating_twists (a : LazardCyclicFive F) :
    LazardCyclicFive F :=
  lazard_cyclic_add
    (lazard_cyclic_sub a (lazard_cyclic_twist2 a))
    (lazard_cyclic_sub
      (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))
      (lazard_cyclic_twist2
        (lazard_cyclic_twist2 (lazard_cyclic_twist2 a)))).

Lemma lazard_cyclic_fourier_fifth_alternating_as_twists roots :
  lazard_cyclic_fourier_fifth_alternating roots =
    lazard_cyclic_alternating_twists
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)).
Proof.
rewrite /lazard_cyclic_fourier_fifth_alternating
  /lazard_cyclic_alternating_twists
  lazard_cyclic_power_P2 lazard_cyclic_power_P4 lazard_cyclic_power_P3.
by rewrite lazard_cyclic_power_P2 lazard_cyclic_power_P4
  lazard_cyclic_power_P2.
Qed.

(** The discriminant vector and alternating character orbit have opposite
    twist signs.  Their product is fixed, with an especially sparse shape. *)
Lemma lazard_cyclic_discriminant_alternating_shape a :
  let v := lazard_cyclic1 a - lazard_cyclic2 a -
    lazard_cyclic3 a + lazard_cyclic4 a in
  lazard_cyclic_mul lazard_cyclic_discriminant
      (lazard_cyclic_alternating_twists a) =
    {| lazard_cyclic0 := 4%:R * v;
       lazard_cyclic1 := - v;
       lazard_cyclic2 := - v;
       lazard_cyclic3 := - v;
       lazard_cyclic4 := - v |}.
Proof.
rewrite /lazard_cyclic_alternating_twists /lazard_cyclic_discriminant
  /lazard_cyclic_mul /lazard_cyclic_add /lazard_cyclic_sub
  /lazard_cyclic_neg /lazard_cyclic_twist2 /=.
apply: lazard_cyclic_ext=> /=; finish_lazard_root_projection_I_ring.
Qed.

Lemma lazard_cyclic_I_vector_shape roots :
  let a := lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots) in
  let v := lazard_cyclic1 a - lazard_cyclic2 a -
    lazard_cyclic3 a + lazard_cyclic4 a in
  lazard_cyclic_I_vector roots =
    {| lazard_cyclic0 :=
         lazard_root_epsilon_product roots * (4%:R * v);
       lazard_cyclic1 := lazard_root_epsilon_product roots * (- v);
       lazard_cyclic2 := lazard_root_epsilon_product roots * (- v);
       lazard_cyclic3 := lazard_root_epsilon_product roots * (- v);
       lazard_cyclic4 := lazard_root_epsilon_product roots * (- v) |}.
Proof.
rewrite /lazard_cyclic_I_vector
  lazard_cyclic_fourier_fifth_alternating_as_twists
  lazard_cyclic_discriminant_alternating_shape
  /lazard_cyclic_scale /=.
reflexivity.
Qed.

Lemma lazard_cyclic_I_vector_tail_equal roots :
  lazard_cyclic1 (lazard_cyclic_I_vector roots) =
    lazard_cyclic2 (lazard_cyclic_I_vector roots) /\
  lazard_cyclic2 (lazard_cyclic_I_vector roots) =
    lazard_cyclic3 (lazard_cyclic_I_vector roots) /\
  lazard_cyclic3 (lazard_cyclic_I_vector roots) =
    lazard_cyclic4 (lazard_cyclic_I_vector roots).
Proof. by rewrite lazard_cyclic_I_vector_shape. Qed.

Lemma lazard_cyclic_I_vector_difference roots :
  lazard_cyclic0 (lazard_cyclic_I_vector roots) -
      lazard_cyclic1 (lazard_cyclic_I_vector roots) =
    5%:R * lazard_root_epsilon_product roots *
      (lazard_cyclic1
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) -
       lazard_cyclic2
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) -
       lazard_cyclic3
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) +
       lazard_cyclic4
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots))).
Proof.
rewrite lazard_cyclic_I_vector_shape /=.
finish_lazard_root_projection_I_ring.
Qed.

(** Root-only degree-ten coefficient identity underlying Lazard's I. *)
Lemma lazard_cyclic_fourier_fifth_I_core roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_root_epsilon_product roots *
      (lazard_cyclic1
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) -
       lazard_cyclic2
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) -
       lazard_cyclic3
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) +
       lazard_cyclic4
          (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots))) =
    lazard_root_invariant_I
      (@lazard_depressed_of_roots F roots) (@lazard_root_invariants F roots).
Proof.
have hx4 := lazard_root_sum_zero_last hsum.
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
rewrite /lazard_root_epsilon_product /lazard_root_invariant_I
  /lazard_depressed_of_roots /= /lazard_root_invariants /=
  /lazard_root_orbit_formula /lazard_root_esymm2 /lazard_root_esymm3
  /lazard_root_esymm4 /lazard_root_esymm5 hx4.
finish_lazard_root_projection_I_ring.
Qed.

(** Direct root-level certificate for Lazard's second projection. *)
Theorem lazard_root_standard_projection_I omega t u roots
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_standard_projections (lazard_root_epsilon omega roots) t u
      (lazard_root_fourier_fifth_orbit omega roots) p1 =
    5%:R * lazard_root_invariant_I
      (@lazard_depressed_of_roots F roots) (@lazard_root_invariants F roots).
Proof.
transitivity (lazard_cyclic_eval omega (lazard_cyclic_I_vector roots)).
- rewrite lazard_standard_projection1
    lazard_root_fourier_fifth_orbit_p0
    lazard_root_fourier_fifth_orbit_p1
    lazard_root_fourier_fifth_orbit_p2
    lazard_root_fourier_fifth_orbit_p3
    lazard_cyclic_I_vector_eval //.
  finish_lazard_root_projection_I_ring.
- have [h12 [h23 h34]] := lazard_cyclic_I_vector_tail_equal roots.
  rewrite (lazard_cyclic_eval_equal_tail omega_primitive h12 h23 h34)
    lazard_cyclic_I_vector_difference.
  rewrite -(lazard_cyclic_fourier_fifth_I_core hsum).
  finish_lazard_root_projection_I_ring.
Qed.


End RootProjectionI.

End PolynomialFormulasLazardQuinticRootProjectionI.
