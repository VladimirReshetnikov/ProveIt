From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticFourier LazardQuinticProjection.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root-level source data for Lazard's first two projections.  Everything
    here is defined directly from an ordered five-tuple.  The H theorem below
    and the companion I module use only the depressed relation (sum of the
    roots is zero) and the primitive-fifth-root relations. *)
Module PolynomialFormulasLazardQuinticRootProjections.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Local Open Scope ring_scope.

Section RootProjections.

Variable F : fieldType.

(** The five elementary symmetric expressions, written out so the bridge
    is independent of any polynomial-root enumeration API. *)
Definition lazard_root_esymm1 (roots : 5.-tuple F) : F :=
  tnth roots o0 + tnth roots o1 + tnth roots o2 + tnth roots o3 +
    tnth roots o4.

Definition lazard_root_esymm2 (roots : 5.-tuple F) : F :=
  tnth roots o0 * tnth roots o1 + tnth roots o0 * tnth roots o2 +
  tnth roots o0 * tnth roots o3 + tnth roots o0 * tnth roots o4 +
  tnth roots o1 * tnth roots o2 + tnth roots o1 * tnth roots o3 +
  tnth roots o1 * tnth roots o4 + tnth roots o2 * tnth roots o3 +
  tnth roots o2 * tnth roots o4 + tnth roots o3 * tnth roots o4.

Definition lazard_root_esymm3 (roots : 5.-tuple F) : F :=
  tnth roots o0 * tnth roots o1 * tnth roots o2 +
  tnth roots o0 * tnth roots o1 * tnth roots o3 +
  tnth roots o0 * tnth roots o1 * tnth roots o4 +
  tnth roots o0 * tnth roots o2 * tnth roots o3 +
  tnth roots o0 * tnth roots o2 * tnth roots o4 +
  tnth roots o0 * tnth roots o3 * tnth roots o4 +
  tnth roots o1 * tnth roots o2 * tnth roots o3 +
  tnth roots o1 * tnth roots o2 * tnth roots o4 +
  tnth roots o1 * tnth roots o3 * tnth roots o4 +
  tnth roots o2 * tnth roots o3 * tnth roots o4.

Definition lazard_root_esymm4 (roots : 5.-tuple F) : F :=
  tnth roots o0 * tnth roots o1 * tnth roots o2 * tnth roots o3 +
  tnth roots o0 * tnth roots o1 * tnth roots o2 * tnth roots o4 +
  tnth roots o0 * tnth roots o1 * tnth roots o3 * tnth roots o4 +
  tnth roots o0 * tnth roots o2 * tnth roots o3 * tnth roots o4 +
  tnth roots o1 * tnth roots o2 * tnth roots o3 * tnth roots o4.

Definition lazard_root_esymm5 (roots : 5.-tuple F) : F :=
  tnth roots o0 * tnth roots o1 * tnth roots o2 * tnth roots o3 *
    tnth roots o4.

Record LazardDepressedRootCoefficients := {
  lazard_root_p : F;
  lazard_root_q : F;
  lazard_root_r : F;
  lazard_root_s : F
}.

(** Coefficients of [X^5 + p X^3 + q X^2 + r X + s]. *)
Definition lazard_depressed_of_roots (roots : 5.-tuple F) :
    LazardDepressedRootCoefficients :=
  {| lazard_root_p := lazard_root_esymm2 roots;
     lazard_root_q := - lazard_root_esymm3 roots;
     lazard_root_r := lazard_root_esymm4 roots;
     lazard_root_s := - lazard_root_esymm5 roots |}.

(** Lazard's shared ten-term metacyclic orbit formula. *)
Definition lazard_root_orbit_formula (a b : nat)
    (roots : 5.-tuple F) : F :=
  tnth roots o0 ^+ a * tnth roots o1 ^+ b * tnth roots o4 ^+ b +
  tnth roots o0 ^+ a * tnth roots o2 ^+ b * tnth roots o3 ^+ b +
  tnth roots o1 ^+ a * tnth roots o0 ^+ b * tnth roots o2 ^+ b +
  tnth roots o1 ^+ a * tnth roots o3 ^+ b * tnth roots o4 ^+ b +
  tnth roots o2 ^+ a * tnth roots o0 ^+ b * tnth roots o4 ^+ b +
  tnth roots o2 ^+ a * tnth roots o1 ^+ b * tnth roots o3 ^+ b +
  tnth roots o3 ^+ a * tnth roots o0 ^+ b * tnth roots o1 ^+ b +
  tnth roots o3 ^+ a * tnth roots o2 ^+ b * tnth roots o4 ^+ b +
  tnth roots o4 ^+ a * tnth roots o0 ^+ b * tnth roots o3 ^+ b +
  tnth roots o4 ^+ a * tnth roots o1 ^+ b * tnth roots o2 ^+ b.

Record LazardRootInvariants := {
  lazard_root_i4 : F;
  lazard_root_i5 : F;
  lazard_root_i6 : F;
  lazard_root_i7 : F;
  lazard_root_i8 : F
}.

Definition lazard_root_invariants (roots : 5.-tuple F) :
    LazardRootInvariants :=
  {| lazard_root_i4 := lazard_root_orbit_formula 2 1 roots;
     lazard_root_i5 := lazard_root_orbit_formula 3 1 roots;
     lazard_root_i6 := lazard_root_orbit_formula 4 1 roots;
     lazard_root_i7 := lazard_root_orbit_formula 3 2 roots;
     lazard_root_i8 := lazard_root_orbit_formula 4 2 roots |}.

Definition lazard_root_invariant_H
    (c : LazardDepressedRootCoefficients)
    (i : LazardRootInvariants) : F :=
  25%:R * (2%:R * lazard_root_i5 i -
    lazard_root_p c * lazard_root_q c - 5%:R * lazard_root_s c).

Definition lazard_root_invariant_I
    (c : LazardDepressedRootCoefficients)
    (i : LazardRootInvariants) : F :=
  25%:R *
    (40%:R * lazard_root_p c * lazard_root_i8 i -
     70%:R * lazard_root_q c * lazard_root_i7 i +
     (- 24%:R * lazard_root_p c ^+ 2 + 100%:R * lazard_root_r c) *
       lazard_root_i6 i +
     (68%:R * lazard_root_p c * lazard_root_q c -
       300%:R * lazard_root_s c) * lazard_root_i5 i +
     (- 24%:R * lazard_root_p c ^+ 3 +
       100%:R * lazard_root_p c * lazard_root_r c -
       46%:R * lazard_root_q c ^+ 2) * lazard_root_i4 i -
     80%:R * lazard_root_p c ^+ 3 * lazard_root_r c +
     20%:R * lazard_root_p c ^+ 2 * lazard_root_q c ^+ 2 -
     255%:R * lazard_root_p c * lazard_root_q c * lazard_root_s c +
     160%:R * lazard_root_p c * lazard_root_r c ^+ 2 -
     28%:R * lazard_root_q c ^+ 2 * lazard_root_r c +
     125%:R * lazard_root_s c ^+ 2).

(** Positive-exponent Fourier convention. *)
Definition lazard_root_fourier_P1 (omega : F) (roots : 5.-tuple F) : F :=
  tnth roots o0 + omega * tnth roots o1 + omega ^+ 2 * tnth roots o2 +
    omega ^+ 3 * tnth roots o3 + omega ^+ 4 * tnth roots o4.

Definition lazard_root_fourier_P2 (omega : F) (roots : 5.-tuple F) : F :=
  tnth roots o0 + omega ^+ 2 * tnth roots o1 +
    omega ^+ 4 * tnth roots o2 + omega * tnth roots o3 +
    omega ^+ 3 * tnth roots o4.

Definition lazard_root_fourier_P3 (omega : F) (roots : 5.-tuple F) : F :=
  tnth roots o0 + omega ^+ 3 * tnth roots o1 + omega * tnth roots o2 +
    omega ^+ 4 * tnth roots o3 + omega ^+ 2 * tnth roots o4.

Definition lazard_root_fourier_P4 (omega : F) (roots : 5.-tuple F) : F :=
  tnth roots o0 + omega ^+ 4 * tnth roots o1 +
    omega ^+ 3 * tnth roots o2 + omega ^+ 2 * tnth roots o3 +
    omega * tnth roots o4.

(** Lazard orbit order: [P1^5,P2^5,P4^5,P3^5]. *)
Definition lazard_root_fourier_fifth_orbit
    (omega : F) (roots : 5.-tuple F) (j : 'I_4) : F :=
  nth 0
    [:: lazard_root_fourier_P1 omega roots ^+ 5;
        lazard_root_fourier_P2 omega roots ^+ 5;
        lazard_root_fourier_P4 omega roots ^+ 5;
        lazard_root_fourier_P3 omega roots ^+ 5] j.

Lemma lazard_root_fourier_fifth_orbit_p0 omega roots :
  lazard_root_fourier_fifth_orbit omega roots p0 =
    lazard_root_fourier_P1 omega roots ^+ 5.
Proof. by rewrite /lazard_root_fourier_fifth_orbit /p0. Qed.

Lemma lazard_root_fourier_fifth_orbit_p1 omega roots :
  lazard_root_fourier_fifth_orbit omega roots p1 =
    lazard_root_fourier_P2 omega roots ^+ 5.
Proof. by rewrite /lazard_root_fourier_fifth_orbit /p1. Qed.

Lemma lazard_root_fourier_fifth_orbit_p2 omega roots :
  lazard_root_fourier_fifth_orbit omega roots p2 =
    lazard_root_fourier_P4 omega roots ^+ 5.
Proof. by rewrite /lazard_root_fourier_fifth_orbit /p2. Qed.

Lemma lazard_root_fourier_fifth_orbit_p3 omega roots :
  lazard_root_fourier_fifth_orbit omega roots p3 =
    lazard_root_fourier_P3 omega roots ^+ 5.
Proof. by rewrite /lazard_root_fourier_fifth_orbit /p3. Qed.

(** The same source, expressed through the shared Fourier definition. *)
Lemma lazard_root_fourier_P1E omega roots :
  lazard_root_fourier_P1 omega roots = lazard_fourier_sum omega roots o1.
Proof.
rewrite /lazard_root_fourier_P1 /lazard_fourier_sum lazard_sum_ord5 /=.
by rewrite !muln1 expr0 expr1 !mul1r.
Qed.

Lemma lazard_primitive_fifth_power6 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 6 = omega.
Proof.
rewrite -[RHS]expr1; apply/eqP.
by rewrite (eq_prim_root_expr omega_primitive).
Qed.

Lemma lazard_primitive_fifth_power5 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 5 = 1.
Proof. exact: prim_expr_order omega_primitive. Qed.

Lemma lazard_primitive_fifth_power7 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 7 = omega ^+ 2.
Proof. apply/eqP; by rewrite (eq_prim_root_expr omega_primitive). Qed.

Lemma lazard_primitive_fifth_power8 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 8 = omega ^+ 3.
Proof. apply/eqP; by rewrite (eq_prim_root_expr omega_primitive). Qed.

Lemma lazard_primitive_fifth_power9 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 9 = omega ^+ 4.
Proof. apply/eqP; by rewrite (eq_prim_root_expr omega_primitive). Qed.

Lemma lazard_primitive_fifth_power12 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 12 = omega ^+ 2.
Proof. apply/eqP; by rewrite (eq_prim_root_expr omega_primitive). Qed.

Lemma lazard_primitive_fifth_power16 (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 16 = omega.
Proof.
rewrite -[RHS]expr1; apply/eqP.
by rewrite (eq_prim_root_expr omega_primitive).
Qed.

Lemma lazard_root_fourier_P2E omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_fourier_P2 omega roots = lazard_fourier_sum omega roots o2.
Proof.
rewrite /lazard_root_fourier_P2 /lazard_fourier_sum lazard_sum_ord5.
change
  ((tnth roots o0 + omega ^+ 2 * tnth roots o1 +
    omega ^+ 4 * tnth roots o2 + omega * tnth roots o3 +
    omega ^+ 3 * tnth roots o4) =
  (omega ^+ 0 * tnth roots o0 + omega ^+ 2 * tnth roots o1 +
    omega ^+ 4 * tnth roots o2 + omega ^+ 6 * tnth roots o3 +
    omega ^+ 8 * tnth roots o4)).
by rewrite expr0 mul1r
  (lazard_primitive_fifth_power6 omega_primitive)
  (lazard_primitive_fifth_power8 omega_primitive).
Qed.

Lemma lazard_root_fourier_P3E omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_fourier_P3 omega roots = lazard_fourier_sum omega roots o3.
Proof.
rewrite /lazard_root_fourier_P3 /lazard_fourier_sum lazard_sum_ord5.
change
  ((tnth roots o0 + omega ^+ 3 * tnth roots o1 +
    omega * tnth roots o2 + omega ^+ 4 * tnth roots o3 +
    omega ^+ 2 * tnth roots o4) =
  (omega ^+ 0 * tnth roots o0 + omega ^+ 3 * tnth roots o1 +
    omega ^+ 6 * tnth roots o2 + omega ^+ 9 * tnth roots o3 +
    omega ^+ 12 * tnth roots o4)).
by rewrite expr0 mul1r
  (lazard_primitive_fifth_power6 omega_primitive)
  (lazard_primitive_fifth_power9 omega_primitive)
  (lazard_primitive_fifth_power12 omega_primitive).
Qed.

Lemma lazard_root_fourier_P4E omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_fourier_P4 omega roots = lazard_fourier_sum omega roots o4.
Proof.
rewrite /lazard_root_fourier_P4 /lazard_fourier_sum lazard_sum_ord5.
change
  ((tnth roots o0 + omega ^+ 4 * tnth roots o1 +
    omega ^+ 3 * tnth roots o2 + omega ^+ 2 * tnth roots o3 +
    omega * tnth roots o4) =
  (omega ^+ 0 * tnth roots o0 + omega ^+ 4 * tnth roots o1 +
    omega ^+ 8 * tnth roots o2 + omega ^+ 12 * tnth roots o3 +
    omega ^+ 16 * tnth roots o4)).
by rewrite expr0 mul1r
  (lazard_primitive_fifth_power8 omega_primitive)
  (lazard_primitive_fifth_power12 omega_primitive)
  (lazard_primitive_fifth_power16 omega_primitive).
Qed.

Definition lazard_root_discriminant_factor (omega : F) : F :=
  omega + omega ^+ 4 - omega ^+ 2 - omega ^+ 3.

Definition lazard_root_epsilon_product (roots : 5.-tuple F) : F :=
  (tnth roots o1 - tnth roots o2 - tnth roots o3 + tnth roots o4) *
  (tnth roots o2 - tnth roots o3 - tnth roots o4 + tnth roots o0) *
  (tnth roots o3 - tnth roots o4 - tnth roots o0 + tnth roots o1) *
  (tnth roots o4 - tnth roots o0 - tnth roots o1 + tnth roots o2) *
  (tnth roots o0 - tnth roots o1 - tnth roots o2 + tnth roots o3).

Definition lazard_root_epsilon (omega : F) (roots : 5.-tuple F) : F :=
  lazard_root_discriminant_factor omega *
    lazard_root_epsilon_product roots.

(** Local bridge from MathComp operations to the reflective [ring] tactic. *)
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

Lemma lazard_root_projection_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_root_projection_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_root_projection_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_root_projection_ring_theory :
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

Add Ring lazard_root_projection_ring : lazard_root_projection_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_root_projection_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_root_projection_four_natrE :
  (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -lazard_root_projection_two_natrE.
  exact: (@natrD F 2 1).
rewrite -h3.
exact: (@natrD F 3 1).
Qed.

Lemma lazard_root_projection_five_natrE :
  (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
have h4 : (4%:R : F) = 1 + 1 + 1 + 1.
  have h3 : (3%:R : F) = 1 + 1 + 1.
    rewrite -lazard_root_projection_two_natrE.
    exact: (@natrD F 2 1).
  rewrite -h3.
  exact: (@natrD F 3 1).
rewrite -h4.
exact: (@natrD F 4 1).
Qed.

Lemma lazard_root_projection_twenty_five_natrE :
  (25%:R : F) = 5%:R * 5%:R.
Proof. exact: (@natrM F 5 5). Qed.

Lemma lazard_root_projection_three_natrE :
  (3%:R : F) = 2%:R + 1.
Proof. exact: (@natrD F 2 1). Qed.
Lemma lazard_root_projection_seven_natrE :
  (7%:R : F) = 5%:R + 2%:R.
Proof. exact: (@natrD F 5 2). Qed.
Lemma lazard_root_projection_eight_natrE :
  (8%:R : F) = 4%:R * 2%:R.
Proof. exact: (@natrM F 4 2). Qed.
Lemma lazard_root_projection_ten_natrE :
  (10%:R : F) = 5%:R * 2%:R.
Proof. exact: (@natrM F 5 2). Qed.
Lemma lazard_root_projection_sixteen_natrE :
  (16%:R : F) = 8%:R * 2%:R.
Proof. exact: (@natrM F 8 2). Qed.
Lemma lazard_root_projection_seventeen_natrE :
  (17%:R : F) = 10%:R + 7%:R.
Proof. exact: (@natrD F 10 7). Qed.
Lemma lazard_root_projection_twenty_natrE :
  (20%:R : F) = 10%:R * 2%:R.
Proof. exact: (@natrM F 10 2). Qed.
Lemma lazard_root_projection_twenty_three_natrE :
  (23%:R : F) = 20%:R + 3%:R.
Proof. exact: (@natrD F 20 3). Qed.
Lemma lazard_root_projection_twenty_four_natrE :
  (24%:R : F) = 3%:R * 8%:R.
Proof. exact: (@natrM F 3 8). Qed.
Lemma lazard_root_projection_twenty_eight_natrE :
  (28%:R : F) = 4%:R * 7%:R.
Proof. exact: (@natrM F 4 7). Qed.
Lemma lazard_root_projection_forty_natrE :
  (40%:R : F) = 5%:R * 8%:R.
Proof. exact: (@natrM F 5 8). Qed.
Lemma lazard_root_projection_forty_six_natrE :
  (46%:R : F) = 2%:R * 23%:R.
Proof. exact: (@natrM F 2 23). Qed.
Lemma lazard_root_projection_fifty_natrE :
  (50%:R : F) = 5%:R * 10%:R.
Proof. exact: (@natrM F 5 10). Qed.
Lemma lazard_root_projection_fifty_one_natrE :
  (51%:R : F) = 50%:R + 1.
Proof. exact: (@natrD F 50 1). Qed.
Lemma lazard_root_projection_sixty_eight_natrE :
  (68%:R : F) = 4%:R * 17%:R.
Proof. exact: (@natrM F 4 17). Qed.
Lemma lazard_root_projection_seventy_natrE :
  (70%:R : F) = 7%:R * 10%:R.
Proof. exact: (@natrM F 7 10). Qed.
Lemma lazard_root_projection_eighty_natrE :
  (80%:R : F) = 8%:R * 10%:R.
Proof. exact: (@natrM F 8 10). Qed.
Lemma lazard_root_projection_hundred_natrE :
  (100%:R : F) = 10%:R * 10%:R.
Proof. exact: (@natrM F 10 10). Qed.
Lemma lazard_root_projection_hundred_twenty_five_natrE :
  (125%:R : F) = 5%:R * 25%:R.
Proof. exact: (@natrM F 5 25). Qed.
Lemma lazard_root_projection_hundred_sixty_natrE :
  (160%:R : F) = 16%:R * 10%:R.
Proof. exact: (@natrM F 16 10). Qed.
Lemma lazard_root_projection_two_hundred_fifty_five_natrE :
  (255%:R : F) = 5%:R * 51%:R.
Proof. exact: (@natrM F 5 51). Qed.
Lemma lazard_root_projection_three_hundred_natrE :
  (300%:R : F) = 3%:R * 100%:R.
Proof. exact: (@natrM F 3 100). Qed.

Lemma lazard_root_projection_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.
Lemma lazard_root_projection_expr3 (x : F) : x ^+ 3 = x * x * x.
Proof. by rewrite exprSr expr2. Qed.
Lemma lazard_root_projection_expr4 (x : F) : x ^+ 4 = x * x * x * x.
Proof. by rewrite exprSr lazard_root_projection_expr3. Qed.
Lemma lazard_root_projection_expr5 (x : F) :
  x ^+ 5 = x * x * x * x * x.
Proof. by rewrite exprSr lazard_root_projection_expr4. Qed.
Lemma lazard_root_projection_expr6 (x : F) :
  x ^+ 6 = x * x * x * x * x * x.
Proof. by rewrite exprSr lazard_root_projection_expr5. Qed.
Lemma lazard_root_projection_expr7 (x : F) :
  x ^+ 7 = x * x * x * x * x * x * x.
Proof. by rewrite exprSr lazard_root_projection_expr6. Qed.
Lemma lazard_root_projection_expr8 (x : F) :
  x ^+ 8 = x * x * x * x * x * x * x * x.
Proof. by rewrite exprSr lazard_root_projection_expr7. Qed.

Ltac finish_lazard_root_projection_ring :=
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
    | rewrite lazard_root_projection_ring_addE
    | rewrite lazard_root_projection_ring_mulE
    | rewrite lazard_root_projection_ring_subE
    | rewrite lazard_root_projection_ring_oppE
    | rewrite lazard_root_projection_ring_zeroE
    | rewrite lazard_root_projection_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** Eliminate the fifth root coordinate once, rather than duplicating the
    sum-zero rearrangement in every projection proof. *)
Lemma lazard_root_sum_zero_last roots
    (hsum : lazard_root_esymm1 roots = 0) :
  tnth roots o4 =
    - (tnth roots o0 + tnth roots o1 + tnth roots o2 + tnth roots o3).
Proof.
rewrite /lazard_root_esymm1 in hsum.
apply: subr0_eq.
transitivity
  (tnth roots o0 + tnth roots o1 + tnth roots o2 + tnth roots o3 +
    tnth roots o4).
- finish_lazard_root_projection_ring.
- exact hsum.
Qed.

(** Primitive fifth roots satisfy the reduced cyclotomic relation used by
    both direct expansion certificates. *)
Lemma lazard_primitive_fifth_root_fourth (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  omega ^+ 4 = - (1 + omega + omega ^+ 2 + omega ^+ 3).
Proof.
have hgeom := @lazard_geometric_orthogonality_nat F omega omega_primitive 1.
rewrite /lazard_geometric_sum lazard_sum_ord5 /= in hgeom.
rewrite !mul1n expr0 expr1 in hgeom.
apply: subr0_eq.
transitivity (1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4).
- finish_lazard_root_projection_ring.
- exact hgeom.
Qed.

(** A five-coordinate cyclic convolution algebra.  It is the group algebra
    of the exponents modulo five, written explicitly so all finite-index
    arithmetic is shared by the H and I certificates. *)
Record LazardCyclicFive := {
  lazard_cyclic0 : F;
  lazard_cyclic1 : F;
  lazard_cyclic2 : F;
  lazard_cyclic3 : F;
  lazard_cyclic4 : F
}.

Definition lazard_cyclic_add (a b : LazardCyclicFive) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := lazard_cyclic0 a + lazard_cyclic0 b;
     lazard_cyclic1 := lazard_cyclic1 a + lazard_cyclic1 b;
     lazard_cyclic2 := lazard_cyclic2 a + lazard_cyclic2 b;
     lazard_cyclic3 := lazard_cyclic3 a + lazard_cyclic3 b;
     lazard_cyclic4 := lazard_cyclic4 a + lazard_cyclic4 b |}.

Definition lazard_cyclic_neg (a : LazardCyclicFive) : LazardCyclicFive :=
  {| lazard_cyclic0 := - lazard_cyclic0 a;
     lazard_cyclic1 := - lazard_cyclic1 a;
     lazard_cyclic2 := - lazard_cyclic2 a;
     lazard_cyclic3 := - lazard_cyclic3 a;
     lazard_cyclic4 := - lazard_cyclic4 a |}.

Definition lazard_cyclic_sub (a b : LazardCyclicFive) :
    LazardCyclicFive := lazard_cyclic_add a (lazard_cyclic_neg b).

Definition lazard_cyclic_scale (c : F) (a : LazardCyclicFive) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := c * lazard_cyclic0 a;
     lazard_cyclic1 := c * lazard_cyclic1 a;
     lazard_cyclic2 := c * lazard_cyclic2 a;
     lazard_cyclic3 := c * lazard_cyclic3 a;
     lazard_cyclic4 := c * lazard_cyclic4 a |}.

Definition lazard_cyclic_mul (a b : LazardCyclicFive) :
    LazardCyclicFive :=
  {| lazard_cyclic0 :=
       lazard_cyclic0 a * lazard_cyclic0 b +
       lazard_cyclic1 a * lazard_cyclic4 b +
       lazard_cyclic2 a * lazard_cyclic3 b +
       lazard_cyclic3 a * lazard_cyclic2 b +
       lazard_cyclic4 a * lazard_cyclic1 b;
     lazard_cyclic1 :=
       lazard_cyclic0 a * lazard_cyclic1 b +
       lazard_cyclic1 a * lazard_cyclic0 b +
       lazard_cyclic2 a * lazard_cyclic4 b +
       lazard_cyclic3 a * lazard_cyclic3 b +
       lazard_cyclic4 a * lazard_cyclic2 b;
     lazard_cyclic2 :=
       lazard_cyclic0 a * lazard_cyclic2 b +
       lazard_cyclic1 a * lazard_cyclic1 b +
       lazard_cyclic2 a * lazard_cyclic0 b +
       lazard_cyclic3 a * lazard_cyclic4 b +
       lazard_cyclic4 a * lazard_cyclic3 b;
     lazard_cyclic3 :=
       lazard_cyclic0 a * lazard_cyclic3 b +
       lazard_cyclic1 a * lazard_cyclic2 b +
       lazard_cyclic2 a * lazard_cyclic1 b +
       lazard_cyclic3 a * lazard_cyclic0 b +
       lazard_cyclic4 a * lazard_cyclic4 b;
     lazard_cyclic4 :=
       lazard_cyclic0 a * lazard_cyclic4 b +
       lazard_cyclic1 a * lazard_cyclic3 b +
       lazard_cyclic2 a * lazard_cyclic2 b +
       lazard_cyclic3 a * lazard_cyclic1 b +
       lazard_cyclic4 a * lazard_cyclic0 b |}.

Lemma lazard_cyclic_mul0E a b :
  lazard_cyclic0 (lazard_cyclic_mul a b) =
    lazard_cyclic0 a * lazard_cyclic0 b +
    lazard_cyclic1 a * lazard_cyclic4 b +
    lazard_cyclic2 a * lazard_cyclic3 b +
    lazard_cyclic3 a * lazard_cyclic2 b +
    lazard_cyclic4 a * lazard_cyclic1 b.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_mul1E a b :
  lazard_cyclic1 (lazard_cyclic_mul a b) =
    lazard_cyclic0 a * lazard_cyclic1 b +
    lazard_cyclic1 a * lazard_cyclic0 b +
    lazard_cyclic2 a * lazard_cyclic4 b +
    lazard_cyclic3 a * lazard_cyclic3 b +
    lazard_cyclic4 a * lazard_cyclic2 b.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_mul2E a b :
  lazard_cyclic2 (lazard_cyclic_mul a b) =
    lazard_cyclic0 a * lazard_cyclic2 b +
    lazard_cyclic1 a * lazard_cyclic1 b +
    lazard_cyclic2 a * lazard_cyclic0 b +
    lazard_cyclic3 a * lazard_cyclic4 b +
    lazard_cyclic4 a * lazard_cyclic3 b.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_mul3E a b :
  lazard_cyclic3 (lazard_cyclic_mul a b) =
    lazard_cyclic0 a * lazard_cyclic3 b +
    lazard_cyclic1 a * lazard_cyclic2 b +
    lazard_cyclic2 a * lazard_cyclic1 b +
    lazard_cyclic3 a * lazard_cyclic0 b +
    lazard_cyclic4 a * lazard_cyclic4 b.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_mul4E a b :
  lazard_cyclic4 (lazard_cyclic_mul a b) =
    lazard_cyclic0 a * lazard_cyclic4 b +
    lazard_cyclic1 a * lazard_cyclic3 b +
    lazard_cyclic2 a * lazard_cyclic2 b +
    lazard_cyclic3 a * lazard_cyclic1 b +
    lazard_cyclic4 a * lazard_cyclic0 b.
Proof. reflexivity. Qed.

Definition lazard_cyclic_fifth_power (a : LazardCyclicFive) :
    LazardCyclicFive :=
  lazard_cyclic_mul (lazard_cyclic_mul a a)
    (lazard_cyclic_mul (lazard_cyclic_mul a a) a).

Definition lazard_cyclic_eval (omega : F) (a : LazardCyclicFive) : F :=
  lazard_cyclic0 a + omega * lazard_cyclic1 a +
    omega ^+ 2 * lazard_cyclic2 a + omega ^+ 3 * lazard_cyclic3 a +
    omega ^+ 4 * lazard_cyclic4 a.

Lemma lazard_cyclic_eval_add omega a b :
  lazard_cyclic_eval omega (lazard_cyclic_add a b) =
    lazard_cyclic_eval omega a + lazard_cyclic_eval omega b.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_add /=.
finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_eval_neg omega a :
  lazard_cyclic_eval omega (lazard_cyclic_neg a) =
    - lazard_cyclic_eval omega a.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_neg /=.
finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_eval_sub omega a b :
  lazard_cyclic_eval omega (lazard_cyclic_sub a b) =
    lazard_cyclic_eval omega a - lazard_cyclic_eval omega b.
Proof.
rewrite /lazard_cyclic_sub lazard_cyclic_eval_add lazard_cyclic_eval_neg.
finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_eval_scale omega c a :
  lazard_cyclic_eval omega (lazard_cyclic_scale c a) =
    c * lazard_cyclic_eval omega a.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_scale /=.
finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_eval_mul omega a b
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_mul a b) =
    lazard_cyclic_eval omega a * lazard_cyclic_eval omega b.
Proof.
transitivity
  (lazard_cyclic0 a * lazard_cyclic0 b +
   (lazard_cyclic0 a * lazard_cyclic1 b +
      lazard_cyclic1 a * lazard_cyclic0 b) * omega +
   (lazard_cyclic0 a * lazard_cyclic2 b +
      lazard_cyclic1 a * lazard_cyclic1 b +
      lazard_cyclic2 a * lazard_cyclic0 b) * omega ^+ 2 +
   (lazard_cyclic0 a * lazard_cyclic3 b +
      lazard_cyclic1 a * lazard_cyclic2 b +
      lazard_cyclic2 a * lazard_cyclic1 b +
      lazard_cyclic3 a * lazard_cyclic0 b) * omega ^+ 3 +
   (lazard_cyclic0 a * lazard_cyclic4 b +
      lazard_cyclic1 a * lazard_cyclic3 b +
      lazard_cyclic2 a * lazard_cyclic2 b +
      lazard_cyclic3 a * lazard_cyclic1 b +
      lazard_cyclic4 a * lazard_cyclic0 b) * omega ^+ 4 +
   (lazard_cyclic1 a * lazard_cyclic4 b +
      lazard_cyclic2 a * lazard_cyclic3 b +
      lazard_cyclic3 a * lazard_cyclic2 b +
      lazard_cyclic4 a * lazard_cyclic1 b) * omega ^+ 5 +
   (lazard_cyclic2 a * lazard_cyclic4 b +
      lazard_cyclic3 a * lazard_cyclic3 b +
      lazard_cyclic4 a * lazard_cyclic2 b) * omega ^+ 6 +
   (lazard_cyclic3 a * lazard_cyclic4 b +
      lazard_cyclic4 a * lazard_cyclic3 b) * omega ^+ 7 +
   lazard_cyclic4 a * lazard_cyclic4 b * omega ^+ 8).
- rewrite /lazard_cyclic_eval /lazard_cyclic_mul /=
    (lazard_primitive_fifth_power5 omega_primitive)
    (lazard_primitive_fifth_power6 omega_primitive)
    (lazard_primitive_fifth_power7 omega_primitive)
    (lazard_primitive_fifth_power8 omega_primitive).
  finish_lazard_root_projection_ring.
- rewrite /lazard_cyclic_eval.
  finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_eval_fifth_power omega a
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_fifth_power a) =
    lazard_cyclic_eval omega a ^+ 5.
Proof.
rewrite /lazard_cyclic_fifth_power !lazard_cyclic_eval_mul //.
finish_lazard_root_projection_ring.
Qed.

Definition lazard_cyclic_fourier_P1 (roots : 5.-tuple F) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := tnth roots o0;
     lazard_cyclic1 := tnth roots o1;
     lazard_cyclic2 := tnth roots o2;
     lazard_cyclic3 := tnth roots o3;
     lazard_cyclic4 := tnth roots o4 |}.

Definition lazard_cyclic_fourier_P2 (roots : 5.-tuple F) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := tnth roots o0;
     lazard_cyclic1 := tnth roots o3;
     lazard_cyclic2 := tnth roots o1;
     lazard_cyclic3 := tnth roots o4;
     lazard_cyclic4 := tnth roots o2 |}.

Definition lazard_cyclic_fourier_P3 (roots : 5.-tuple F) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := tnth roots o0;
     lazard_cyclic1 := tnth roots o2;
     lazard_cyclic2 := tnth roots o4;
     lazard_cyclic3 := tnth roots o1;
     lazard_cyclic4 := tnth roots o3 |}.

Definition lazard_cyclic_fourier_P4 (roots : 5.-tuple F) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := tnth roots o0;
     lazard_cyclic1 := tnth roots o4;
     lazard_cyclic2 := tnth roots o3;
     lazard_cyclic3 := tnth roots o2;
     lazard_cyclic4 := tnth roots o1 |}.

Lemma lazard_cyclic_fourier_P1_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_fourier_P1 roots) =
    lazard_root_fourier_P1 omega roots.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_fourier_P2_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_fourier_P2 roots) =
    lazard_root_fourier_P2 omega roots.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fourier_P2
  /lazard_root_fourier_P2 /=.
finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_fourier_P3_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_fourier_P3 roots) =
    lazard_root_fourier_P3 omega roots.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fourier_P3
  /lazard_root_fourier_P3 /=.
finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_fourier_P4_eval omega roots :
  lazard_cyclic_eval omega (lazard_cyclic_fourier_P4 roots) =
    lazard_root_fourier_P4 omega roots.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fourier_P4
  /lazard_root_fourier_P4 /=.
finish_lazard_root_projection_ring.
Qed.

Definition lazard_cyclic_fourier_fifth_orbit (roots : 5.-tuple F) :
    LazardCyclicFive :=
  lazard_cyclic_add
    (lazard_cyclic_add
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots))
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P2 roots)))
    (lazard_cyclic_add
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P4 roots))
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P3 roots))).

Lemma lazard_cyclic_fourier_fifth_orbit_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_fourier_fifth_orbit roots) =
    lazard_root_fourier_P1 omega roots ^+ 5 +
    lazard_root_fourier_P2 omega roots ^+ 5 +
    lazard_root_fourier_P4 omega roots ^+ 5 +
    lazard_root_fourier_P3 omega roots ^+ 5.
Proof.
rewrite /lazard_cyclic_fourier_fifth_orbit !lazard_cyclic_eval_add
  !lazard_cyclic_eval_fifth_power //
  lazard_cyclic_fourier_P1_eval lazard_cyclic_fourier_P2_eval
  lazard_cyclic_fourier_P4_eval lazard_cyclic_fourier_P3_eval.
finish_lazard_root_projection_ring.
Qed.

(** The exponent-doubling automorphism.  On nonzero characters it cycles
    [P1,P2,P4,P3], exactly the source-orbit order used above. *)
Definition lazard_cyclic_twist2 (a : LazardCyclicFive) :
    LazardCyclicFive :=
  {| lazard_cyclic0 := lazard_cyclic0 a;
     lazard_cyclic1 := lazard_cyclic3 a;
     lazard_cyclic2 := lazard_cyclic1 a;
     lazard_cyclic3 := lazard_cyclic4 a;
     lazard_cyclic4 := lazard_cyclic2 a |}.

Lemma lazard_cyclic_ext (a b : LazardCyclicFive)
    (h0 : lazard_cyclic0 a = lazard_cyclic0 b)
    (h1 : lazard_cyclic1 a = lazard_cyclic1 b)
    (h2 : lazard_cyclic2 a = lazard_cyclic2 b)
    (h3 : lazard_cyclic3 a = lazard_cyclic3 b)
    (h4 : lazard_cyclic4 a = lazard_cyclic4 b) : a = b.
Proof.
case: a h0 h1 h2 h3 h4=> a0 a1 a2 a3 a4 /=.
case: b=> b0 b1 b2 b3 b4 /=.
by move=> -> -> -> -> ->.
Qed.

Lemma lazard_cyclic_twist2_add a b :
  lazard_cyclic_twist2 (lazard_cyclic_add a b) =
    lazard_cyclic_add (lazard_cyclic_twist2 a) (lazard_cyclic_twist2 b).
Proof. reflexivity. Qed.

Lemma lazard_cyclic_twist2_mul a b :
  lazard_cyclic_twist2 (lazard_cyclic_mul a b) =
    lazard_cyclic_mul (lazard_cyclic_twist2 a) (lazard_cyclic_twist2 b).
Proof.
apply: lazard_cyclic_ext=> /=;
  rewrite /lazard_cyclic_twist2 /lazard_cyclic_mul /=;
  finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_twist2_fifth_power a :
  lazard_cyclic_twist2 (lazard_cyclic_fifth_power a) =
    lazard_cyclic_fifth_power (lazard_cyclic_twist2 a).
Proof.
by rewrite /lazard_cyclic_fifth_power !lazard_cyclic_twist2_mul.
Qed.

Lemma lazard_cyclic_twist2_P1 roots :
  lazard_cyclic_twist2 (lazard_cyclic_fourier_P1 roots) =
    lazard_cyclic_fourier_P2 roots.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_twist2_P2 roots :
  lazard_cyclic_twist2 (lazard_cyclic_fourier_P2 roots) =
    lazard_cyclic_fourier_P4 roots.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_twist2_P4 roots :
  lazard_cyclic_twist2 (lazard_cyclic_fourier_P4 roots) =
    lazard_cyclic_fourier_P3 roots.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_twist2_P3 roots :
  lazard_cyclic_twist2 (lazard_cyclic_fourier_P3 roots) =
    lazard_cyclic_fourier_P1 roots.
Proof. reflexivity. Qed.

Lemma lazard_cyclic_power_P2 roots :
  lazard_cyclic_fifth_power (lazard_cyclic_fourier_P2 roots) =
    lazard_cyclic_twist2
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)).
Proof.
by rewrite lazard_cyclic_twist2_fifth_power lazard_cyclic_twist2_P1.
Qed.

Lemma lazard_cyclic_power_P4 roots :
  lazard_cyclic_fifth_power (lazard_cyclic_fourier_P4 roots) =
    lazard_cyclic_twist2
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P2 roots)).
Proof.
by rewrite lazard_cyclic_twist2_fifth_power lazard_cyclic_twist2_P2.
Qed.

Lemma lazard_cyclic_power_P3 roots :
  lazard_cyclic_fifth_power (lazard_cyclic_fourier_P3 roots) =
    lazard_cyclic_twist2
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P4 roots)).
Proof.
by rewrite lazard_cyclic_twist2_fifth_power lazard_cyclic_twist2_P4.
Qed.

Lemma lazard_cyclic_add_rotate_four a b c d :
  lazard_cyclic_add (lazard_cyclic_add a b) (lazard_cyclic_add c d) =
    lazard_cyclic_add (lazard_cyclic_add b c) (lazard_cyclic_add d a).
Proof.
apply: lazard_cyclic_ext=> /=;
  rewrite /lazard_cyclic_add /=;
  finish_lazard_root_projection_ring.
Qed.

Lemma lazard_cyclic_fourier_fifth_orbit_twist2 roots :
  lazard_cyclic_twist2 (lazard_cyclic_fourier_fifth_orbit roots) =
    lazard_cyclic_fourier_fifth_orbit roots.
Proof.
rewrite /lazard_cyclic_fourier_fifth_orbit !lazard_cyclic_twist2_add
  !lazard_cyclic_twist2_fifth_power
  lazard_cyclic_twist2_P1 lazard_cyclic_twist2_P2
  lazard_cyclic_twist2_P4 lazard_cyclic_twist2_P3.
exact: esym (lazard_cyclic_add_rotate_four _ _ _ _).
Qed.

Lemma lazard_cyclic_fourier_fifth_orbit_as_twists roots :
  lazard_cyclic_fourier_fifth_orbit roots =
    let a := lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots) in
    lazard_cyclic_add
      (lazard_cyclic_add a (lazard_cyclic_twist2 a))
      (lazard_cyclic_add
        (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))
        (lazard_cyclic_twist2
          (lazard_cyclic_twist2 (lazard_cyclic_twist2 a)))).
Proof.
rewrite /lazard_cyclic_fourier_fifth_orbit
  lazard_cyclic_power_P2 lazard_cyclic_power_P4 lazard_cyclic_power_P3.
by rewrite lazard_cyclic_power_P2 lazard_cyclic_power_P4
  lazard_cyclic_power_P2.
Qed.

(** Multiplication by a nonzero exponent permutes the four nontrivial
    characters, so the four tail coefficients of their fifth-power orbit
    coincide. *)
Lemma lazard_cyclic_fourier_fifth_orbit_tail_equal roots :
  lazard_cyclic1 (lazard_cyclic_fourier_fifth_orbit roots) =
    lazard_cyclic2 (lazard_cyclic_fourier_fifth_orbit roots) /\
  lazard_cyclic2 (lazard_cyclic_fourier_fifth_orbit roots) =
    lazard_cyclic3 (lazard_cyclic_fourier_fifth_orbit roots) /\
  lazard_cyclic3 (lazard_cyclic_fourier_fifth_orbit roots) =
    lazard_cyclic4 (lazard_cyclic_fourier_fifth_orbit roots).
Proof.
pose orbit := lazard_cyclic_fourier_fifth_orbit roots.
change
  (lazard_cyclic1 orbit = lazard_cyclic2 orbit /\
   lazard_cyclic2 orbit = lazard_cyclic3 orbit /\
   lazard_cyclic3 orbit = lazard_cyclic4 orbit).
have hfix : lazard_cyclic_twist2 orbit = orbit.
  exact: lazard_cyclic_fourier_fifth_orbit_twist2 roots.
clearbody orbit.
have h1 := congr1 lazard_cyclic1 hfix.
have h2 := congr1 lazard_cyclic2 hfix.
have h3 := congr1 lazard_cyclic3 hfix.
rewrite /lazard_cyclic_twist2 /= in h1 h2 h3.
constructor.
- exact h2.
constructor.
- by rewrite -h2 -h1.
- exact: esym h3.
Qed.

(** The zero-minus-tail coordinate of the complete orbit can be computed
    from a single Fourier component; the twist supplies the other three. *)
Lemma lazard_cyclic_fourier_fifth_orbit_difference roots :
  lazard_cyclic0 (lazard_cyclic_fourier_fifth_orbit roots) -
      lazard_cyclic1 (lazard_cyclic_fourier_fifth_orbit roots) =
    4%:R * lazard_cyclic0
      (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) -
    (lazard_cyclic1
        (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) +
     lazard_cyclic2
        (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) +
     lazard_cyclic3
        (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots)) +
     lazard_cyclic4
        (lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots))).
Proof.
rewrite lazard_cyclic_fourier_fifth_orbit_as_twists /=.
pose a := lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots).
change
  (lazard_cyclic0
      (lazard_cyclic_add (lazard_cyclic_add a (lazard_cyclic_twist2 a))
        (lazard_cyclic_add
          (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))
          (lazard_cyclic_twist2
            (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))))) -
   lazard_cyclic1
      (lazard_cyclic_add (lazard_cyclic_add a (lazard_cyclic_twist2 a))
        (lazard_cyclic_add
          (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))
          (lazard_cyclic_twist2
            (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))))) =
   4%:R * lazard_cyclic0 a -
    (lazard_cyclic1 a + lazard_cyclic2 a + lazard_cyclic3 a +
      lazard_cyclic4 a)).
clearbody a.
rewrite /lazard_cyclic_add /lazard_cyclic_twist2 /=.
finish_lazard_root_projection_ring.
Qed.

(** Evaluation of a cyclic vector whose four tail coefficients agree. *)
Lemma lazard_cyclic_eval_equal_tail omega a
    (omega_primitive : 5.-primitive_root omega)
    (h12 : lazard_cyclic1 a = lazard_cyclic2 a)
    (h23 : lazard_cyclic2 a = lazard_cyclic3 a)
    (h34 : lazard_cyclic3 a = lazard_cyclic4 a) :
  lazard_cyclic_eval omega a = lazard_cyclic0 a - lazard_cyclic1 a.
Proof.
have hw4 := lazard_primitive_fifth_root_fourth omega_primitive.
rewrite /lazard_cyclic_eval -h34 -h23 -h12 hw4.
finish_lazard_root_projection_ring.
Qed.

(** The remaining root-only coefficient certificate for H. *)
Lemma lazard_cyclic_fourier_fifth_orbit_H roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_cyclic0 (lazard_cyclic_fourier_fifth_orbit roots) -
      lazard_cyclic1 (lazard_cyclic_fourier_fifth_orbit roots) =
    5%:R * lazard_root_invariant_H
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots).
Proof.
have hx4 := lazard_root_sum_zero_last hsum.
rewrite lazard_cyclic_fourier_fifth_orbit_difference.
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
rewrite lazard_cyclic_mul0E lazard_cyclic_mul1E lazard_cyclic_mul2E
  lazard_cyclic_mul3E lazard_cyclic_mul4E
  hc0 hc1 hc2 hc3 hc4 hs0 hs1 hs2 hs3 hs4
  ha0 ha1 ha2 ha3 ha4.
rewrite /lazard_root_invariant_H /lazard_depressed_of_roots /=
  /lazard_root_invariants /= /lazard_root_orbit_formula
  /lazard_root_esymm2 /lazard_root_esymm3 /lazard_root_esymm5 hx4.
finish_lazard_root_projection_ring.
Qed.

(** Direct root-level certificate for Lazard's first projection. *)
Theorem lazard_root_standard_projection_H omega t u roots
    (omega_primitive : 5.-primitive_root omega)
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_standard_projections omega t u
      (lazard_root_fourier_fifth_orbit omega roots) p0 =
    5%:R * lazard_root_invariant_H
      (lazard_depressed_of_roots roots) (lazard_root_invariants roots).
Proof.
transitivity
  (lazard_cyclic_eval omega (lazard_cyclic_fourier_fifth_orbit roots)).
- rewrite lazard_standard_projection0
    lazard_root_fourier_fifth_orbit_p0
    lazard_root_fourier_fifth_orbit_p1
    lazard_root_fourier_fifth_orbit_p2
    lazard_root_fourier_fifth_orbit_p3
    lazard_cyclic_fourier_fifth_orbit_eval //.
- have [h12 [h23 h34]] := lazard_cyclic_fourier_fifth_orbit_tail_equal roots.
  rewrite (lazard_cyclic_eval_equal_tail omega_primitive h12 h23 h34).
  exact: lazard_cyclic_fourier_fifth_orbit_H hsum.
Qed.

End RootProjections.

End PolynomialFormulasLazardQuinticRootProjections.
