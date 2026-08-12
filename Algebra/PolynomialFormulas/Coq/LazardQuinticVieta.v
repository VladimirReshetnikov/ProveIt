From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticFourier.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Vieta identities for the five inverse-Fourier values in Lazard's
    quintic formula.  The long algebraic identities below are explicit
    polynomial certificates: [ring] checks them in the kernel, and the only
    relation subsequently used is the fifth cyclotomic equation supplied by
    the primitive-root hypothesis. *)
Module PolynomialFormulasLazardQuinticVieta.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticFourier.

Local Open Scope ring_scope.

Section Vieta.

Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : 5.-primitive_root omega.
Hypothesis five_neq0 : (5%:R : F) != 0.

(** The four cyclic expressions in the nonzero Fourier components. *)
Definition lazard_fourier_cyclic2 (a b c d : F) : F :=
  a * d + b * c.

Definition lazard_fourier_cyclic3 (a b c d : F) : F :=
  a ^+ 2 * c + a * b ^+ 2 + b * d ^+ 2 + c ^+ 2 * d.

Definition lazard_fourier_cyclic4 (a b c d : F) : F :=
  a ^+ 2 * d ^+ 2 - a * b * c * d + b ^+ 2 * c ^+ 2 -
    a ^+ 3 * b - a * c ^+ 3 - b ^+ 3 * d - c * d ^+ 3.

Definition lazard_fourier_cyclic5 (a b c d : F) : F :=
  a ^+ 5 + b ^+ 5 + c ^+ 5 + d ^+ 5 -
    5%:R * a ^+ 3 * c * d + 5%:R * a ^+ 2 * b ^+ 2 * d +
    5%:R * a ^+ 2 * b * c ^+ 2 - 5%:R * a * b ^+ 3 * c -
    5%:R * a * b * d ^+ 3 + 5%:R * a * c ^+ 2 * d ^+ 2 +
    5%:R * b ^+ 2 * c * d ^+ 2 - 5%:R * b * c ^+ 3 * d.

(** Unscaled inverse Fourier transform of the four nonzero components.
    Reducing the exponents modulo five is definitionally convenient and is
    equal to the usual transform because [omega] has order five. *)
Definition lazard_inverse_fourier_unscaled
    (a b c d : F) (k : 'I_5) : F :=
  omega ^+ ((nat_of_ord k) %% 5) * a +
  omega ^+ ((2 * nat_of_ord k) %% 5) * b +
  omega ^+ ((3 * nat_of_ord k) %% 5) * c +
  omega ^+ ((4 * nat_of_ord k) %% 5) * d.

Definition lazard_inverse_fourier_output
    (a b c d : F) (k : 'I_5) : F :=
  (5%:R)^-1 * lazard_inverse_fourier_unscaled a b c d k.

Lemma lazard_inverse_fourier_unscaledE a b c d k :
  lazard_inverse_fourier_unscaled a b c d k =
    omega ^+ nat_of_ord k * a +
    omega ^+ (2 * nat_of_ord k) * b +
    omega ^+ (3 * nat_of_ord k) * c +
    omega ^+ (4 * nat_of_ord k) * d.
Proof.
rewrite /lazard_inverse_fourier_unscaled.
by rewrite !prim_expr_mod.
Qed.

(** Explicit elementary symmetric expressions in five indexed values. *)
Definition lazard_five_esymm1 (x : 'I_5 -> F) : F :=
  x o0 + x o1 + x o2 + x o3 + x o4.

Definition lazard_five_esymm2 (x : 'I_5 -> F) : F :=
  x o0 * x o1 + x o0 * x o2 + x o0 * x o3 + x o0 * x o4 +
  x o1 * x o2 + x o1 * x o3 + x o1 * x o4 +
  x o2 * x o3 + x o2 * x o4 + x o3 * x o4.

Definition lazard_five_esymm3 (x : 'I_5 -> F) : F :=
  x o0 * x o1 * x o2 + x o0 * x o1 * x o3 +
  x o0 * x o1 * x o4 + x o0 * x o2 * x o3 +
  x o0 * x o2 * x o4 + x o0 * x o3 * x o4 +
  x o1 * x o2 * x o3 + x o1 * x o2 * x o4 +
  x o1 * x o3 * x o4 + x o2 * x o3 * x o4.

Definition lazard_five_esymm4 (x : 'I_5 -> F) : F :=
  x o0 * x o1 * x o2 * x o3 + x o0 * x o1 * x o2 * x o4 +
  x o0 * x o1 * x o3 * x o4 + x o0 * x o2 * x o3 * x o4 +
  x o1 * x o2 * x o3 * x o4.

Definition lazard_five_esymm5 (x : 'I_5 -> F) : F :=
  x o0 * x o1 * x o2 * x o3 * x o4.

(** The cyclotomic relation is obtained from the geometric-orthogonality
    lemma in [LazardQuinticFourier], so this layer shares the same primitive
    root foundation as the Fourier inversion theorem. *)
Lemma lazard_vieta_cyclotomic :
  1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4 = 0.
Proof.
have h := @lazard_geometric_orthogonality_nat F omega omega_primitive 1.
move: h.
rewrite /lazard_geometric_sum lazard_sum_ord5 /=.
by rewrite !mul1n expr0 expr1.
Qed.

(** Local bridge from MathComp's packed operations to the standard [ring]
    tactic. *)
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

Lemma lazard_vieta_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_vieta_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_vieta_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_vieta_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_vieta_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_vieta_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_vieta_ring_theory :
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

Add Ring lazard_vieta_ring : lazard_vieta_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_vieta_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_vieta_three_natrE : (3%:R : F) = 1 + 1 + 1.
Proof.
rewrite -lazard_vieta_two_natrE.
exact: (@natrD F 2 1).
Qed.

Lemma lazard_vieta_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_vieta_three_natrE.
exact: (@natrD F 3 1).
Qed.

Lemma lazard_vieta_five_natrE :
  (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_vieta_four_natrE.
exact: (@natrD F 4 1).
Qed.

Lemma lazard_vieta_six_natrE :
  (6%:R : F) = 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_vieta_five_natrE.
exact: (@natrD F 5 1).
Qed.

Lemma lazard_vieta_seven_natrE :
  (7%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_vieta_six_natrE.
exact: (@natrD F 6 1).
Qed.

Lemma lazard_vieta_eight_natrE :
  (8%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_vieta_seven_natrE.
exact: (@natrD F 7 1).
Qed.

Ltac finish_lazard_vieta_ring :=
  repeat first
    [ rewrite lazard_vieta_two_natrE
    | rewrite lazard_vieta_three_natrE
    | rewrite lazard_vieta_four_natrE
    | rewrite lazard_vieta_five_natrE
    | rewrite lazard_vieta_six_natrE
    | rewrite lazard_vieta_seven_natrE
    | rewrite lazard_vieta_eight_natrE
    | rewrite exprSr | rewrite expr0
    | rewrite lazard_vieta_ring_addE | rewrite lazard_vieta_ring_mulE
    | rewrite lazard_vieta_ring_subE | rewrite lazard_vieta_ring_oppE
    | rewrite lazard_vieta_ring_zeroE | rewrite lazard_vieta_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Local Definition lazard_vieta_q1 (a b c d : F) : F :=
  a + b + c + d.

Local Definition lazard_vieta_q2 (a b c d : F) : F :=
  a * b * omega ^+ 4 + a * c * omega ^+ 4 +
  a * d * omega ^+ 4 + b * c * omega ^+ 4 +
  b * d * omega ^+ 4 + c * d * omega ^+ 4 +
  a ^+ 2 * omega ^+ 3 + a * d * omega ^+ 3 +
  b ^+ 2 * omega ^+ 3 + b * c * omega ^+ 3 +
  c ^+ 2 * omega ^+ 3 + d ^+ 2 * omega ^+ 3 +
  a * b * omega ^+ 2 + a * c * omega ^+ 2 +
  a * d * omega ^+ 2 + b * c * omega ^+ 2 +
  b * d * omega ^+ 2 + c * d * omega ^+ 2 +
  a ^+ 2 * omega + 2%:R * (a * b * omega) +
  2%:R * (a * c * omega) - 3%:R * (a * d * omega) +
  b ^+ 2 * omega - 3%:R * (b * c * omega) +
  2%:R * (b * d * omega) + c ^+ 2 * omega +
  2%:R * (c * d * omega) + d ^+ 2 * omega +
  5%:R * (a * d) + 5%:R * (b * c).

Lemma lazard_unscaled_esymm1_certificate a b c d :
  lazard_five_esymm1
      (lazard_inverse_fourier_unscaled a b c d) =
    lazard_vieta_q1 a b c d *
      (1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4).
Proof.
unfold lazard_five_esymm1, lazard_inverse_fourier_unscaled,
  lazard_vieta_q1.
cbn.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_unscaled_esymm2_certificate a b c d :
  lazard_five_esymm2
      (lazard_inverse_fourier_unscaled a b c d) =
    - 5%:R * lazard_fourier_cyclic2 a b c d +
      lazard_vieta_q2 a b c d *
        (1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4).
Proof.
unfold lazard_five_esymm2, lazard_inverse_fourier_unscaled,
  lazard_fourier_cyclic2, lazard_vieta_q2.
cbn.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_unscaled_esymm1 a b c d :
  lazard_five_esymm1
      (lazard_inverse_fourier_unscaled a b c d) = 0.
Proof.
rewrite lazard_unscaled_esymm1_certificate lazard_vieta_cyclotomic.
by rewrite mulr0.
Qed.

Lemma lazard_unscaled_esymm2 a b c d :
  lazard_five_esymm2
      (lazard_inverse_fourier_unscaled a b c d) =
    - 5%:R * lazard_fourier_cyclic2 a b c d.
Proof.
rewrite lazard_unscaled_esymm2_certificate lazard_vieta_cyclotomic.
by rewrite mulr0 addr0.
Qed.

Local Definition lazard_vieta_q3 (a b c d : F) : F :=
  a * b * c * omega ^+ 8 + a * b * d * omega ^+ 8 + a * c * d * omega ^+ 8
  + b * c * d * omega ^+ 8 + a ^+ 2 * b * omega ^+ 7 + a ^+ 2 * d * omega ^+ 7
  + a * c ^+ 2 * omega ^+ 7 + a * d ^+ 2 * omega ^+ 7 + b ^+ 2 * c * omega ^+ 7
  + b ^+ 2 * d * omega ^+ 7 + b * c ^+ 2 * omega ^+ 7 + c * d ^+ 2 * omega ^+ 7
  - a ^+ 2 * b * omega ^+ 6 + 2%:R * (a ^+ 2 * c * omega ^+ 6) + a ^+ 2 * d * omega ^+ 6
  + 2%:R * (a * b ^+ 2 * omega ^+ 6) + a * b * c * omega ^+ 6 + a * b * d * omega ^+ 6
  - a * c ^+ 2 * omega ^+ 6 + a * c * d * omega ^+ 6 + a * d ^+ 2 * omega ^+ 6
  + b ^+ 2 * c * omega ^+ 6 - b ^+ 2 * d * omega ^+ 6 + b * c ^+ 2 * omega ^+ 6
  + b * c * d * omega ^+ 6 + 2%:R * (b * d ^+ 2 * omega ^+ 6)
  + 2%:R * (c ^+ 2 * d * omega ^+ 6) - c * d ^+ 2 * omega ^+ 6 + a ^+ 3 * omega ^+ 5
  + 2%:R * (a ^+ 2 * b * omega ^+ 5) - a ^+ 2 * d * omega ^+ 5
  + 2%:R * (a * b * c * omega ^+ 5) + 2%:R * (a * b * d * omega ^+ 5)
  + 2%:R * (a * c ^+ 2 * omega ^+ 5) + 2%:R * (a * c * d * omega ^+ 5)
  - a * d ^+ 2 * omega ^+ 5 + b ^+ 3 * omega ^+ 5 - b ^+ 2 * c * omega ^+ 5
  + 2%:R * (b ^+ 2 * d * omega ^+ 5) - b * c ^+ 2 * omega ^+ 5
  + 2%:R * (b * c * d * omega ^+ 5) + c ^+ 3 * omega ^+ 5 + 2%:R * (c * d ^+ 2 * omega ^+ 5)
  + d ^+ 3 * omega ^+ 5 + 2%:R * (a ^+ 2 * b * omega ^+ 4) + a ^+ 2 * c * omega ^+ 4
  + 2%:R * (a ^+ 2 * d * omega ^+ 4) + a * b ^+ 2 * omega ^+ 4
  + 3%:R * (a * b * c * omega ^+ 4) + 3%:R * (a * b * d * omega ^+ 4)
  + 2%:R * (a * c ^+ 2 * omega ^+ 4) + 3%:R * (a * c * d * omega ^+ 4)
  + 2%:R * (a * d ^+ 2 * omega ^+ 4) + 2%:R * (b ^+ 2 * c * omega ^+ 4)
  + 2%:R * (b ^+ 2 * d * omega ^+ 4) + 2%:R * (b * c ^+ 2 * omega ^+ 4)
  + 3%:R * (b * c * d * omega ^+ 4) + b * d ^+ 2 * omega ^+ 4 + c ^+ 2 * d * omega ^+ 4
  + 2%:R * (c * d ^+ 2 * omega ^+ 4) + a ^+ 3 * omega ^+ 3 + a ^+ 2 * b * omega ^+ 3
  + a ^+ 2 * c * omega ^+ 3 + 2%:R * (a ^+ 2 * d * omega ^+ 3) + a * b ^+ 2 * omega ^+ 3
  + 2%:R * (a * b * c * omega ^+ 3) + 2%:R * (a * b * d * omega ^+ 3) + a * c ^+ 2 * omega ^+ 3
  + 2%:R * (a * c * d * omega ^+ 3) + 2%:R * (a * d ^+ 2 * omega ^+ 3) + b ^+ 3 * omega ^+ 3
  + 2%:R * (b ^+ 2 * c * omega ^+ 3) + b ^+ 2 * d * omega ^+ 3
  + 2%:R * (b * c ^+ 2 * omega ^+ 3) + 2%:R * (b * c * d * omega ^+ 3)
  + b * d ^+ 2 * omega ^+ 3 + c ^+ 3 * omega ^+ 3 + c ^+ 2 * d * omega ^+ 3
  + c * d ^+ 2 * omega ^+ 3 + d ^+ 3 * omega ^+ 3 + a ^+ 2 * b * omega ^+ 2
  + a ^+ 2 * c * omega ^+ 2 + a ^+ 2 * d * omega ^+ 2 + a * b ^+ 2 * omega ^+ 2
  + 3%:R * (a * b * c * omega ^+ 2) + 3%:R * (a * b * d * omega ^+ 2) + a * c ^+ 2 * omega ^+ 2
  + 3%:R * (a * c * d * omega ^+ 2) + a * d ^+ 2 * omega ^+ 2 + b ^+ 2 * c * omega ^+ 2
  + b ^+ 2 * d * omega ^+ 2 + b * c ^+ 2 * omega ^+ 2 + 3%:R * (b * c * d * omega ^+ 2)
  + b * d ^+ 2 * omega ^+ 2 + c ^+ 2 * d * omega ^+ 2 + c * d ^+ 2 * omega ^+ 2
  + 5%:R * (a ^+ 2 * c * omega) + 5%:R * (a * b ^+ 2 * omega) + 5%:R * (b * d ^+ 2 * omega)
  + 5%:R * (c ^+ 2 * d * omega) - 5%:R * (a ^+ 2 * c) - 5%:R * (a * b ^+ 2)
  - 5%:R * (b * d ^+ 2) - 5%:R * (c ^+ 2 * d).

Lemma lazard_unscaled_esymm3_certificate a b c d :
  lazard_five_esymm3
      (lazard_inverse_fourier_unscaled a b c d) =
    5%:R * lazard_fourier_cyclic3 a b c d +
      lazard_vieta_q3 a b c d *
        (1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4).
Proof.
unfold lazard_five_esymm3, lazard_inverse_fourier_unscaled,
  lazard_fourier_cyclic3, lazard_vieta_q3.
cbn.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_unscaled_esymm3 a b c d :
  lazard_five_esymm3
      (lazard_inverse_fourier_unscaled a b c d) =
    5%:R * lazard_fourier_cyclic3 a b c d.
Proof.
rewrite lazard_unscaled_esymm3_certificate lazard_vieta_cyclotomic.
by rewrite mulr0 addr0.
Qed.

Local Definition lazard_vieta_q4 (a b c d : F) : F :=
  a * b * c * d * omega ^+ 12 + a ^+ 2 * b * d * omega ^+ 11 + a * b * c ^+ 2 * omega ^+ 11
  - a * b * c * d * omega ^+ 11 + a * c * d ^+ 2 * omega ^+ 11 + b ^+ 2 * c * d * omega ^+ 11
  + a ^+ 2 * b * c * omega ^+ 10 - a ^+ 2 * b * d * omega ^+ 10 + a ^+ 2 * c * d * omega ^+ 10
  + a ^+ 2 * d ^+ 2 * omega ^+ 10 + a * b ^+ 2 * c * omega ^+ 10 + a * b ^+ 2 * d * omega ^+ 10
  - a * b * c ^+ 2 * omega ^+ 10 + a * b * d ^+ 2 * omega ^+ 10 + a * c ^+ 2 * d * omega ^+ 10
  - a * c * d ^+ 2 * omega ^+ 10 + b ^+ 2 * c ^+ 2 * omega ^+ 10 - b ^+ 2 * c * d * omega ^+ 10
  + b * c ^+ 2 * d * omega ^+ 10 + b * c * d ^+ 2 * omega ^+ 10 + a ^+ 3 * d * omega ^+ 9
  + a ^+ 2 * b ^+ 2 * omega ^+ 9 + a ^+ 2 * c ^+ 2 * omega ^+ 9 - a ^+ 2 * d ^+ 2 * omega ^+ 9
  + 4%:R * (a * b * c * d * omega ^+ 9) + a * d ^+ 3 * omega ^+ 9 + b ^+ 3 * c * omega ^+ 9
  - b ^+ 2 * c ^+ 2 * omega ^+ 9 + b ^+ 2 * d ^+ 2 * omega ^+ 9 + b * c ^+ 3 * omega ^+ 9
  + c ^+ 2 * d ^+ 2 * omega ^+ 9 + a ^+ 3 * b * omega ^+ 8 + a ^+ 3 * c * omega ^+ 8
  - a ^+ 3 * d * omega ^+ 8 - a ^+ 2 * b ^+ 2 * omega ^+ 8 + a ^+ 2 * b * c * omega ^+ 8
  + 3%:R * (a ^+ 2 * b * d * omega ^+ 8) - a ^+ 2 * c ^+ 2 * omega ^+ 8
  + 2%:R * (a ^+ 2 * c * d * omega ^+ 8) + a ^+ 2 * d ^+ 2 * omega ^+ 8
  + a * b ^+ 3 * omega ^+ 8 + 2%:R * (a * b ^+ 2 * c * omega ^+ 8)
  + a * b ^+ 2 * d * omega ^+ 8 + 3%:R * (a * b * c ^+ 2 * omega ^+ 8)
  + a * b * c * d * omega ^+ 8 + 2%:R * (a * b * d ^+ 2 * omega ^+ 8) + a * c ^+ 3 * omega ^+ 8
  + a * c ^+ 2 * d * omega ^+ 8 + 3%:R * (a * c * d ^+ 2 * omega ^+ 8)
  - a * d ^+ 3 * omega ^+ 8 - b ^+ 3 * c * omega ^+ 8 + b ^+ 3 * d * omega ^+ 8
  + b ^+ 2 * c ^+ 2 * omega ^+ 8 + 3%:R * (b ^+ 2 * c * d * omega ^+ 8)
  - b ^+ 2 * d ^+ 2 * omega ^+ 8 - b * c ^+ 3 * omega ^+ 8
  + 2%:R * (b * c ^+ 2 * d * omega ^+ 8) + b * c * d ^+ 2 * omega ^+ 8
  + b * d ^+ 3 * omega ^+ 8 + c ^+ 3 * d * omega ^+ 8 - c ^+ 2 * d ^+ 2 * omega ^+ 8
  + c * d ^+ 3 * omega ^+ 8 + a ^+ 3 * b * omega ^+ 7 + 2%:R * (a ^+ 3 * d * omega ^+ 7)
  + 2%:R * (a ^+ 2 * b ^+ 2 * omega ^+ 7) + a ^+ 2 * b * c * omega ^+ 7
  + 2%:R * (a ^+ 2 * b * d * omega ^+ 7) + 2%:R * (a ^+ 2 * c ^+ 2 * omega ^+ 7)
  + a ^+ 2 * c * d * omega ^+ 7 + a ^+ 2 * d ^+ 2 * omega ^+ 7 + a * b ^+ 2 * c * omega ^+ 7
  + a * b ^+ 2 * d * omega ^+ 7 + 2%:R * (a * b * c ^+ 2 * omega ^+ 7)
  + 4%:R * (a * b * c * d * omega ^+ 7) + a * b * d ^+ 2 * omega ^+ 7 + a * c ^+ 3 * omega ^+ 7
  + a * c ^+ 2 * d * omega ^+ 7 + 2%:R * (a * c * d ^+ 2 * omega ^+ 7)
  + 2%:R * (a * d ^+ 3 * omega ^+ 7) + 2%:R * (b ^+ 3 * c * omega ^+ 7)
  + b ^+ 3 * d * omega ^+ 7 + b ^+ 2 * c ^+ 2 * omega ^+ 7
  + 2%:R * (b ^+ 2 * c * d * omega ^+ 7) + 2%:R * (b ^+ 2 * d ^+ 2 * omega ^+ 7)
  + 2%:R * (b * c ^+ 3 * omega ^+ 7) + b * c ^+ 2 * d * omega ^+ 7
  + b * c * d ^+ 2 * omega ^+ 7 + 2%:R * (c ^+ 2 * d ^+ 2 * omega ^+ 7)
  + c * d ^+ 3 * omega ^+ 7 + a ^+ 4 * omega ^+ 6 - 2%:R * (a ^+ 3 * b * omega ^+ 6)
  + a ^+ 3 * c * omega ^+ 6 + 2%:R * (a ^+ 2 * b ^+ 2 * omega ^+ 6)
  + 5%:R * (a ^+ 2 * b * c * omega ^+ 6) + 2%:R * (a ^+ 2 * b * d * omega ^+ 6)
  + 2%:R * (a ^+ 2 * c ^+ 2 * omega ^+ 6) + 2%:R * (a ^+ 2 * c * d * omega ^+ 6)
  + 4%:R * (a ^+ 2 * d ^+ 2 * omega ^+ 6) + a * b ^+ 3 * omega ^+ 6
  + 2%:R * (a * b ^+ 2 * c * omega ^+ 6) + 5%:R * (a * b ^+ 2 * d * omega ^+ 6)
  + 2%:R * (a * b * c ^+ 2 * omega ^+ 6) + 3%:R * (a * b * c * d * omega ^+ 6)
  + 2%:R * (a * b * d ^+ 2 * omega ^+ 6) - 2%:R * (a * c ^+ 3 * omega ^+ 6)
  + 5%:R * (a * c ^+ 2 * d * omega ^+ 6) + 2%:R * (a * c * d ^+ 2 * omega ^+ 6)
  + b ^+ 4 * omega ^+ 6 - 2%:R * (b ^+ 3 * d * omega ^+ 6)
  + 4%:R * (b ^+ 2 * c ^+ 2 * omega ^+ 6) + 2%:R * (b ^+ 2 * c * d * omega ^+ 6)
  + 2%:R * (b ^+ 2 * d ^+ 2 * omega ^+ 6) + 2%:R * (b * c ^+ 2 * d * omega ^+ 6)
  + 5%:R * (b * c * d ^+ 2 * omega ^+ 6) + b * d ^+ 3 * omega ^+ 6 + c ^+ 4 * omega ^+ 6
  + c ^+ 3 * d * omega ^+ 6 + 2%:R * (c ^+ 2 * d ^+ 2 * omega ^+ 6)
  - 2%:R * (c * d ^+ 3 * omega ^+ 6) + d ^+ 4 * omega ^+ 6 + 4%:R * (a ^+ 3 * b * omega ^+ 5)
  + 2%:R * (a ^+ 3 * c * omega ^+ 5) + a ^+ 3 * d * omega ^+ 5 + a ^+ 2 * b ^+ 2 * omega ^+ 5
  + 2%:R * (a ^+ 2 * b * c * omega ^+ 5) + 2%:R * (a ^+ 2 * b * d * omega ^+ 5)
  + a ^+ 2 * c ^+ 2 * omega ^+ 5 + 4%:R * (a ^+ 2 * c * d * omega ^+ 5)
  - 3%:R * (a ^+ 2 * d ^+ 2 * omega ^+ 5) + 2%:R * (a * b ^+ 3 * omega ^+ 5)
  + 4%:R * (a * b ^+ 2 * c * omega ^+ 5) + 2%:R * (a * b ^+ 2 * d * omega ^+ 5)
  + 2%:R * (a * b * c ^+ 2 * omega ^+ 5) + 8%:R * (a * b * c * d * omega ^+ 5)
  + 4%:R * (a * b * d ^+ 2 * omega ^+ 5) + 4%:R * (a * c ^+ 3 * omega ^+ 5)
  + 2%:R * (a * c ^+ 2 * d * omega ^+ 5) + 2%:R * (a * c * d ^+ 2 * omega ^+ 5)
  + a * d ^+ 3 * omega ^+ 5 + b ^+ 3 * c * omega ^+ 5 + 4%:R * (b ^+ 3 * d * omega ^+ 5)
  - 3%:R * (b ^+ 2 * c ^+ 2 * omega ^+ 5) + 2%:R * (b ^+ 2 * c * d * omega ^+ 5)
  + b ^+ 2 * d ^+ 2 * omega ^+ 5 + b * c ^+ 3 * omega ^+ 5
  + 4%:R * (b * c ^+ 2 * d * omega ^+ 5) + 2%:R * (b * c * d ^+ 2 * omega ^+ 5)
  + 2%:R * (b * d ^+ 3 * omega ^+ 5) + 2%:R * (c ^+ 3 * d * omega ^+ 5)
  + c ^+ 2 * d ^+ 2 * omega ^+ 5 + 4%:R * (c * d ^+ 3 * omega ^+ 5) + a ^+ 3 * b * omega ^+ 4
  + a ^+ 3 * d * omega ^+ 4 + a ^+ 2 * b ^+ 2 * omega ^+ 4 + a ^+ 2 * b * c * omega ^+ 4
  + 2%:R * (a ^+ 2 * b * d * omega ^+ 4) + a ^+ 2 * c ^+ 2 * omega ^+ 4
  + a ^+ 2 * c * d * omega ^+ 4 + 2%:R * (a ^+ 2 * d ^+ 2 * omega ^+ 4)
  + a * b ^+ 2 * c * omega ^+ 4 + a * b ^+ 2 * d * omega ^+ 4
  + 2%:R * (a * b * c ^+ 2 * omega ^+ 4) + a * b * c * d * omega ^+ 4
  + a * b * d ^+ 2 * omega ^+ 4 + a * c ^+ 3 * omega ^+ 4 + a * c ^+ 2 * d * omega ^+ 4
  + 2%:R * (a * c * d ^+ 2 * omega ^+ 4) + a * d ^+ 3 * omega ^+ 4 + b ^+ 3 * c * omega ^+ 4
  + b ^+ 3 * d * omega ^+ 4 + 2%:R * (b ^+ 2 * c ^+ 2 * omega ^+ 4)
  + 2%:R * (b ^+ 2 * c * d * omega ^+ 4) + b ^+ 2 * d ^+ 2 * omega ^+ 4
  + b * c ^+ 3 * omega ^+ 4 + b * c ^+ 2 * d * omega ^+ 4 + b * c * d ^+ 2 * omega ^+ 4
  + c ^+ 2 * d ^+ 2 * omega ^+ 4 + c * d ^+ 3 * omega ^+ 4 + a ^+ 2 * b * c * omega ^+ 3
  + a ^+ 2 * b * d * omega ^+ 3 + a ^+ 2 * c * d * omega ^+ 3 + a * b ^+ 2 * c * omega ^+ 3
  + a * b ^+ 2 * d * omega ^+ 3 + a * b * c ^+ 2 * omega ^+ 3
  + 4%:R * (a * b * c * d * omega ^+ 3) + a * b * d ^+ 2 * omega ^+ 3
  + a * c ^+ 2 * d * omega ^+ 3 + a * c * d ^+ 2 * omega ^+ 3 + b ^+ 2 * c * d * omega ^+ 3
  + b * c ^+ 2 * d * omega ^+ 3 + b * c * d ^+ 2 * omega ^+ 3 - 5%:R * (a ^+ 3 * b * omega)
  + 5%:R * (a ^+ 2 * d ^+ 2 * omega) - 5%:R * (a * b * c * d * omega)
  - 5%:R * (a * c ^+ 3 * omega) - 5%:R * (b ^+ 3 * d * omega)
  + 5%:R * (b ^+ 2 * c ^+ 2 * omega) - 5%:R * (c * d ^+ 3 * omega) + 5%:R * (a ^+ 3 * b)
  - 5%:R * (a ^+ 2 * d ^+ 2) + 5%:R * (a * b * c * d) + 5%:R * (a * c ^+ 3)
  + 5%:R * (b ^+ 3 * d) - 5%:R * (b ^+ 2 * c ^+ 2) + 5%:R * (c * d ^+ 3).

Lemma lazard_unscaled_esymm4_certificate a b c d :
  lazard_five_esymm4
      (lazard_inverse_fourier_unscaled a b c d) =
    5%:R * lazard_fourier_cyclic4 a b c d +
      lazard_vieta_q4 a b c d *
        (1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4).
Proof.
unfold lazard_five_esymm4, lazard_inverse_fourier_unscaled,
  lazard_fourier_cyclic4, lazard_vieta_q4.
cbn.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_unscaled_esymm4 a b c d :
  lazard_five_esymm4
      (lazard_inverse_fourier_unscaled a b c d) =
    5%:R * lazard_fourier_cyclic4 a b c d.
Proof.
rewrite lazard_unscaled_esymm4_certificate lazard_vieta_cyclotomic.
by rewrite mulr0 addr0.
Qed.

Local Definition lazard_vieta_q5 (a b c d : F) : F :=
  a ^+ 2 * b * c * d * omega ^+ 12 + a * b ^+ 2 * c * d * omega ^+ 12
  + a * b * c ^+ 2 * d * omega ^+ 12 + a * b * c * d ^+ 2 * omega ^+ 12
  + a ^+ 3 * b * d * omega ^+ 11 + a ^+ 2 * b ^+ 2 * d * omega ^+ 11
  + a ^+ 2 * b * c ^+ 2 * omega ^+ 11 + a ^+ 2 * b * d ^+ 2 * omega ^+ 11
  + a ^+ 2 * c * d ^+ 2 * omega ^+ 11 + a * b ^+ 2 * c ^+ 2 * omega ^+ 11
  + a * b * c ^+ 3 * omega ^+ 11 + a * c ^+ 2 * d ^+ 2 * omega ^+ 11
  + a * c * d ^+ 3 * omega ^+ 11 + b ^+ 3 * c * d * omega ^+ 11
  + b ^+ 2 * c ^+ 2 * d * omega ^+ 11 + b ^+ 2 * c * d ^+ 2 * omega ^+ 11
  + a ^+ 3 * b * c * omega ^+ 10 - a ^+ 3 * b * d * omega ^+ 10 + a ^+ 3 * c * d * omega ^+ 10
  + a ^+ 3 * d ^+ 2 * omega ^+ 10 + 2%:R * (a ^+ 2 * b ^+ 2 * c * omega ^+ 10)
  + a ^+ 2 * b * c * d * omega ^+ 10 + a ^+ 2 * b * d ^+ 2 * omega ^+ 10
  + 2%:R * (a ^+ 2 * c ^+ 2 * d * omega ^+ 10) + a ^+ 2 * c * d ^+ 2 * omega ^+ 10
  + a ^+ 2 * d ^+ 3 * omega ^+ 10 + a * b ^+ 3 * c * omega ^+ 10 + a * b ^+ 3 * d * omega ^+ 10
  + a * b ^+ 2 * c ^+ 2 * omega ^+ 10 + a * b ^+ 2 * c * d * omega ^+ 10
  + 2%:R * (a * b ^+ 2 * d ^+ 2 * omega ^+ 10) - a * b * c ^+ 3 * omega ^+ 10
  + a * b * c ^+ 2 * d * omega ^+ 10 + a * b * c * d ^+ 2 * omega ^+ 10
  + a * b * d ^+ 3 * omega ^+ 10 + a * c ^+ 3 * d * omega ^+ 10 - a * c * d ^+ 3 * omega ^+ 10
  + b ^+ 3 * c ^+ 2 * omega ^+ 10 - b ^+ 3 * c * d * omega ^+ 10
  + b ^+ 2 * c ^+ 3 * omega ^+ 10 + b ^+ 2 * c ^+ 2 * d * omega ^+ 10
  + b * c ^+ 3 * d * omega ^+ 10 + 2%:R * (b * c ^+ 2 * d ^+ 2 * omega ^+ 10)
  + b * c * d ^+ 3 * omega ^+ 10 + a ^+ 4 * d * omega ^+ 9 + a ^+ 3 * b ^+ 2 * omega ^+ 9
  + a ^+ 3 * b * d * omega ^+ 9 + a ^+ 3 * c ^+ 2 * omega ^+ 9 + a ^+ 3 * c * d * omega ^+ 9
  + a ^+ 2 * b ^+ 3 * omega ^+ 9 + a ^+ 2 * b ^+ 2 * c * omega ^+ 9
  + a ^+ 2 * b ^+ 2 * d * omega ^+ 9 + a ^+ 2 * b * c ^+ 2 * omega ^+ 9
  + 4%:R * (a ^+ 2 * b * c * d * omega ^+ 9) - a ^+ 2 * b * d ^+ 2 * omega ^+ 9
  + a ^+ 2 * c ^+ 3 * omega ^+ 9 + a ^+ 2 * c ^+ 2 * d * omega ^+ 9
  - a ^+ 2 * c * d ^+ 2 * omega ^+ 9 + a * b ^+ 3 * c * omega ^+ 9
  - a * b ^+ 2 * c ^+ 2 * omega ^+ 9 + 4%:R * (a * b ^+ 2 * c * d * omega ^+ 9)
  + a * b ^+ 2 * d ^+ 2 * omega ^+ 9 + a * b * c ^+ 3 * omega ^+ 9
  + 4%:R * (a * b * c ^+ 2 * d * omega ^+ 9) + 4%:R * (a * b * c * d ^+ 2 * omega ^+ 9)
  + a * b * d ^+ 3 * omega ^+ 9 + a * c ^+ 2 * d ^+ 2 * omega ^+ 9
  + a * c * d ^+ 3 * omega ^+ 9 + a * d ^+ 4 * omega ^+ 9 + b ^+ 4 * c * omega ^+ 9
  + b ^+ 3 * c * d * omega ^+ 9 + b ^+ 3 * d ^+ 2 * omega ^+ 9
  - b ^+ 2 * c ^+ 2 * d * omega ^+ 9 + b ^+ 2 * c * d ^+ 2 * omega ^+ 9
  + b ^+ 2 * d ^+ 3 * omega ^+ 9 + b * c ^+ 4 * omega ^+ 9 + b * c ^+ 3 * d * omega ^+ 9
  + b * c ^+ 2 * d ^+ 2 * omega ^+ 9 + c ^+ 3 * d ^+ 2 * omega ^+ 9
  + c ^+ 2 * d ^+ 3 * omega ^+ 9 + a ^+ 4 * b * omega ^+ 8 + a ^+ 4 * c * omega ^+ 8
  - a ^+ 4 * d * omega ^+ 8 + 2%:R * (a ^+ 3 * b * c * omega ^+ 8)
  + 2%:R * (a ^+ 3 * b * d * omega ^+ 8) + a ^+ 3 * c * d * omega ^+ 8
  + a ^+ 2 * b ^+ 2 * d * omega ^+ 8 + a ^+ 2 * b * c ^+ 2 * omega ^+ 8
  + 4%:R * (a ^+ 2 * b * d ^+ 2 * omega ^+ 8) + 4%:R * (a ^+ 2 * c * d ^+ 2 * omega ^+ 8)
  + a * b ^+ 4 * omega ^+ 8 + a * b ^+ 3 * c * omega ^+ 8
  + 2%:R * (a * b ^+ 3 * d * omega ^+ 8) + 4%:R * (a * b ^+ 2 * c ^+ 2 * omega ^+ 8)
  + 2%:R * (a * b * c ^+ 3 * omega ^+ 8) + a * b * d ^+ 3 * omega ^+ 8
  + a * c ^+ 4 * omega ^+ 8 + 2%:R * (a * c ^+ 3 * d * omega ^+ 8)
  + a * c ^+ 2 * d ^+ 2 * omega ^+ 8 + 2%:R * (a * c * d ^+ 3 * omega ^+ 8)
  - a * d ^+ 4 * omega ^+ 8 - b ^+ 4 * c * omega ^+ 8 + b ^+ 4 * d * omega ^+ 8
  + 2%:R * (b ^+ 3 * c * d * omega ^+ 8) + 4%:R * (b ^+ 2 * c ^+ 2 * d * omega ^+ 8)
  + b ^+ 2 * c * d ^+ 2 * omega ^+ 8 - b * c ^+ 4 * omega ^+ 8 + b * c ^+ 3 * d * omega ^+ 8
  + 2%:R * (b * c * d ^+ 3 * omega ^+ 8) + b * d ^+ 4 * omega ^+ 8 + c ^+ 4 * d * omega ^+ 8
  + c * d ^+ 4 * omega ^+ 8 + a ^+ 4 * d * omega ^+ 7 + a ^+ 3 * b ^+ 2 * omega ^+ 7
  + a ^+ 3 * b * d * omega ^+ 7 + a ^+ 3 * c ^+ 2 * omega ^+ 7 + a ^+ 3 * c * d * omega ^+ 7
  + a ^+ 2 * b ^+ 3 * omega ^+ 7 + a ^+ 2 * b ^+ 2 * c * omega ^+ 7
  + a ^+ 2 * b ^+ 2 * d * omega ^+ 7 + a ^+ 2 * b * c ^+ 2 * omega ^+ 7
  + 4%:R * (a ^+ 2 * b * c * d * omega ^+ 7) - a ^+ 2 * b * d ^+ 2 * omega ^+ 7
  + a ^+ 2 * c ^+ 3 * omega ^+ 7 + a ^+ 2 * c ^+ 2 * d * omega ^+ 7
  - a ^+ 2 * c * d ^+ 2 * omega ^+ 7 + a * b ^+ 3 * c * omega ^+ 7
  - a * b ^+ 2 * c ^+ 2 * omega ^+ 7 + 4%:R * (a * b ^+ 2 * c * d * omega ^+ 7)
  + a * b ^+ 2 * d ^+ 2 * omega ^+ 7 + a * b * c ^+ 3 * omega ^+ 7
  + 4%:R * (a * b * c ^+ 2 * d * omega ^+ 7) + 4%:R * (a * b * c * d ^+ 2 * omega ^+ 7)
  + a * b * d ^+ 3 * omega ^+ 7 + a * c ^+ 2 * d ^+ 2 * omega ^+ 7
  + a * c * d ^+ 3 * omega ^+ 7 + a * d ^+ 4 * omega ^+ 7 + b ^+ 4 * c * omega ^+ 7
  + b ^+ 3 * c * d * omega ^+ 7 + b ^+ 3 * d ^+ 2 * omega ^+ 7
  - b ^+ 2 * c ^+ 2 * d * omega ^+ 7 + b ^+ 2 * c * d ^+ 2 * omega ^+ 7
  + b ^+ 2 * d ^+ 3 * omega ^+ 7 + b * c ^+ 4 * omega ^+ 7 + b * c ^+ 3 * d * omega ^+ 7
  + b * c ^+ 2 * d ^+ 2 * omega ^+ 7 + c ^+ 3 * d ^+ 2 * omega ^+ 7
  + c ^+ 2 * d ^+ 3 * omega ^+ 7 + a ^+ 5 * omega ^+ 6 + a ^+ 3 * b * c * omega ^+ 6
  - a ^+ 3 * b * d * omega ^+ 6 - 4%:R * (a ^+ 3 * c * d * omega ^+ 6)
  + a ^+ 3 * d ^+ 2 * omega ^+ 6 + 2%:R * (a ^+ 2 * b ^+ 2 * c * omega ^+ 6)
  + 5%:R * (a ^+ 2 * b ^+ 2 * d * omega ^+ 6) + 5%:R * (a ^+ 2 * b * c ^+ 2 * omega ^+ 6)
  + a ^+ 2 * b * c * d * omega ^+ 6 + a ^+ 2 * b * d ^+ 2 * omega ^+ 6
  + 2%:R * (a ^+ 2 * c ^+ 2 * d * omega ^+ 6) + a ^+ 2 * c * d ^+ 2 * omega ^+ 6
  + a ^+ 2 * d ^+ 3 * omega ^+ 6 - 4%:R * (a * b ^+ 3 * c * omega ^+ 6)
  + a * b ^+ 3 * d * omega ^+ 6 + a * b ^+ 2 * c ^+ 2 * omega ^+ 6
  + a * b ^+ 2 * c * d * omega ^+ 6 + 2%:R * (a * b ^+ 2 * d ^+ 2 * omega ^+ 6)
  - a * b * c ^+ 3 * omega ^+ 6 + a * b * c ^+ 2 * d * omega ^+ 6
  + a * b * c * d ^+ 2 * omega ^+ 6 - 4%:R * (a * b * d ^+ 3 * omega ^+ 6)
  + a * c ^+ 3 * d * omega ^+ 6 + 5%:R * (a * c ^+ 2 * d ^+ 2 * omega ^+ 6)
  - a * c * d ^+ 3 * omega ^+ 6 + b ^+ 5 * omega ^+ 6 + b ^+ 3 * c ^+ 2 * omega ^+ 6
  - b ^+ 3 * c * d * omega ^+ 6 + b ^+ 2 * c ^+ 3 * omega ^+ 6
  + b ^+ 2 * c ^+ 2 * d * omega ^+ 6 + 5%:R * (b ^+ 2 * c * d ^+ 2 * omega ^+ 6)
  - 4%:R * (b * c ^+ 3 * d * omega ^+ 6) + 2%:R * (b * c ^+ 2 * d ^+ 2 * omega ^+ 6)
  + b * c * d ^+ 3 * omega ^+ 6 + c ^+ 5 * omega ^+ 6 + d ^+ 5 * omega ^+ 6
  - a ^+ 5 * omega ^+ 5 + a ^+ 3 * b * d * omega ^+ 5 + 5%:R * (a ^+ 3 * c * d * omega ^+ 5)
  - 4%:R * (a ^+ 2 * b ^+ 2 * d * omega ^+ 5) - 4%:R * (a ^+ 2 * b * c ^+ 2 * omega ^+ 5)
  + a ^+ 2 * b * d ^+ 2 * omega ^+ 5 + a ^+ 2 * c * d ^+ 2 * omega ^+ 5
  + 5%:R * (a * b ^+ 3 * c * omega ^+ 5) + a * b ^+ 2 * c ^+ 2 * omega ^+ 5
  + a * b * c ^+ 3 * omega ^+ 5 + 5%:R * (a * b * d ^+ 3 * omega ^+ 5)
  - 4%:R * (a * c ^+ 2 * d ^+ 2 * omega ^+ 5) + a * c * d ^+ 3 * omega ^+ 5
  - b ^+ 5 * omega ^+ 5 + b ^+ 3 * c * d * omega ^+ 5 + b ^+ 2 * c ^+ 2 * d * omega ^+ 5
  - 4%:R * (b ^+ 2 * c * d ^+ 2 * omega ^+ 5) + 5%:R * (b * c ^+ 3 * d * omega ^+ 5)
  - c ^+ 5 * omega ^+ 5 - d ^+ 5 * omega ^+ 5 + a ^+ 2 * b * c * d * omega ^+ 4
  + a * b ^+ 2 * c * d * omega ^+ 4 + a * b * c ^+ 2 * d * omega ^+ 4
  + a * b * c * d ^+ 2 * omega ^+ 4 + a ^+ 5 * omega - 5%:R * (a ^+ 3 * c * d * omega)
  + 5%:R * (a ^+ 2 * b ^+ 2 * d * omega) + 5%:R * (a ^+ 2 * b * c ^+ 2 * omega)
  - 5%:R * (a * b ^+ 3 * c * omega) - 5%:R * (a * b * d ^+ 3 * omega)
  + 5%:R * (a * c ^+ 2 * d ^+ 2 * omega) + b ^+ 5 * omega
  + 5%:R * (b ^+ 2 * c * d ^+ 2 * omega) - 5%:R * (b * c ^+ 3 * d * omega) + c ^+ 5 * omega
  + d ^+ 5 * omega - a ^+ 5 + 5%:R * (a ^+ 3 * c * d) - 5%:R * (a ^+ 2 * b ^+ 2 * d)
  - 5%:R * (a ^+ 2 * b * c ^+ 2) + 5%:R * (a * b ^+ 3 * c) + 5%:R * (a * b * d ^+ 3)
  - 5%:R * (a * c ^+ 2 * d ^+ 2) - b ^+ 5 - 5%:R * (b ^+ 2 * c * d ^+ 2)
  + 5%:R * (b * c ^+ 3 * d) - c ^+ 5 - d ^+ 5.

Lemma lazard_unscaled_esymm5_certificate a b c d :
  lazard_five_esymm5
      (lazard_inverse_fourier_unscaled a b c d) =
    lazard_fourier_cyclic5 a b c d +
      lazard_vieta_q5 a b c d *
        (1 + omega + omega ^+ 2 + omega ^+ 3 + omega ^+ 4).
Proof.
unfold lazard_five_esymm5, lazard_inverse_fourier_unscaled,
  lazard_fourier_cyclic5, lazard_vieta_q5.
cbn.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_unscaled_esymm5 a b c d :
  lazard_five_esymm5
      (lazard_inverse_fourier_unscaled a b c d) =
    lazard_fourier_cyclic5 a b c d.
Proof.
rewrite lazard_unscaled_esymm5_certificate lazard_vieta_cyclotomic.
by rewrite mulr0 addr0.
Qed.

(** Scaling all five unscaled values by [5^-1] scales the degree-[i]
    elementary symmetric expression by [(5^-1)^i]. *)
Lemma lazard_inverse_fourier_esymm1_scale a b c d :
  lazard_five_esymm1 (lazard_inverse_fourier_output a b c d) =
    (5%:R)^-1 * lazard_five_esymm1
      (lazard_inverse_fourier_unscaled a b c d).
Proof.
unfold lazard_five_esymm1, lazard_inverse_fourier_output.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_inverse_fourier_esymm2_scale a b c d :
  lazard_five_esymm2 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 2 * lazard_five_esymm2
      (lazard_inverse_fourier_unscaled a b c d).
Proof.
unfold lazard_five_esymm2, lazard_inverse_fourier_output.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_inverse_fourier_esymm3_scale a b c d :
  lazard_five_esymm3 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 3 * lazard_five_esymm3
      (lazard_inverse_fourier_unscaled a b c d).
Proof.
unfold lazard_five_esymm3, lazard_inverse_fourier_output.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_inverse_fourier_esymm4_scale a b c d :
  lazard_five_esymm4 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 4 * lazard_five_esymm4
      (lazard_inverse_fourier_unscaled a b c d).
Proof.
unfold lazard_five_esymm4, lazard_inverse_fourier_output.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_inverse_fourier_esymm5_scale a b c d :
  lazard_five_esymm5 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 5 * lazard_five_esymm5
      (lazard_inverse_fourier_unscaled a b c d).
Proof.
unfold lazard_five_esymm5, lazard_inverse_fourier_output.
finish_lazard_vieta_ring.
Qed.

Lemma lazard_inv_five_power_succ_cancel n :
  ((5%:R : F)^-1) ^+ n.+1 * 5%:R =
    ((5%:R : F)^-1) ^+ n.
Proof.
by rewrite exprSr -mulrA (mulVf five_neq0) mulr1.
Qed.

Lemma lazard_inv_five_power_cancel n :
  ((5%:R : F)^-1) ^+ n * (5%:R : F) ^+ n = 1.
Proof.
rewrite -(exprMn n (5%:R : F)^-1 (5%:R : F)).
by rewrite (mulVf five_neq0) expr1n.
Qed.

(** The five Vieta identities before substituting the coefficient
    relations.  These are the exact Coq counterparts of the Lean
    [inverseFourier_esymm1]--[inverseFourier_esymm5] results. *)
Theorem lazard_inverse_fourier_esymm1 a b c d :
  lazard_five_esymm1 (lazard_inverse_fourier_output a b c d) = 0.
Proof.
rewrite lazard_inverse_fourier_esymm1_scale lazard_unscaled_esymm1.
by rewrite mulr0.
Qed.

Theorem lazard_inverse_fourier_esymm2 a b c d :
  lazard_five_esymm2 (lazard_inverse_fourier_output a b c d) =
    - (5%:R)^-1 * lazard_fourier_cyclic2 a b c d.
Proof.
rewrite lazard_inverse_fourier_esymm2_scale lazard_unscaled_esymm2.
rewrite mulrA mulrN lazard_inv_five_power_succ_cancel expr1.
reflexivity.
Qed.

Theorem lazard_inverse_fourier_esymm3 a b c d :
  lazard_five_esymm3 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 2 * lazard_fourier_cyclic3 a b c d.
Proof.
rewrite lazard_inverse_fourier_esymm3_scale lazard_unscaled_esymm3.
by rewrite mulrA lazard_inv_five_power_succ_cancel.
Qed.

Theorem lazard_inverse_fourier_esymm4 a b c d :
  lazard_five_esymm4 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 3 * lazard_fourier_cyclic4 a b c d.
Proof.
rewrite lazard_inverse_fourier_esymm4_scale lazard_unscaled_esymm4.
by rewrite mulrA lazard_inv_five_power_succ_cancel.
Qed.

Theorem lazard_inverse_fourier_esymm5 a b c d :
  lazard_five_esymm5 (lazard_inverse_fourier_output a b c d) =
    ((5%:R)^-1) ^+ 5 * lazard_fourier_cyclic5 a b c d.
Proof.
by rewrite lazard_inverse_fourier_esymm5_scale lazard_unscaled_esymm5.
Qed.

(** Lazard's four coefficient relations.  Writing the integer scales as
    powers of five makes the cancellations with Fourier normalization
    transparent and avoids any characteristic-zero assumption beyond the
    explicitly stated [5 != 0]. *)
Record lazard_fourier_relations
    (p q r s a b c d : F) : Prop := LazardFourierRelations {
  lazard_relation_cyclic2 :
    lazard_fourier_cyclic2 a b c d = - (5%:R) ^+ 1 * p;
  lazard_relation_cyclic3 :
    lazard_fourier_cyclic3 a b c d = - ((5%:R) ^+ 2 * q);
  lazard_relation_cyclic4 :
    lazard_fourier_cyclic4 a b c d = (5%:R) ^+ 3 * r;
  lazard_relation_cyclic5 :
    lazard_fourier_cyclic5 a b c d = - ((5%:R) ^+ 5 * s)
}.

Record lazard_depressed_five_root_relations
    (p q r s : F) (x : 'I_5 -> F) : Prop :=
    LazardDepressedFiveRootRelations {
  lazard_vieta_sum : lazard_five_esymm1 x = 0;
  lazard_vieta_pairs : lazard_five_esymm2 x = p;
  lazard_vieta_triples : lazard_five_esymm3 x = - q;
  lazard_vieta_quadruples : lazard_five_esymm4 x = r;
  lazard_vieta_product : lazard_five_esymm5 x = - s
}.

Lemma lazard_inv_five_cancel_monomial n x :
  ((5%:R : F)^-1) ^+ n * ((5%:R : F) ^+ n * x) = x.
Proof.
by rewrite mulrA lazard_inv_five_power_cancel mul1r.
Qed.

Theorem lazard_fourier_relations_vieta p q r s a b c d
    (h : lazard_fourier_relations p q r s a b c d) :
  lazard_depressed_five_root_relations p q r s
    (lazard_inverse_fourier_output a b c d).
Proof.
constructor.
- exact: lazard_inverse_fourier_esymm1.
- rewrite lazard_inverse_fourier_esymm2
    (lazard_relation_cyclic2 h).
  rewrite expr1.
  have hid :
      - (5%:R)^-1 * (- (5%:R) * p) =
        (5%:R)^-1 * (5%:R * p).
    finish_lazard_vieta_ring.
  rewrite hid.
  exact: lazard_inv_five_cancel_monomial 1 p.
- rewrite lazard_inverse_fourier_esymm3
    (lazard_relation_cyclic3 h) mulrN.
  by rewrite lazard_inv_five_cancel_monomial.
- rewrite lazard_inverse_fourier_esymm4
    (lazard_relation_cyclic4 h).
  by rewrite lazard_inv_five_cancel_monomial.
- rewrite lazard_inverse_fourier_esymm5
    (lazard_relation_cyclic5 h) mulrN.
  by rewrite lazard_inv_five_cancel_monomial.

Qed.

Definition lazard_depressed_quintic_eval
    (p q r s x : F) : F :=
  x ^+ 5 + p * x ^+ 3 + q * x ^+ 2 + r * x + s.

(** The polynomial whose scalar evaluation is
    [lazard_depressed_quintic_eval]. *)
Definition lazard_depressed_quintic_polynomial
    (p q r s : F) : {poly F} :=
  'X^5 + p%:P * 'X^3 + q%:P * 'X^2 + r%:P * 'X + s%:P.

Lemma lazard_depressed_quintic_polynomial_horner p q r s x :
  (lazard_depressed_quintic_polynomial p q r s).[x] =
    lazard_depressed_quintic_eval p q r s x.
Proof.
rewrite /lazard_depressed_quintic_polynomial
  /lazard_depressed_quintic_eval !hornerE.
finish_lazard_vieta_ring.
Qed.

(** Expand an ordinal-indexed product over exactly five coordinates. *)
Lemma lazard_five_index_poly_productE (xv : 'I_5 -> F) :
  \prod_(k : 'I_5) ('X - (xv k)%:P) =
    ('X - (xv o0)%:P) * ('X - (xv o1)%:P) *
    ('X - (xv o2)%:P) * ('X - (xv o3)%:P) *
    ('X - (xv o4)%:P).
Proof.
rewrite !big_ord_recl !big_ord0.
have h0 : (@ord0 4) = o0 by apply: val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = o1 by apply: val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = o2
  by apply: val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = o3
  by apply: val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2)
      (lift (@ord0 1) (@ord0 0)))) = o4 by apply: val_inj.
by rewrite h4 h3 h2 h1 h0 mulr1 !mulrA.
Qed.

(** A local bridge from MathComp's packed polynomial operations to the
    standard [ring] tactic. *)
Local Definition lazard_vieta_poly_ring_carrier : Type := {poly F}.
Local Definition lazard_vieta_poly_ring_zero :
  lazard_vieta_poly_ring_carrier := 0.
Local Definition lazard_vieta_poly_ring_one :
  lazard_vieta_poly_ring_carrier := 1.
Local Definition lazard_vieta_poly_ring_add :
    lazard_vieta_poly_ring_carrier -> lazard_vieta_poly_ring_carrier ->
      lazard_vieta_poly_ring_carrier := @GRing.add {poly F}.
Local Definition lazard_vieta_poly_ring_mul :
    lazard_vieta_poly_ring_carrier -> lazard_vieta_poly_ring_carrier ->
      lazard_vieta_poly_ring_carrier := @GRing.mul {poly F}.
Local Definition lazard_vieta_poly_ring_sub :
    lazard_vieta_poly_ring_carrier -> lazard_vieta_poly_ring_carrier ->
      lazard_vieta_poly_ring_carrier := fun p0 q0 => p0 - q0.
Local Definition lazard_vieta_poly_ring_opp :
    lazard_vieta_poly_ring_carrier -> lazard_vieta_poly_ring_carrier :=
  @GRing.opp {poly F}.
Local Definition lazard_vieta_poly_ring_eq :
    lazard_vieta_poly_ring_carrier -> lazard_vieta_poly_ring_carrier -> Prop :=
  @eq lazard_vieta_poly_ring_carrier.

Lemma lazard_vieta_poly_ring_addE p0 q0 :
  p0 + q0 = lazard_vieta_poly_ring_add p0 q0.
Proof. reflexivity. Qed.
Lemma lazard_vieta_poly_ring_mulE p0 q0 :
  p0 * q0 = lazard_vieta_poly_ring_mul p0 q0.
Proof. reflexivity. Qed.
Lemma lazard_vieta_poly_ring_subE p0 q0 :
  p0 - q0 = lazard_vieta_poly_ring_sub p0 q0.
Proof. reflexivity. Qed.
Lemma lazard_vieta_poly_ring_oppE p0 :
  - p0 = lazard_vieta_poly_ring_opp p0.
Proof. reflexivity. Qed.
Lemma lazard_vieta_poly_ring_zeroE :
  (0 : {poly F}) = lazard_vieta_poly_ring_zero.
Proof. reflexivity. Qed.
Lemma lazard_vieta_poly_ring_oneE :
  (1 : {poly F}) = lazard_vieta_poly_ring_one.
Proof. reflexivity. Qed.

Lemma lazard_vieta_poly_ring_theory :
  @ring_theory lazard_vieta_poly_ring_carrier
    lazard_vieta_poly_ring_zero lazard_vieta_poly_ring_one
    lazard_vieta_poly_ring_add lazard_vieta_poly_ring_mul
    lazard_vieta_poly_ring_sub lazard_vieta_poly_ring_opp
    lazard_vieta_poly_ring_eq.
Proof.
constructor; unfold lazard_vieta_poly_ring_carrier,
  lazard_vieta_poly_ring_zero, lazard_vieta_poly_ring_one,
  lazard_vieta_poly_ring_add, lazard_vieta_poly_ring_mul,
  lazard_vieta_poly_ring_sub, lazard_vieta_poly_ring_opp,
  lazard_vieta_poly_ring_eq; intros.
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

Add Ring lazard_vieta_polynomial_ring : lazard_vieta_poly_ring_theory.
Opaque lazard_vieta_poly_ring_zero lazard_vieta_poly_ring_one
  lazard_vieta_poly_ring_add lazard_vieta_poly_ring_mul
  lazard_vieta_poly_ring_sub lazard_vieta_poly_ring_opp
  lazard_vieta_poly_ring_eq.

Ltac finish_lazard_vieta_polynomial_ring :=
  repeat first
    [ rewrite polyC_exp | rewrite polyCB | rewrite polyCN
    | rewrite polyCM | rewrite polyCD | rewrite polyC_natr
    | rewrite exprSr | rewrite expr0 ];
  repeat first
    [ rewrite lazard_vieta_poly_ring_addE
    | rewrite lazard_vieta_poly_ring_mulE
    | rewrite lazard_vieta_poly_ring_subE
    | rewrite lazard_vieta_poly_ring_oppE
    | rewrite lazard_vieta_poly_ring_zeroE
    | rewrite lazard_vieta_poly_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (lazard_vieta_poly_ring_eq lhs rhs)
  end;
  ring.

(** Expand five abstract linear factors entirely inside the polynomial ring.
    Keeping this lemma separate from the coefficient embedding avoids asking
    the ring normalizer to unfold [polyC] while it is also expanding the
    product. *)
Lemma lazard_five_factor_polynomial_identity
    (XX A B C D E : {poly F}) :
  XX ^+ 5 +
      (A * B + A * C + A * D + A * E + B * C + B * D + B * E +
        C * D + C * E + D * E) * XX ^+ 3 +
      (- (A * B * C + A * B * D + A * B * E + A * C * D + A * C * E +
        A * D * E + B * C * D + B * C * E + B * D * E + C * D * E)) *
        XX ^+ 2 +
      (A * B * C * D + A * B * C * E + A * B * D * E +
        A * C * D * E + B * C * D * E) * XX +
      (- (A * B * C * D * E)) =
    (XX - A) * (XX - B) * (XX - C) * (XX - D) * (XX - E) +
      XX ^+ 4 * (A + B + C + D + E).
Proof.
finish_lazard_vieta_polynomial_ring.
Qed.

(** Exact polynomial equality, including repeated factors, for every tuple
    satisfying the depressed Vieta package. *)
Theorem lazard_depressed_vieta_polynomial_factorization
    (p q r s : F) (xv : 'I_5 -> F)
    (h : lazard_depressed_five_root_relations p q r s xv) :
  lazard_depressed_quintic_polynomial p q r s =
    \prod_(k : 'I_5) ('X - (xv k)%:P).
Proof.
have hq : q = - lazard_five_esymm3 xv.
  rewrite (lazard_vieta_triples h).
  by rewrite opprK.
have hs : s = - lazard_five_esymm5 xv.
  rewrite (lazard_vieta_product h).
  by rewrite opprK.
rewrite lazard_five_index_poly_productE
  /lazard_depressed_quintic_polynomial
  -(lazard_vieta_pairs h) hq -(lazard_vieta_quadruples h) hs.
have hid :
    'X^5 + (lazard_five_esymm2 xv)%:P * 'X^3 +
        (- lazard_five_esymm3 xv)%:P * 'X^2 +
        (lazard_five_esymm4 xv)%:P * 'X +
        (- lazard_five_esymm5 xv)%:P =
      ('X - (xv o0)%:P) * ('X - (xv o1)%:P) *
        ('X - (xv o2)%:P) * ('X - (xv o3)%:P) *
        ('X - (xv o4)%:P) +
      'X^4 * (lazard_five_esymm1 xv)%:P.
  unfold lazard_five_esymm1, lazard_five_esymm2,
    lazard_five_esymm3, lazard_five_esymm4, lazard_five_esymm5.
  rewrite !polyCN !polyCD !polyCM.
  exact: lazard_five_factor_polynomial_identity.
rewrite hid (lazard_vieta_sum h).
by rewrite polyC0 mulr0 addr0.
Qed.

Theorem lazard_depressed_vieta_eval_factorization
    (p q r s : F) (xv : 'I_5 -> F)
    (h : lazard_depressed_five_root_relations p q r s xv) (x : F) :
  lazard_depressed_quintic_eval p q r s x =
    (x - xv o0) * (x - xv o1) * (x - xv o2) *
      (x - xv o3) * (x - xv o4).
Proof.
have hq : q = - lazard_five_esymm3 xv.
  rewrite (lazard_vieta_triples h).
  by rewrite opprK.
have hs : s = - lazard_five_esymm5 xv.
  rewrite (lazard_vieta_product h).
  by rewrite opprK.
rewrite /lazard_depressed_quintic_eval
  -(lazard_vieta_pairs h) hq -(lazard_vieta_quadruples h) hs.
have hid :
    x ^+ 5 + lazard_five_esymm2 xv * x ^+ 3 +
        (- lazard_five_esymm3 xv) * x ^+ 2 +
        lazard_five_esymm4 xv * x - lazard_five_esymm5 xv =
      (x - xv o0) * (x - xv o1) * (x - xv o2) *
          (x - xv o3) * (x - xv o4) +
        x ^+ 4 * lazard_five_esymm1 xv.
  unfold lazard_five_esymm1, lazard_five_esymm2,
    lazard_five_esymm3, lazard_five_esymm4, lazard_five_esymm5.
  finish_lazard_vieta_ring.
rewrite hid (lazard_vieta_sum h).
by rewrite mulr0 addr0.
Qed.

(** Every entry of an exact depressed Vieta tuple is a root. *)
Theorem lazard_depressed_vieta_root
    (p q r s : F) (xv : 'I_5 -> F)
    (h : lazard_depressed_five_root_relations p q r s xv) (k : 'I_5) :
  lazard_depressed_quintic_eval p q r s (xv k) = 0.
Proof.
rewrite (lazard_depressed_vieta_eval_factorization h).
case: k=> [[|[|[|[|[|k]]]]] hk].
- have -> : @Ordinal 5 0 hk = o0 by apply: val_inj.
  rewrite subrr.
  finish_lazard_vieta_ring.
- have -> : @Ordinal 5 1 hk = o1 by apply: val_inj.
  rewrite subrr.
  finish_lazard_vieta_ring.
- have -> : @Ordinal 5 2 hk = o2 by apply: val_inj.
  rewrite subrr.
  finish_lazard_vieta_ring.
- have -> : @Ordinal 5 3 hk = o3 by apply: val_inj.
  rewrite subrr.
  finish_lazard_vieta_ring.
- have -> : @Ordinal 5 4 hk = o4 by apply: val_inj.
  rewrite subrr.
  finish_lazard_vieta_ring.
- by move: hk.
Qed.

(** Exact depressed Vieta data exhausts the root set.  This is the reusable
    support-level consequence of the stronger five-factor identity. *)
Theorem lazard_depressed_vieta_complete
    (p q r s : F) (xv : 'I_5 -> F)
    (h : lazard_depressed_five_root_relations p q r s xv) (x : F)
    (hx : lazard_depressed_quintic_eval p q r s x = 0) :
  exists k : 'I_5, x = xv k.
Proof.
rewrite (lazard_depressed_vieta_eval_factorization h) in hx.
have hproductb :
    (x - xv o0) * (x - xv o1) * (x - xv o2) *
      (x - xv o3) * (x - xv o4) == 0.
  apply/eqP.
  exact: hx.
move: hproductb.
rewrite !mulf_eq0 !subr_eq0.
move/orP=> [h0123 | /eqP h4].
- move/orP: h0123=> [h012 | /eqP h3].
  + move/orP: h012=> [h01 | /eqP h2].
    * move/orP: h01=> [/eqP h0 | /eqP h1].
      -- by exists o0.
      -- by exists o1.
    * by exists o2.
  + by exists o3.
- by exists o4.
Qed.

(** Root-set form of an exact depressed Vieta certificate. *)
Theorem lazard_depressed_vieta_root_iff
    (p q r s : F) (xv : 'I_5 -> F)
    (h : lazard_depressed_five_root_relations p q r s xv) (x : F) :
  lazard_depressed_quintic_eval p q r s x = 0 <->
    exists k : 'I_5, x = xv k.
Proof.
split.
- move=> hx.
  exact: (lazard_depressed_vieta_complete
    (p := p) (q := q) (r := r) (s := s) (xv := xv) h hx).
- move=> [k ->].
  exact: lazard_depressed_vieta_root h k.
Qed.

(** Every one of the five inverse-Fourier outputs is a root of
    [X^5 + p X^3 + q X^2 + r X + s]. *)
Theorem lazard_inverse_fourier_output_root
    p q r s a b c d
    (h : lazard_fourier_relations p q r s a b c d) (k : 'I_5) :
  lazard_depressed_quintic_eval p q r s
    (lazard_inverse_fourier_output a b c d k) = 0.
Proof.
exact: lazard_depressed_vieta_root
  (lazard_fourier_relations_vieta h) k.
Qed.

End Vieta.

End PolynomialFormulasLazardQuinticVieta.
