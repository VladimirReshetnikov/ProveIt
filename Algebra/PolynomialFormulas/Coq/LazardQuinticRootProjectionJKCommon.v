From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticFourier
  LazardQuinticProjection LazardQuinticRootProjections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Shared cyclic algebra for Lazard's third and fourth raw root
    projections.  The expensive degree-ten coefficient identities are kept
    in separate J and K modules. *)
Module PolynomialFormulasLazardQuinticRootProjectionJKCommon.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootRadicals.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticRootProjections.
Local Open Scope ring_scope.

Section RootProjectionJKCommon.

Variable F : fieldType.

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

Lemma lazard_root_projection_JK_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_JK_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_JK_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_root_projection_JK_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_root_projection_JK_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_root_projection_JK_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_root_projection_JK_ring_theory :
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

Add Ring lazard_root_projection_JK_ring :
  lazard_root_projection_JK_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_lazard_root_projection_JK_ring :=
  repeat first
    [ rewrite lazard_root_projection_five_natrE
    | rewrite lazard_root_projection_four_natrE
    | rewrite lazard_root_projection_two_natrE
    | rewrite lazard_root_projection_JK_ring_addE
    | rewrite lazard_root_projection_JK_ring_mulE
    | rewrite lazard_root_projection_JK_ring_subE
    | rewrite lazard_root_projection_JK_ring_oppE
    | rewrite lazard_root_projection_JK_ring_zeroE
    | rewrite lazard_root_projection_JK_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** Lazard's remaining two coefficient invariants. *)
Definition lazard_root_invariant_J
    (c : LazardDepressedRootCoefficients F)
    (i : LazardRootInvariants F) : F :=
  - 25%:R * lazard_root_p c * lazard_root_i8 i -
  25%:R * lazard_root_q c * lazard_root_i7 i +
  (- 9%:R * lazard_root_p c ^+ 2 - 60%:R * lazard_root_r c) *
    lazard_root_i6 i +
  (- 7%:R * lazard_root_p c * lazard_root_q c +
    525%:R * lazard_root_s c) * lazard_root_i5 i +
  (- lazard_root_p c ^+ 3 -
    96%:R * lazard_root_p c * lazard_root_r c +
    11%:R * lazard_root_q c ^+ 2) * lazard_root_i4 i +
  50%:R * lazard_root_p c ^+ 3 * lazard_root_r c -
  7%:R * lazard_root_p c ^+ 2 * lazard_root_q c ^+ 2 -
  145%:R * lazard_root_p c * lazard_root_q c * lazard_root_s c -
  308%:R * lazard_root_p c * lazard_root_r c ^+ 2 +
  128%:R * lazard_root_q c ^+ 2 * lazard_root_r c -
  1000%:R * lazard_root_s c ^+ 2.

Definition lazard_root_invariant_K
    (c : LazardDepressedRootCoefficients F)
    (i : LazardRootInvariants F) : F :=
  - 125%:R * lazard_root_p c * lazard_root_i8 i +
  75%:R * lazard_root_q c * lazard_root_i7 i +
  (67%:R * lazard_root_p c ^+ 2 - 420%:R * lazard_root_r c) *
    lazard_root_i6 i +
  (- 109%:R * lazard_root_p c * lazard_root_q c +
    1175%:R * lazard_root_s c) * lazard_root_i5 i +
  (63%:R * lazard_root_p c ^+ 3 -
    412%:R * lazard_root_p c * lazard_root_r c +
    27%:R * lazard_root_q c ^+ 2) * lazard_root_i4 i +
  210%:R * lazard_root_p c ^+ 3 * lazard_root_r c -
  79%:R * lazard_root_p c ^+ 2 * lazard_root_q c ^+ 2 -
  415%:R * lazard_root_p c * lazard_root_q c * lazard_root_s c -
  676%:R * lazard_root_p c * lazard_root_r c ^+ 2 +
  496%:R * lazard_root_q c ^+ 2 * lazard_root_r c -
  750%:R * lazard_root_s c ^+ 2.

(** Cyclic representatives of A = omega - omega^4 and
    B = omega^2 - omega^3. *)
Definition lazard_cyclic_fifth_root_A : LazardCyclicFive F :=
  {| lazard_cyclic0 := 0;
     lazard_cyclic1 := 1;
     lazard_cyclic2 := 0;
     lazard_cyclic3 := 0;
     lazard_cyclic4 := - 1 |}.

Definition lazard_cyclic_fifth_root_B : LazardCyclicFive F :=
  {| lazard_cyclic0 := 0;
     lazard_cyclic1 := 0;
     lazard_cyclic2 := 1;
     lazard_cyclic3 := - 1;
     lazard_cyclic4 := 0 |}.

Lemma lazard_cyclic_fifth_root_A_eval omega :
  lazard_cyclic_eval omega lazard_cyclic_fifth_root_A =
    lazard_fifth_root_A omega.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fifth_root_A
  /lazard_fifth_root_A /=.
finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_cyclic_fifth_root_B_eval omega :
  lazard_cyclic_eval omega lazard_cyclic_fifth_root_B =
    lazard_fifth_root_B omega.
Proof.
rewrite /lazard_cyclic_eval /lazard_cyclic_fifth_root_B
  /lazard_fifth_root_B /=.
finish_lazard_root_projection_JK_ring.
Qed.

(** Generic T and formula-U vectors, parameterized by T' and U'. *)
Definition lazard_cyclic_T_from (tp up : F) : LazardCyclicFive F :=
  lazard_cyclic_add
    (lazard_cyclic_scale tp lazard_cyclic_fifth_root_A)
    (lazard_cyclic_scale up lazard_cyclic_fifth_root_B).

Definition lazard_cyclic_U_from (tp up : F) : LazardCyclicFive F :=
  lazard_cyclic_add
    (lazard_cyclic_scale (- tp) lazard_cyclic_fifth_root_B)
    (lazard_cyclic_scale up lazard_cyclic_fifth_root_A).

Lemma lazard_cyclic_T_from_eval omega tp up :
  lazard_cyclic_eval omega (lazard_cyclic_T_from tp up) =
    lazard_fifth_root_A omega * tp + lazard_fifth_root_B omega * up.
Proof.
rewrite /lazard_cyclic_T_from lazard_cyclic_eval_add
  !lazard_cyclic_eval_scale lazard_cyclic_fifth_root_A_eval
  lazard_cyclic_fifth_root_B_eval.
finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_cyclic_U_from_eval omega tp up :
  lazard_cyclic_eval omega (lazard_cyclic_U_from tp up) =
    - lazard_fifth_root_B omega * tp + lazard_fifth_root_A omega * up.
Proof.
rewrite /lazard_cyclic_U_from lazard_cyclic_eval_add
  !lazard_cyclic_eval_scale lazard_cyclic_fifth_root_A_eval
  lazard_cyclic_fifth_root_B_eval.
finish_lazard_root_projection_JK_ring.
Qed.

Definition lazard_cyclic_fourier_seed (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_fifth_power (lazard_cyclic_fourier_P1 roots).

Definition lazard_cyclic_even_difference_from (a : LazardCyclicFive F) :
    LazardCyclicFive F :=
  lazard_cyclic_sub a (lazard_cyclic_twist2 (lazard_cyclic_twist2 a)).

Definition lazard_cyclic_odd_difference_from (a : LazardCyclicFive F) :
    LazardCyclicFive F :=
  lazard_cyclic_sub (lazard_cyclic_twist2 a)
    (lazard_cyclic_twist2
      (lazard_cyclic_twist2 (lazard_cyclic_twist2 a))).

Definition lazard_cyclic_J_from (tp up : F) (a : LazardCyclicFive F) :
    LazardCyclicFive F :=
  lazard_cyclic_sub
    (lazard_cyclic_mul (lazard_cyclic_T_from tp up)
      (lazard_cyclic_even_difference_from a))
    (lazard_cyclic_mul (lazard_cyclic_U_from tp up)
      (lazard_cyclic_odd_difference_from a)).

Definition lazard_cyclic_K_from (tp up : F) (a : LazardCyclicFive F) :
    LazardCyclicFive F :=
  lazard_cyclic_add
    (lazard_cyclic_mul (lazard_cyclic_U_from tp up)
      (lazard_cyclic_even_difference_from a))
    (lazard_cyclic_mul (lazard_cyclic_T_from tp up)
      (lazard_cyclic_odd_difference_from a)).

Definition lazard_cyclic_J_vector (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_J_from (lazard_root_T_prime roots)
    (lazard_root_U_prime roots) (lazard_cyclic_fourier_seed roots).

Definition lazard_cyclic_K_vector (roots : 5.-tuple F) :
    LazardCyclicFive F :=
  lazard_cyclic_K_from (lazard_root_T_prime roots)
    (lazard_root_U_prime roots) (lazard_cyclic_fourier_seed roots).

Lemma lazard_cyclic_fourier_seed_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_fourier_seed roots) =
    lazard_root_fourier_P1 omega roots ^+ 5.
Proof.
rewrite /lazard_cyclic_fourier_seed lazard_cyclic_eval_fifth_power //
  lazard_cyclic_fourier_P1_eval.
Qed.

Lemma lazard_cyclic_fourier_seed_twist1_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_twist2 (lazard_cyclic_fourier_seed roots)) =
    lazard_root_fourier_P2 omega roots ^+ 5.
Proof.
rewrite -lazard_cyclic_power_P2 /lazard_cyclic_fourier_seed
  lazard_cyclic_eval_fifth_power // lazard_cyclic_fourier_P2_eval.
reflexivity.
Qed.

Lemma lazard_cyclic_power_P4_as_twists roots :
  lazard_cyclic_fifth_power (lazard_cyclic_fourier_P4 roots) =
    lazard_cyclic_twist2
      (lazard_cyclic_twist2 (lazard_cyclic_fourier_seed roots)).
Proof.
rewrite /lazard_cyclic_fourier_seed lazard_cyclic_power_P4
  lazard_cyclic_power_P2.
reflexivity.
Qed.

Lemma lazard_cyclic_fourier_seed_twist2_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_twist2
        (lazard_cyclic_twist2 (lazard_cyclic_fourier_seed roots))) =
    lazard_root_fourier_P4 omega roots ^+ 5.
Proof.
rewrite -lazard_cyclic_power_P4_as_twists
  lazard_cyclic_eval_fifth_power // lazard_cyclic_fourier_P4_eval.
reflexivity.
Qed.

Lemma lazard_cyclic_power_P3_as_twists roots :
  lazard_cyclic_fifth_power (lazard_cyclic_fourier_P3 roots) =
    lazard_cyclic_twist2
      (lazard_cyclic_twist2
        (lazard_cyclic_twist2 (lazard_cyclic_fourier_seed roots))).
Proof.
rewrite /lazard_cyclic_fourier_seed lazard_cyclic_power_P3
  lazard_cyclic_power_P4 lazard_cyclic_power_P2.
reflexivity.
Qed.

Lemma lazard_cyclic_fourier_seed_twist3_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_twist2
        (lazard_cyclic_twist2
          (lazard_cyclic_twist2 (lazard_cyclic_fourier_seed roots)))) =
    lazard_root_fourier_P3 omega roots ^+ 5.
Proof.
rewrite -lazard_cyclic_power_P3_as_twists
  lazard_cyclic_eval_fifth_power // lazard_cyclic_fourier_P3_eval.
reflexivity.
Qed.

Lemma lazard_cyclic_even_difference_from_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_even_difference_from
        (lazard_cyclic_fourier_seed roots)) =
    lazard_root_fourier_P1 omega roots ^+ 5 -
      lazard_root_fourier_P4 omega roots ^+ 5.
Proof.
rewrite /lazard_cyclic_even_difference_from lazard_cyclic_eval_sub
  lazard_cyclic_fourier_seed_eval //
  lazard_cyclic_fourier_seed_twist2_eval //.
Qed.

Lemma lazard_cyclic_odd_difference_from_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega
      (lazard_cyclic_odd_difference_from
        (lazard_cyclic_fourier_seed roots)) =
    lazard_root_fourier_P2 omega roots ^+ 5 -
      lazard_root_fourier_P3 omega roots ^+ 5.
Proof.
rewrite /lazard_cyclic_odd_difference_from lazard_cyclic_eval_sub
  lazard_cyclic_fourier_seed_twist1_eval //
  lazard_cyclic_fourier_seed_twist3_eval //.
Qed.

Lemma lazard_cyclic_J_vector_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_J_vector roots) =
    lazard_root_T omega roots *
      (lazard_root_fourier_P1 omega roots ^+ 5 -
       lazard_root_fourier_P4 omega roots ^+ 5) -
    lazard_root_formula_U omega roots *
      (lazard_root_fourier_P2 omega roots ^+ 5 -
       lazard_root_fourier_P3 omega roots ^+ 5).
Proof.
rewrite /lazard_cyclic_J_vector /lazard_cyclic_J_from
  lazard_cyclic_eval_sub !lazard_cyclic_eval_mul //
  lazard_cyclic_T_from_eval lazard_cyclic_U_from_eval
  lazard_cyclic_even_difference_from_eval //
  lazard_cyclic_odd_difference_from_eval //
  /lazard_root_T /lazard_root_formula_U /lazard_root_printed_U.
finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_cyclic_K_vector_eval omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_cyclic_eval omega (lazard_cyclic_K_vector roots) =
    lazard_root_formula_U omega roots *
      (lazard_root_fourier_P1 omega roots ^+ 5 -
       lazard_root_fourier_P4 omega roots ^+ 5) +
    lazard_root_T omega roots *
      (lazard_root_fourier_P2 omega roots ^+ 5 -
       lazard_root_fourier_P3 omega roots ^+ 5).
Proof.
rewrite /lazard_cyclic_K_vector /lazard_cyclic_K_from
  lazard_cyclic_eval_add !lazard_cyclic_eval_mul //
  lazard_cyclic_T_from_eval lazard_cyclic_U_from_eval
  lazard_cyclic_even_difference_from_eval //
  lazard_cyclic_odd_difference_from_eval //
  /lazard_root_T /lazard_root_formula_U /lazard_root_printed_U.
finish_lazard_root_projection_JK_ring.
Qed.

(** Both vectors are invariant under the exponent-doubling action.  Their
    common sparse shape exposes the two root-only coefficient cores. *)
Lemma lazard_cyclic_J_from_shape tp up a :
  let v :=
    tp * (lazard_cyclic4 a - lazard_cyclic1 a) +
    up * (lazard_cyclic3 a - lazard_cyclic2 a) in
  lazard_cyclic_J_from tp up a =
    {| lazard_cyclic0 := 4%:R * v;
       lazard_cyclic1 := - v;
       lazard_cyclic2 := - v;
       lazard_cyclic3 := - v;
       lazard_cyclic4 := - v |}.
Proof.
rewrite /lazard_cyclic_J_from /lazard_cyclic_T_from
  /lazard_cyclic_U_from /lazard_cyclic_even_difference_from
  /lazard_cyclic_odd_difference_from /lazard_cyclic_fifth_root_A
  /lazard_cyclic_fifth_root_B /lazard_cyclic_add /lazard_cyclic_sub
  /lazard_cyclic_neg /lazard_cyclic_scale /lazard_cyclic_mul
  /lazard_cyclic_twist2 /=.
apply: lazard_cyclic_ext=> /=; finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_cyclic_K_from_shape tp up a :
  let v :=
    - tp * (lazard_cyclic3 a - lazard_cyclic2 a) +
    up * (lazard_cyclic4 a - lazard_cyclic1 a) in
  lazard_cyclic_K_from tp up a =
    {| lazard_cyclic0 := 4%:R * v;
       lazard_cyclic1 := - v;
       lazard_cyclic2 := - v;
       lazard_cyclic3 := - v;
       lazard_cyclic4 := - v |}.
Proof.
rewrite /lazard_cyclic_K_from /lazard_cyclic_T_from
  /lazard_cyclic_U_from /lazard_cyclic_even_difference_from
  /lazard_cyclic_odd_difference_from /lazard_cyclic_fifth_root_A
  /lazard_cyclic_fifth_root_B /lazard_cyclic_add /lazard_cyclic_sub
  /lazard_cyclic_neg /lazard_cyclic_scale /lazard_cyclic_mul
  /lazard_cyclic_twist2 /=.
apply: lazard_cyclic_ext=> /=; finish_lazard_root_projection_JK_ring.
Qed.

Definition lazard_root_J_component (roots : 5.-tuple F) : F :=
  let a := lazard_cyclic_fourier_seed roots in
  lazard_root_T_prime roots *
      (lazard_cyclic4 a - lazard_cyclic1 a) +
    lazard_root_U_prime roots *
      (lazard_cyclic3 a - lazard_cyclic2 a).

Definition lazard_root_K_component (roots : 5.-tuple F) : F :=
  let a := lazard_cyclic_fourier_seed roots in
  - lazard_root_T_prime roots *
      (lazard_cyclic3 a - lazard_cyclic2 a) +
    lazard_root_U_prime roots *
      (lazard_cyclic4 a - lazard_cyclic1 a).

Lemma lazard_cyclic_J_vector_shape roots :
  lazard_cyclic_J_vector roots =
    {| lazard_cyclic0 := 4%:R * lazard_root_J_component roots;
       lazard_cyclic1 := - lazard_root_J_component roots;
       lazard_cyclic2 := - lazard_root_J_component roots;
       lazard_cyclic3 := - lazard_root_J_component roots;
       lazard_cyclic4 := - lazard_root_J_component roots |}.
Proof.
rewrite /lazard_cyclic_J_vector /lazard_root_J_component
  lazard_cyclic_J_from_shape.
reflexivity.
Qed.

Lemma lazard_cyclic_K_vector_shape roots :
  lazard_cyclic_K_vector roots =
    {| lazard_cyclic0 := 4%:R * lazard_root_K_component roots;
       lazard_cyclic1 := - lazard_root_K_component roots;
       lazard_cyclic2 := - lazard_root_K_component roots;
       lazard_cyclic3 := - lazard_root_K_component roots;
       lazard_cyclic4 := - lazard_root_K_component roots |}.
Proof.
rewrite /lazard_cyclic_K_vector /lazard_root_K_component
  lazard_cyclic_K_from_shape.
reflexivity.
Qed.

Lemma lazard_cyclic_J_vector_tail_equal roots :
  lazard_cyclic1 (lazard_cyclic_J_vector roots) =
      lazard_cyclic2 (lazard_cyclic_J_vector roots) /\
  lazard_cyclic2 (lazard_cyclic_J_vector roots) =
      lazard_cyclic3 (lazard_cyclic_J_vector roots) /\
  lazard_cyclic3 (lazard_cyclic_J_vector roots) =
      lazard_cyclic4 (lazard_cyclic_J_vector roots).
Proof. by rewrite lazard_cyclic_J_vector_shape. Qed.

Lemma lazard_cyclic_K_vector_tail_equal roots :
  lazard_cyclic1 (lazard_cyclic_K_vector roots) =
      lazard_cyclic2 (lazard_cyclic_K_vector roots) /\
  lazard_cyclic2 (lazard_cyclic_K_vector roots) =
      lazard_cyclic3 (lazard_cyclic_K_vector roots) /\
  lazard_cyclic3 (lazard_cyclic_K_vector roots) =
      lazard_cyclic4 (lazard_cyclic_K_vector roots).
Proof. by rewrite lazard_cyclic_K_vector_shape. Qed.

Lemma lazard_cyclic_J_vector_difference roots :
  lazard_cyclic0 (lazard_cyclic_J_vector roots) -
      lazard_cyclic1 (lazard_cyclic_J_vector roots) =
    5%:R * lazard_root_J_component roots.
Proof.
rewrite lazard_cyclic_J_vector_shape /=.
finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_cyclic_K_vector_difference roots :
  lazard_cyclic0 (lazard_cyclic_K_vector roots) -
      lazard_cyclic1 (lazard_cyclic_K_vector roots) =
    5%:R * lazard_root_K_component roots.
Proof.
rewrite lazard_cyclic_K_vector_shape /=.
finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_root_standard_projection_J_as_cyclic omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_standard_projections (lazard_root_epsilon omega roots)
      (lazard_root_T omega roots) (lazard_root_formula_U omega roots)
      (lazard_root_fourier_fifth_orbit omega roots) p2 =
    lazard_cyclic_eval omega (lazard_cyclic_J_vector roots).
Proof.
rewrite lazard_standard_projection2
  lazard_root_fourier_fifth_orbit_p0
  lazard_root_fourier_fifth_orbit_p1
  lazard_root_fourier_fifth_orbit_p2
  lazard_root_fourier_fifth_orbit_p3
  lazard_cyclic_J_vector_eval //.
finish_lazard_root_projection_JK_ring.
Qed.

Lemma lazard_root_standard_projection_K_as_cyclic omega roots
    (omega_primitive : 5.-primitive_root omega) :
  lazard_standard_projections (lazard_root_epsilon omega roots)
      (lazard_root_T omega roots) (lazard_root_formula_U omega roots)
      (lazard_root_fourier_fifth_orbit omega roots) p3 =
    lazard_cyclic_eval omega (lazard_cyclic_K_vector roots).
Proof.
rewrite lazard_standard_projection3
  lazard_root_fourier_fifth_orbit_p0
  lazard_root_fourier_fifth_orbit_p1
  lazard_root_fourier_fifth_orbit_p2
  lazard_root_fourier_fifth_orbit_p3
  lazard_cyclic_K_vector_eval //.
finish_lazard_root_projection_JK_ring.
Qed.

End RootProjectionJKCommon.

End PolynomialFormulasLazardQuinticRootProjectionJKCommon.
