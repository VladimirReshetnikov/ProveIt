From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues
  LazardQuinticFourier LazardQuinticProjection LazardQuinticQuadratic
  LazardQuinticRootRadicals
  LazardQuinticQ1ProjectionBridge LazardQuinticRootProjections
  LazardQuinticRootBranchEquivariance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's literal combined root/cyclotomic action in Section 5.

    The five entries below are exactly [s0,...,s4], and the four cyclic
    entries are exactly

      [S1 = s1^5], [S2 = s2 s1^3], [S3 = s3 s1^2], [S4 = s4 s1].

    The root action [phi] sends [x_i] to [x_(2i)], while [psi] sends the
    chosen primitive fifth root [omega] to [omega^2].  We prove their
    commutation, fixedness of both displayed tuples under the composite,
    and the general implication from [phi]-invariance plus composite
    fixedness to independence under [omega -> omega^2]. *)
Module PolynomialFormulasLazardQuinticSectionFiveCombinedAction.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.

Module P := PolynomialFormulasLazardQuinticProjection.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module LF := PolynomialFormulasLazardQuinticFourier.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module QB := PolynomialFormulasLazardQuinticQ1ProjectionBridge.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module TV := PolynomialFormulasQuinticThetaValues.

Section Configuration.

Variable F : fieldType.

Lemma lazard_primitive_fifth_squared (z : F) :
  5.-primitive_root z -> 5.-primitive_root (z ^+ 2).
Proof.
move=> z_primitive.
by rewrite (prim_root_exp_coprime 2 z_primitive).
Qed.

(** A primitive fifth-root generator together with an ordered root tuple. *)
Record LazardSectionFiveConfiguration := {
  lazard_section_five_config_omega : F;
  lazard_section_five_config_omega_primitive :
    5.-primitive_root lazard_section_five_config_omega;
  lazard_section_five_config_roots : 5.-tuple F
}.

(** Lazard's [phi : x_i -> x_(2i)]. *)
Definition lazard_section_five_phi
    (c : LazardSectionFiveConfiguration) :
    LazardSectionFiveConfiguration :=
  {| lazard_section_five_config_omega :=
       lazard_section_five_config_omega c;
     lazard_section_five_config_omega_primitive :=
       lazard_section_five_config_omega_primitive c;
     lazard_section_five_config_roots :=
       TV.permute_quintic_roots multiplier_two
         (lazard_section_five_config_roots c) |}.

(** Lazard's [psi : omega -> omega^2]. *)
Definition lazard_section_five_psi
    (c : LazardSectionFiveConfiguration) :
    LazardSectionFiveConfiguration :=
  {| lazard_section_five_config_omega :=
       lazard_section_five_config_omega c ^+ 2;
     lazard_section_five_config_omega_primitive :=
       lazard_primitive_fifth_squared
         (lazard_section_five_config_omega_primitive c);
     lazard_section_five_config_roots :=
       lazard_section_five_config_roots c |}.

Theorem lazard_section_five_phi_psi_commute
    (c : LazardSectionFiveConfiguration) :
  lazard_section_five_phi (lazard_section_five_psi c) =
    lazard_section_five_psi (lazard_section_five_phi c).
Proof. by case: c. Qed.

End Configuration.

Section CombinedAction.

Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : 5.-primitive_root omega.

(** Re-register the root-radical module's proved MathComp ring theory in
    this compiled module.  Ltac registrations do not cross [.vo]
    boundaries, so the local wrapper deliberately refers only to exported
    lemmas and definitions. *)
Add Ring lazard_section_five_ring :
  (@RR.lazard_mathcomp_ring_theory F).
Opaque RR.ring_zero RR.ring_one RR.ring_add RR.ring_mul RR.ring_sub
  RR.ring_opp RR.ring_eq.

Ltac finish_section_five_ring :=
  repeat first
    [ rewrite RR.lazard_two_natrE | rewrite RR.lazard_three_natrE
    | rewrite RR.lazard_four_natrE | rewrite RR.lazard_five_natrE
    | rewrite RR.lazard_eight_natrE | rewrite RR.lazard_nine_natrE
    | rewrite expr2 | rewrite RR.lazard_expr3E
    | rewrite RR.lazard_expr4E | rewrite RR.lazard_expr5E
    | rewrite RR.lazard_expr6E | rewrite RR.lazard_expr7E
    | rewrite RR.lazard_expr8E
    | rewrite RR.ring_addE | rewrite RR.ring_mulE
    | rewrite RR.ring_subE | rewrite RR.ring_oppE
    | rewrite RR.ring_zeroE | rewrite RR.ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (RR.ring_eq lhs rhs)
  end;
  ring.

(** Every primitive fifth root is one of the four powers of the selected
    generator.  The exponent-zero case is excluded by primitivity, rather
    than by an extra characteristic hypothesis. *)
Lemma lazard_primitive_fifth_root_cases (z : F) :
  5.-primitive_root z ->
  z = omega \/ z = omega ^+ 2 \/ z = omega ^+ 3 \/ z = omega ^+ 4.
Proof.
move=> z_primitive.
have z_power : z ^+ 5 = 1 := prim_expr_order z_primitive.
have [j hj] := prim_rootP omega_primitive z_power.
case: j hj=> [[|[|[|[|[|j]]]]] hjlt] //= hj.
- have hbad : (5 %| 1)%N.
    by rewrite (prim_order_dvd z_primitive) hj expr0.
  by move: hbad.
- left. by rewrite hj expr1.
- by right; left.
- by right; right; left.
- by right; right; right.
Qed.

(** Multiplication by two is the explicit [rotate] branch on root tuples. *)
Lemma permute_multiplier_two_is_rotate_branch (roots : 5.-tuple F) :
  TV.permute_quintic_roots multiplier_two roots =
    BE.lazard_roots_for_branch roots Q.LazardBranchRotate.
Proof.
apply: eq_from_tnth=> i.
rewrite TV.tnth_permute_quintic_roots
  BE.lazard_roots_for_branch_tnth.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite multiplier_two_o0 /BE.lazard_branch_index.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite multiplier_two_o1 /BE.lazard_branch_index.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite multiplier_two_o2 /BE.lazard_branch_index.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite multiplier_two_o3 /BE.lazard_branch_index.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite multiplier_two_o4 /BE.lazard_branch_index.
- by move: hi.
Qed.

(** The corrected multiplier-two identities in the [U] convention printed
    before Figure 3.  Since Figure 3 actually uses
    [U_formula = -U_printed], the correct second identity has a plus sign:
    [phi(T) = -U_printed] and [phi(U_printed) = T]. *)
Theorem lazard_root_T_phi_eq_neg_printed_U (roots : 5.-tuple F) :
  RR.lazard_root_T omega
      (TV.permute_quintic_roots multiplier_two roots) =
    - RR.lazard_root_printed_U omega roots.
Proof.
rewrite permute_multiplier_two_is_rotate_branch.
have ht := congr1 (@Q.lazard_t F)
  (BE.lazard_root_quadratic_triple_roots_for_branch
    omega roots Q.LazardBranchRotate).
move: ht.
by rewrite /BE.lazard_root_quadratic_triple /Q.lazard_branch_triple /=
  RR.lazard_root_formula_U_eq_neg_printed_U.
Qed.

Theorem lazard_root_printed_U_phi_eq_T (roots : 5.-tuple F) :
  RR.lazard_root_printed_U omega
      (TV.permute_quintic_roots multiplier_two roots) =
    RR.lazard_root_T omega roots.
Proof.
rewrite permute_multiplier_two_is_rotate_branch.
have hu := congr1 (@Q.lazard_u F)
  (BE.lazard_root_quadratic_triple_roots_for_branch
    omega roots Q.LazardBranchRotate).
have hneg := congr1 (fun x : F => - x) hu.
move: hneg.
by rewrite /BE.lazard_root_quadratic_triple /Q.lazard_branch_triple /=
  /RR.lazard_root_formula_U !opprK.
Qed.

(** The elementary fifth-root coefficients under [omega -> omega^2]. *)
Lemma lazard_fifth_root_A_squared :
  RR.lazard_fifth_root_A (omega ^+ 2) =
    RR.lazard_fifth_root_B omega.
Proof.
rewrite /RR.lazard_fifth_root_A /RR.lazard_fifth_root_B
  -(@exprM F omega 2 4)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_fifth_root_B_squared :
  RR.lazard_fifth_root_B (omega ^+ 2) =
    - RR.lazard_fifth_root_A omega.
Proof.
rewrite /RR.lazard_fifth_root_A /RR.lazard_fifth_root_B
  -(@exprM F omega 2 2) -(@exprM F omega 2 3)
  (RP.lazard_primitive_fifth_power6 omega_primitive).
by rewrite opprB.
Qed.

Lemma lazard_fifth_root_discriminant_factor_squared :
  RR.lazard_fifth_root_discriminant_factor (omega ^+ 2) =
    - RR.lazard_fifth_root_discriminant_factor omega.
Proof.
rewrite /RR.lazard_fifth_root_discriminant_factor
  -(@exprM F omega 2 4) -(@exprM F omega 2 2)
  -(@exprM F omega 2 3)
  (RP.lazard_primitive_fifth_power8 omega_primitive)
  (RP.lazard_primitive_fifth_power6 omega_primitive).
finish_section_five_ring.
Qed.

Lemma lazard_root_epsilon_squared (roots : 5.-tuple F) :
  RR.lazard_root_epsilon (omega ^+ 2) roots =
    - RR.lazard_root_epsilon omega roots.
Proof.
rewrite /RR.lazard_root_epsilon
  lazard_fifth_root_discriminant_factor_squared.
finish_section_five_ring.
Qed.

Lemma lazard_root_T_squared (roots : 5.-tuple F) :
  RR.lazard_root_T (omega ^+ 2) roots =
    - RR.lazard_root_formula_U omega roots.
Proof.
rewrite /RR.lazard_root_T /RR.lazard_root_formula_U
  /RR.lazard_root_printed_U
  lazard_fifth_root_A_squared lazard_fifth_root_B_squared.
finish_section_five_ring.
Qed.

Lemma lazard_root_formula_U_squared (roots : 5.-tuple F) :
  RR.lazard_root_formula_U (omega ^+ 2) roots =
    RR.lazard_root_T omega roots.
Proof.
rewrite /RR.lazard_root_T /RR.lazard_root_formula_U
  /RR.lazard_root_printed_U
  lazard_fifth_root_A_squared lazard_fifth_root_B_squared.
finish_section_five_ring.
Qed.

(** The actual quadratic triple follows the rotate-negate branch. *)
Lemma lazard_root_quadratic_triple_squared (roots : 5.-tuple F) :
  BE.lazard_root_quadratic_triple (omega ^+ 2) roots =
    Q.lazard_branch_triple (BE.lazard_root_quadratic_triple omega roots)
      Q.LazardBranchRotateNegate.
Proof.
apply: BE.lazard_quadratic_triple_ext.
- exact: lazard_root_epsilon_squared.
- exact: lazard_root_T_squared.
- exact: lazard_root_formula_U_squared.
Qed.

(** The four Fourier coordinates cycle under [omega -> omega^2]. *)
Lemma lazard_root_fourier_P1_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P1 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P2 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P1 /RP.lazard_root_fourier_P2
  -(@exprM F omega 2 2) -(@exprM F omega 2 3)
  -(@exprM F omega 2 4)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_P2_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P2 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P4 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P2 /RP.lazard_root_fourier_P4
  -(@exprM F omega 2 2) -(@exprM F omega 2 4)
  -(@exprM F omega 2 3)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_P4_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P4 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P3 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P4 /RP.lazard_root_fourier_P3
  -(@exprM F omega 2 4) -(@exprM F omega 2 3)
  -(@exprM F omega 2 2)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

Lemma lazard_root_fourier_P3_squared (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P3 (omega ^+ 2) roots =
    RP.lazard_root_fourier_P1 omega roots.
Proof.
rewrite /RP.lazard_root_fourier_P3 /RP.lazard_root_fourier_P1
  -(@exprM F omega 2 3) -(@exprM F omega 2 4)
  -(@exprM F omega 2 2)
  (RP.lazard_primitive_fifth_power6 omega_primitive)
  (RP.lazard_primitive_fifth_power8 omega_primitive).
reflexivity.
Qed.

(** The literal tuple [s0,...,s4] from the paper. *)
Definition lazard_section_five_fourier_s
    (z : F) (roots : 5.-tuple F) : 5.-tuple F :=
  [tuple nth 0
    [:: RP.lazard_root_esymm1 roots;
        RP.lazard_root_fourier_P1 z roots;
        RP.lazard_root_fourier_P2 z roots;
        RP.lazard_root_fourier_P3 z roots;
        RP.lazard_root_fourier_P4 z roots] i | i < 5].

(** The literal tuple [S1,...,S4] from the paper. *)
Definition lazard_section_five_cyclic_S
    (z : F) (roots : 5.-tuple F) : 4.-tuple F :=
  let s := lazard_section_five_fourier_s z roots in
  [tuple nth 0
    [:: tnth s o1 ^+ 5;
        tnth s o2 * tnth s o1 ^+ 3;
        tnth s o3 * tnth s o1 ^+ 2;
        tnth s o4 * tnth s o1] i | i < 4].

Lemma lazard_section_five_fourier_s_o0E
    (z : F) (roots : 5.-tuple F) :
  tnth (lazard_section_five_fourier_s z roots) o0 =
    RP.lazard_root_esymm1 roots.
Proof. by rewrite /lazard_section_five_fourier_s tnth_mktuple. Qed.

(** For a depressed quintic the literal coordinate [s0] is zero. *)
Theorem lazard_section_five_fourier_s_o0_eq_zero
    (z : F) (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  tnth (lazard_section_five_fourier_s z roots) o0 = 0.
Proof. by rewrite lazard_section_five_fourier_s_o0E hsum. Qed.

(** The tuple permutation by Lazard's five-cycle is the cyclic shift used
    by the shared Fourier development. *)
Lemma permute_five_cycle_is_cyclic_shift (roots : 5.-tuple F) :
  TV.permute_quintic_roots five_cycle roots = LF.lazard_cyclic_shift roots.
Proof. by []. Qed.

Lemma lazard_root_fourier_P1_five_cycle (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P1 omega
      (TV.permute_quintic_roots five_cycle roots) =
    omega * RP.lazard_root_fourier_P1 omega roots.
Proof.
rewrite permute_five_cycle_is_cyclic_shift
  (@RP.lazard_root_fourier_P1E F omega (LF.lazard_cyclic_shift roots))
  (@RP.lazard_root_fourier_P1E F omega roots).
exact: (@LF.lazard_fourier_sum_cyclic_shift
  F omega omega_primitive roots o1).
Qed.

Lemma lazard_root_fourier_P2_five_cycle (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P2 omega
      (TV.permute_quintic_roots five_cycle roots) =
    omega ^+ 2 * RP.lazard_root_fourier_P2 omega roots.
Proof.
rewrite permute_five_cycle_is_cyclic_shift
  (@RP.lazard_root_fourier_P2E F omega (LF.lazard_cyclic_shift roots)
    omega_primitive)
  (@RP.lazard_root_fourier_P2E F omega roots omega_primitive).
exact: (@LF.lazard_fourier_sum_cyclic_shift
  F omega omega_primitive roots o2).
Qed.

Lemma lazard_root_fourier_P3_five_cycle (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P3 omega
      (TV.permute_quintic_roots five_cycle roots) =
    omega ^+ 3 * RP.lazard_root_fourier_P3 omega roots.
Proof.
rewrite permute_five_cycle_is_cyclic_shift
  (@RP.lazard_root_fourier_P3E F omega (LF.lazard_cyclic_shift roots)
    omega_primitive)
  (@RP.lazard_root_fourier_P3E F omega roots omega_primitive).
exact: (@LF.lazard_fourier_sum_cyclic_shift
  F omega omega_primitive roots o3).
Qed.

Lemma lazard_root_fourier_P4_five_cycle (roots : 5.-tuple F) :
  RP.lazard_root_fourier_P4 omega
      (TV.permute_quintic_roots five_cycle roots) =
    omega ^+ 4 * RP.lazard_root_fourier_P4 omega roots.
Proof.
rewrite permute_five_cycle_is_cyclic_shift
  (@RP.lazard_root_fourier_P4E F omega (LF.lazard_cyclic_shift roots)
    omega_primitive)
  (@RP.lazard_root_fourier_P4E F omega roots omega_primitive).
exact: (@LF.lazard_fourier_sum_cyclic_shift
  F omega omega_primitive roots o4).
Qed.

(** The four total Fourier weights in [S1,...,S4] are all five. *)
Lemma lazard_cyclic_weight_five (a : F) :
  (omega * a) ^+ 5 = a ^+ 5.
Proof.
by rewrite exprMn (prim_expr_order omega_primitive) mul1r.
Qed.

Lemma lazard_cyclic_weight_two_three (a b : F) :
  (omega ^+ 2 * a) * (omega * b) ^+ 3 = a * b ^+ 3.
Proof.
have hfactor :
    (omega ^+ 2 * a) * (omega * b) ^+ 3 =
      omega ^+ 5 * (a * b ^+ 3).
  finish_section_five_ring.
by rewrite hfactor (prim_expr_order omega_primitive) mul1r.
Qed.

Lemma lazard_cyclic_weight_three_two (a b : F) :
  (omega ^+ 3 * a) * (omega * b) ^+ 2 = a * b ^+ 2.
Proof.
have hfactor :
    (omega ^+ 3 * a) * (omega * b) ^+ 2 =
      omega ^+ 5 * (a * b ^+ 2).
  finish_section_five_ring.
by rewrite hfactor (prim_expr_order omega_primitive) mul1r.
Qed.

Lemma lazard_cyclic_weight_four_one (a b : F) :
  (omega ^+ 4 * a) * (omega * b) = a * b.
Proof.
have hfactor :
    (omega ^+ 4 * a) * (omega * b) = omega ^+ 5 * (a * b).
  finish_section_five_ring.
by rewrite hfactor (prim_expr_order omega_primitive) mul1r.
Qed.

(** Lazard's literal mixed tuple [S1,...,S4] is cyclically invariant. *)
Theorem lazard_section_five_cyclic_S_five_cycle_fixed
    (roots : 5.-tuple F) :
  lazard_section_five_cyclic_S omega
      (TV.permute_quintic_roots five_cycle roots) =
    lazard_section_five_cyclic_S omega roots.
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|i]]]] hi] //=;
rewrite /lazard_section_five_cyclic_S
  /lazard_section_five_fourier_s !tnth_mktuple /=.
- by rewrite lazard_root_fourier_P1_five_cycle
    lazard_cyclic_weight_five.
- by rewrite lazard_root_fourier_P2_five_cycle
    lazard_root_fourier_P1_five_cycle lazard_cyclic_weight_two_three.
- by rewrite lazard_root_fourier_P3_five_cycle
    lazard_root_fourier_P1_five_cycle lazard_cyclic_weight_three_two.
- by rewrite lazard_root_fourier_P4_five_cycle
    lazard_root_fourier_P1_five_cycle lazard_cyclic_weight_four_one.
Qed.

(** The unscaled inverse Fourier equation at coordinate zero, stated for
    the actual Section 5 tuple rather than an auxiliary Fourier object. *)
Theorem lazard_section_five_fourier_sum_recovery
    (roots : 5.-tuple F) :
  tnth (lazard_section_five_fourier_s omega roots) o0 +
      tnth (lazard_section_five_fourier_s omega roots) o1 +
      tnth (lazard_section_five_fourier_s omega roots) o2 +
      tnth (lazard_section_five_fourier_s omega roots) o3 +
      tnth (lazard_section_five_fourier_s omega roots) o4 =
    5%:R * tnth roots o0.
Proof.
have hidentity :
    tnth (lazard_section_five_fourier_s omega roots) o0 +
        tnth (lazard_section_five_fourier_s omega roots) o1 +
        tnth (lazard_section_five_fourier_s omega roots) o2 +
        tnth (lazard_section_five_fourier_s omega roots) o3 +
        tnth (lazard_section_five_fourier_s omega roots) o4 =
      5%:R * tnth roots o0 +
        RR.lazard_root_fifth_cyclotomic_value omega *
          (tnth roots o1 + tnth roots o2 + tnth roots o3 +
            tnth roots o4).
  rewrite /lazard_section_five_fourier_s !tnth_mktuple /=
    /RP.lazard_root_esymm1
    /RP.lazard_root_fourier_P1 /RP.lazard_root_fourier_P2
    /RP.lazard_root_fourier_P3 /RP.lazard_root_fourier_P4
    /RR.lazard_root_fifth_cyclotomic_value.
  finish_section_five_ring.
rewrite hidentity
  (RR.lazard_primitive_fifth_root_cyclotomic omega_primitive).
by rewrite mul0r addr0.
Qed.

(** Dividing the definitions of [S2,S3,S4] by the indicated nonzero
    powers of the actual [s1] recovers the remaining Fourier coordinates. *)
Theorem lazard_section_five_x0_recovery_scaled
    (roots : 5.-tuple F)
    (s1_neq0 :
      tnth (lazard_section_five_fourier_s omega roots) o1 != 0) :
  5%:R * tnth roots o0 =
    tnth (lazard_section_five_fourier_s omega roots) o0 +
    tnth (lazard_section_five_fourier_s omega roots) o1 +
    tnth (lazard_section_five_cyclic_S omega roots) P.p1 /
      tnth (lazard_section_five_fourier_s omega roots) o1 ^+ 3 +
    tnth (lazard_section_five_cyclic_S omega roots) P.p2 /
      tnth (lazard_section_five_fourier_s omega roots) o1 ^+ 2 +
    tnth (lazard_section_five_cyclic_S omega roots) P.p3 /
      tnth (lazard_section_five_fourier_s omega roots) o1.
Proof.
have p1_neq0 : RP.lazard_root_fourier_P1 omega roots != 0.
  move: s1_neq0.
  by rewrite /lazard_section_five_fourier_s tnth_mktuple.
have p1_cube_neq0 := expf_neq0 3 p1_neq0.
have p1_square_neq0 := expf_neq0 2 p1_neq0.
have hS2 :
    tnth (lazard_section_five_cyclic_S omega roots) P.p1 /
        tnth (lazard_section_five_fourier_s omega roots) o1 ^+ 3 =
      tnth (lazard_section_five_fourier_s omega roots) o2.
  rewrite /lazard_section_five_cyclic_S
    /lazard_section_five_fourier_s !tnth_mktuple /=.
  exact: mulfK p1_cube_neq0 _.
have hS3 :
    tnth (lazard_section_five_cyclic_S omega roots) P.p2 /
        tnth (lazard_section_five_fourier_s omega roots) o1 ^+ 2 =
      tnth (lazard_section_five_fourier_s omega roots) o3.
  rewrite /lazard_section_five_cyclic_S
    /lazard_section_five_fourier_s !tnth_mktuple /=.
  exact: mulfK p1_square_neq0 _.
have hS4 :
    tnth (lazard_section_five_cyclic_S omega roots) P.p3 /
        tnth (lazard_section_five_fourier_s omega roots) o1 =
      tnth (lazard_section_five_fourier_s omega roots) o4.
  rewrite /lazard_section_five_cyclic_S
    /lazard_section_five_fourier_s !tnth_mktuple /=.
  exact: mulfK p1_neq0 _.
rewrite hS2 hS3 hS4.
exact: esym (lazard_section_five_fourier_sum_recovery roots).
Qed.

(** Lazard's displayed [x0] equation for a depressed quintic. *)
Theorem lazard_section_five_x0_recovery
    (roots : 5.-tuple F)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (s1_neq0 :
      tnth (lazard_section_five_fourier_s omega roots) o1 != 0)
    (five_neq0 : (5%:R : F) != 0) :
  tnth roots o0 =
    (tnth (lazard_section_five_fourier_s omega roots) o1 +
      tnth (lazard_section_five_cyclic_S omega roots) P.p1 /
        tnth (lazard_section_five_fourier_s omega roots) o1 ^+ 3 +
      tnth (lazard_section_five_cyclic_S omega roots) P.p2 /
        tnth (lazard_section_five_fourier_s omega roots) o1 ^+ 2 +
      tnth (lazard_section_five_cyclic_S omega roots) P.p3 /
        tnth (lazard_section_five_fourier_s omega roots) o1) / 5%:R.
Proof.
apply: (mulfI five_neq0).
rewrite [5%:R * (_ / 5%:R)]mulrC divfK.
rewrite lazard_section_five_x0_recovery_scaled //.
by rewrite (@lazard_section_five_fourier_s_o0_eq_zero omega roots hsum)
  add0r.
exact five_neq0.
Qed.

(** The four positive Fourier sums, in the existing orbit order
    [s1,s2,s4,s3], follow the rotate-negate source permutation under
    [omega -> omega^2]. *)
Lemma lazard_root_fourier_orbit_squared
    (roots : 5.-tuple F) (i : 'I_4) :
  BE.lazard_root_fourier_orbit (omega ^+ 2) roots i =
    BE.lazard_source_for_branch
      (BE.lazard_root_fourier_orbit omega roots)
      Q.LazardBranchRotateNegate i.
Proof.
case: i=> [[|[|[|[|i]]]] hi] //=;
by rewrite /BE.lazard_root_fourier_orbit /BE.lazard_source_for_branch
  /QB.lazard_rotate_negate_source /P.p0 /P.p1 /P.p2 /P.p3 /=
  ?lazard_root_fourier_P1_squared
  ?lazard_root_fourier_P2_squared
  ?lazard_root_fourier_P3_squared
  ?lazard_root_fourier_P4_squared.
Qed.

(** The rotate and rotate-negate source permutations cancel. *)
Theorem lazard_root_fourier_orbit_phi_psi_fixed
    (roots : 5.-tuple F) (i : 'I_4) :
  BE.lazard_root_fourier_orbit (omega ^+ 2)
      (TV.permute_quintic_roots multiplier_two roots) i =
    BE.lazard_root_fourier_orbit omega roots i.
Proof.
rewrite permute_multiplier_two_is_rotate_branch
  lazard_root_fourier_orbit_squared.
case: i=> [[|[|[|[|i]]]] hi] //=;
by rewrite /BE.lazard_source_for_branch
  /QB.lazard_rotate_source /QB.lazard_rotate_negate_source
  /P.p0 /P.p1 /P.p2 /P.p3 /=
  BE.lazard_root_fourier_orbit_roots_for_branch.
Qed.

(** Every displayed [s0,...,s4] is fixed by [phi o psi]. *)
Theorem lazard_section_five_fourier_s_phi_psi_fixed
    (roots : 5.-tuple F) :
  lazard_section_five_fourier_s (omega ^+ 2)
      (TV.permute_quintic_roots multiplier_two roots) =
    lazard_section_five_fourier_s omega roots.
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]] hi] //=;
rewrite /lazard_section_five_fourier_s !tnth_mktuple /=.
- by rewrite permute_multiplier_two_is_rotate_branch
    BE.lazard_root_esymm1_roots_for_branch.
- exact: (lazard_root_fourier_orbit_phi_psi_fixed roots P.p0).
- exact: (lazard_root_fourier_orbit_phi_psi_fixed roots P.p1).
- exact: (lazard_root_fourier_orbit_phi_psi_fixed roots P.p3).
- exact: (lazard_root_fourier_orbit_phi_psi_fixed roots P.p2).
Qed.

(** Every displayed [S1,...,S4] is fixed by [phi o psi]. *)
Theorem lazard_section_five_cyclic_S_phi_psi_fixed
    (roots : 5.-tuple F) :
  lazard_section_five_cyclic_S (omega ^+ 2)
      (TV.permute_quintic_roots multiplier_two roots) =
    lazard_section_five_cyclic_S omega roots.
Proof.
by rewrite /lazard_section_five_cyclic_S
  lazard_section_five_fourier_s_phi_psi_fixed.
Qed.

(** A pointwise fifth-power orbit is packaged as an actual tuple so later
    equalities remain constructive and need no function-extensionality
    principle. *)
Definition lazard_root_fourier_fifth_orbit_tuple
    (z : F) (roots : 5.-tuple F) : 4.-tuple F :=
  [tuple RP.lazard_root_fourier_fifth_orbit z roots i | i < 4].

Definition lazard_source_tuple_for_branch
    (source : 4.-tuple F) (branch : Q.lazard_sign_branch) : 4.-tuple F :=
  [tuple BE.lazard_source_for_branch (fun j => tnth source j) branch i
    | i < 4].

Lemma lazard_root_fourier_fifth_orbitE
    (z : F) (roots : 5.-tuple F) (i : 'I_4) :
  RP.lazard_root_fourier_fifth_orbit z roots i =
    BE.lazard_root_fourier_orbit z roots i ^+ 5.
Proof.
case: i=> [[|[|[|[|i]]]] hi] //=;
by rewrite /RP.lazard_root_fourier_fifth_orbit
  /BE.lazard_root_fourier_orbit.
Qed.

Lemma lazard_root_fourier_fifth_orbit_roots_for_branch
    (z : F) (roots : 5.-tuple F) (branch : Q.lazard_sign_branch) :
  lazard_root_fourier_fifth_orbit_tuple z
      (BE.lazard_roots_for_branch roots branch) =
    lazard_source_tuple_for_branch
      (lazard_root_fourier_fifth_orbit_tuple z roots) branch.
Proof.
apply: eq_from_tnth=> i.
case: branch;
case: i=> [[|[|[|[|i]]]] hi] //=;
rewrite /lazard_root_fourier_fifth_orbit_tuple
  /lazard_source_tuple_for_branch !tnth_mktuple
  /BE.lazard_source_for_branch
  /QB.lazard_negate_source /QB.lazard_rotate_source
  /QB.lazard_rotate_negate_source /P.p0 /P.p1 /P.p2 /P.p3 /=;
by rewrite !tnth_mktuple !lazard_root_fourier_fifth_orbitE
  ?BE.lazard_root_fourier_orbit_roots_for_branch.
Qed.

Theorem lazard_root_fourier_fifth_orbit_phi_psi_fixed
    (roots : 5.-tuple F) :
  lazard_root_fourier_fifth_orbit_tuple (omega ^+ 2)
      (TV.permute_quintic_roots multiplier_two roots) =
    lazard_root_fourier_fifth_orbit_tuple omega roots.
Proof.
apply: eq_from_tnth=> i.
by rewrite /lazard_root_fourier_fifth_orbit_tuple !tnth_mktuple
  !lazard_root_fourier_fifth_orbitE
  lazard_root_fourier_orbit_phi_psi_fixed.
Qed.

(** The combined action also fixes the actual quadratic triple. *)
Theorem lazard_root_quadratic_triple_phi_psi_fixed
    (roots : 5.-tuple F) :
  BE.lazard_root_quadratic_triple (omega ^+ 2)
      (TV.permute_quintic_roots multiplier_two roots) =
    BE.lazard_root_quadratic_triple omega roots.
Proof.
rewrite lazard_root_quadratic_triple_squared
  permute_multiplier_two_is_rotate_branch
  BE.lazard_root_quadratic_triple_roots_for_branch.
case: (BE.lazard_root_quadratic_triple omega roots)=> epsilon t u /=.
by rewrite !opprK.
Qed.

(** Standard projections are unchanged by every coherent simultaneous
    branch transformation of their quadratic and source inputs. *)
Lemma lazard_standard_projections_branch
    (v : Q.lazard_quadratic_triple F) (source : 'I_4 -> F)
    (branch : Q.lazard_sign_branch) (i : 'I_4) :
  P.lazard_standard_projections
      (Q.lazard_epsilon (Q.lazard_branch_triple v branch))
      (Q.lazard_t (Q.lazard_branch_triple v branch))
      (Q.lazard_u (Q.lazard_branch_triple v branch))
      (BE.lazard_source_for_branch source branch) i =
    P.lazard_standard_projections
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v) source i.
Proof.
case: v=> epsilon t u.
case: branch;
case: i=> [[|[|[|[|j]]]] hj] //=;
rewrite /BE.lazard_source_for_branch /Q.lazard_branch_triple
  /QB.lazard_negate_source /QB.lazard_rotate_source
  /QB.lazard_rotate_negate_source
  /P.lazard_standard_projections !P.lazard_sum_ord4
  /P.lazard_standard_projection_matrix
  /P.p0 /P.p1 /P.p2 /P.p3 !mxE /=;
finish_section_five_ring.
Qed.

(** The source in the literal forward order printed with the standard
    projection matrix: [[P1^5,P3^5,P4^5,P2^5]]. *)
Definition lazard_root_printed_section_five_forward_source
    (z : F) (roots : 5.-tuple F) : 4.-tuple F :=
  [tuple nth 0
    [:: RP.lazard_root_fourier_P1 z roots ^+ 5;
        RP.lazard_root_fourier_P3 z roots ^+ 5;
        RP.lazard_root_fourier_P4 z roots ^+ 5;
        RP.lazard_root_fourier_P2 z roots ^+ 5] i | i < 4].

(** This is the derived [phi]-orbit description of the literal forward
    source, not a second definition of it.  Each [phi] below is the actual
    multiplier-two permutation on root tuples, and the explicit nesting
    fixes the order as [[S, phi(S), phi^2(S), phi^3(S)]]. *)
Theorem lazard_root_printed_section_five_forward_source_eq_phi_iterates
    (z : F) (roots : 5.-tuple F) :
  lazard_root_printed_section_five_forward_source z roots =
    [tuple nth 0
      [:: RP.lazard_root_fourier_P1 z roots ^+ 5;
          RP.lazard_root_fourier_P1 z
            (TV.permute_quintic_roots multiplier_two roots) ^+ 5;
          RP.lazard_root_fourier_P1 z
            (TV.permute_quintic_roots multiplier_two
              (TV.permute_quintic_roots multiplier_two roots)) ^+ 5;
          RP.lazard_root_fourier_P1 z
            (TV.permute_quintic_roots multiplier_two
              (TV.permute_quintic_roots multiplier_two
                (TV.permute_quintic_roots multiplier_two roots))) ^+ 5]
      i | i < 4].
Proof.
have hphi (r : 5.-tuple F) :
    lazard_root_fourier_fifth_orbit_tuple z
        (TV.permute_quintic_roots multiplier_two r) =
      lazard_source_tuple_for_branch
        (lazard_root_fourier_fifth_orbit_tuple z r)
        Q.LazardBranchRotate.
  rewrite permute_multiplier_two_is_rotate_branch.
  exact: lazard_root_fourier_fifth_orbit_roots_for_branch.
have hphi2 :
    lazard_root_fourier_fifth_orbit_tuple z
        (TV.permute_quintic_roots multiplier_two
          (TV.permute_quintic_roots multiplier_two roots)) =
      lazard_source_tuple_for_branch
        (lazard_source_tuple_for_branch
          (lazard_root_fourier_fifth_orbit_tuple z roots)
          Q.LazardBranchRotate) Q.LazardBranchRotate.
  transitivity
    (lazard_source_tuple_for_branch
      (lazard_root_fourier_fifth_orbit_tuple z
        (TV.permute_quintic_roots multiplier_two roots))
      Q.LazardBranchRotate).
  - exact: hphi _.
  - by rewrite hphi.
have hphi3 :
    lazard_root_fourier_fifth_orbit_tuple z
        (TV.permute_quintic_roots multiplier_two
          (TV.permute_quintic_roots multiplier_two
            (TV.permute_quintic_roots multiplier_two roots))) =
      lazard_source_tuple_for_branch
        (lazard_source_tuple_for_branch
          (lazard_source_tuple_for_branch
            (lazard_root_fourier_fifth_orbit_tuple z roots)
            Q.LazardBranchRotate) Q.LazardBranchRotate)
        Q.LazardBranchRotate.
  transitivity
    (lazard_source_tuple_for_branch
      (lazard_root_fourier_fifth_orbit_tuple z
        (TV.permute_quintic_roots multiplier_two
          (TV.permute_quintic_roots multiplier_two roots)))
      Q.LazardBranchRotate).
  - exact: hphi _.
  - by rewrite hphi2.
have hs1 :
    RP.lazard_root_fourier_P1 z
        (TV.permute_quintic_roots multiplier_two roots) ^+ 5 =
      RP.lazard_root_fourier_P3 z roots ^+ 5.
  have h := congr1 (fun source : 4.-tuple F => tnth source P.p0)
    (hphi roots).
  move: h.
  by rewrite /lazard_root_fourier_fifth_orbit_tuple
    /lazard_source_tuple_for_branch !tnth_mktuple
    /BE.lazard_source_for_branch /QB.lazard_rotate_source
    !tnth_mktuple /RP.lazard_root_fourier_fifth_orbit
    /P.p0 /P.p1 /P.p2 /P.p3 /=.
have hs2 :
    RP.lazard_root_fourier_P1 z
        (TV.permute_quintic_roots multiplier_two
          (TV.permute_quintic_roots multiplier_two roots)) ^+ 5 =
      RP.lazard_root_fourier_P4 z roots ^+ 5.
  have h := congr1 (fun source : 4.-tuple F => tnth source P.p0) hphi2.
  move: h.
  by rewrite /lazard_root_fourier_fifth_orbit_tuple
    /lazard_source_tuple_for_branch !tnth_mktuple
    /BE.lazard_source_for_branch /QB.lazard_rotate_source
    !tnth_mktuple /RP.lazard_root_fourier_fifth_orbit
    /P.p0 /P.p1 /P.p2 /P.p3 /=.
have hs3 :
    RP.lazard_root_fourier_P1 z
        (TV.permute_quintic_roots multiplier_two
          (TV.permute_quintic_roots multiplier_two
            (TV.permute_quintic_roots multiplier_two roots))) ^+ 5 =
      RP.lazard_root_fourier_P2 z roots ^+ 5.
  have h := congr1 (fun source : 4.-tuple F => tnth source P.p0) hphi3.
  move: h.
  by rewrite /lazard_root_fourier_fifth_orbit_tuple
    /lazard_source_tuple_for_branch !tnth_mktuple
    /BE.lazard_source_for_branch /QB.lazard_rotate_source
    !tnth_mktuple /RP.lazard_root_fourier_fifth_orbit
    /P.p0 /P.p1 /P.p2 /P.p3 /=.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|j]]]] hj] //=;
rewrite /lazard_root_printed_section_five_forward_source !tnth_mktuple /=.
- reflexivity.
- exact: esym hs1.
- exact: esym hs2.
- exact: esym hs3.
Qed.

(** The literal printed standard tuple, using both the printed source order
    and the earlier printed sign [U_printed]. *)
Definition lazard_root_printed_section_five_projection_values
    (z : F) (roots : 5.-tuple F) : 4.-tuple F :=
  let source := lazard_root_printed_section_five_forward_source z roots in
  [tuple P.lazard_standard_projections
      (RR.lazard_root_epsilon z roots) (RR.lazard_root_T z roots)
      (RR.lazard_root_printed_U z roots)
      (fun j => tnth source j) i | i < 4].

Definition lazard_negate_fourth_projection_tuple
    (values : 4.-tuple F) : 4.-tuple F :=
  [tuple nth 0
    [:: tnth values P.p0; tnth values P.p1; tnth values P.p2;
        - tnth values P.p3] i | i < 4].

(** The four metacyclic projections formed from the actual root data and
    Figure 3's formula-sign convention [U_formula = -U_printed]. *)
Definition lazard_root_formula_convention_projection_values
    (z : F) (roots : 5.-tuple F) : 4.-tuple F :=
  let v := BE.lazard_root_quadratic_triple z roots in
  let source := lazard_root_fourier_fifth_orbit_tuple z roots in
  [tuple P.lazard_standard_projections
      (Q.lazard_epsilon v) (Q.lazard_t v) (Q.lazard_u v)
      (fun j => tnth source j) i | i < 4].

(** This proves, rather than merely records in prose, the exact comparison
    with the literal printed tuple: [[I1,I2,I3,-I4]]. *)
Theorem
    lazard_root_formula_convention_projection_values_eq_printed_I1_I2_I3_neg_I4
    (z : F) (roots : 5.-tuple F) :
  lazard_root_formula_convention_projection_values z roots =
    lazard_negate_fourth_projection_tuple
      (lazard_root_printed_section_five_projection_values z roots).
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|j]]]] hj] //=;
rewrite /lazard_root_formula_convention_projection_values
  /lazard_root_printed_section_five_projection_values
  /lazard_negate_fourth_projection_tuple
  /lazard_root_printed_section_five_forward_source
  /lazard_root_fourier_fifth_orbit_tuple
  /BE.lazard_root_quadratic_triple
  /RP.lazard_root_fourier_fifth_orbit
  /RR.lazard_root_formula_U
  /P.lazard_standard_projections
  /P.lazard_standard_projection_matrix
  /P.p0 /P.p1 /P.p2 /P.p3 ?mxE ?tnth_mktuple /=;
rewrite !P.lazard_sum_ord4 !mxE !tnth_mktuple /=;
finish_section_five_ring.
Qed.

Theorem lazard_root_formula_convention_projection_values_phi_fixed
    (z : F) (roots : 5.-tuple F) :
  lazard_root_formula_convention_projection_values z
      (TV.permute_quintic_roots multiplier_two roots) =
    lazard_root_formula_convention_projection_values z roots.
Proof.
rewrite permute_multiplier_two_is_rotate_branch.
apply: eq_from_tnth=> i.
rewrite /lazard_root_formula_convention_projection_values ?tnth_mktuple
  BE.lazard_root_quadratic_triple_roots_for_branch
  lazard_root_fourier_fifth_orbit_roots_for_branch
  /lazard_source_tuple_for_branch ?tnth_mktuple.
rewrite /P.lazard_standard_projections.
under [LHS] eq_bigr => j _ do rewrite tnth_mktuple.
exact: lazard_standard_projections_branch.
Qed.

Theorem lazard_root_formula_convention_projection_values_phi_psi_fixed
    (roots : 5.-tuple F) :
  lazard_root_formula_convention_projection_values (omega ^+ 2)
      (TV.permute_quintic_roots multiplier_two roots) =
    lazard_root_formula_convention_projection_values omega roots.
Proof.
apply: eq_from_tnth=> i.
by rewrite /lazard_root_formula_convention_projection_values !tnth_mktuple
  lazard_root_quadratic_triple_phi_psi_fixed
  lazard_root_fourier_fifth_orbit_phi_psi_fixed.
Qed.

(** Close the action-specific section before proving generator-independence.
    This makes the preceding equivariance theorems genuinely polymorphic in
    the primitive fifth root, so they can be instantiated at an arbitrary
    primitive generator below. *)
End CombinedAction.

(** If an expression is [phi]-invariant at every primitive generator and
    fixed by [phi o psi] at the chosen [omega], then it is unchanged by
    [omega -> omega^2]. *)
Theorem lazard_omega_squared_independent_of_phi_invariant
    (F : fieldType) (omega : F)
    (omega_primitive : 5.-primitive_root omega)
    (A : Type) (I : F -> 5.-tuple F -> A)
    (I_phi : forall z : F, 5.-primitive_root z -> forall roots,
      I z (TV.permute_quintic_roots multiplier_two roots) = I z roots)
    (I_phi_psi : forall roots,
      I (omega ^+ 2) (TV.permute_quintic_roots multiplier_two roots) =
        I omega roots)
    (roots : 5.-tuple F) :
  I (omega ^+ 2) roots = I omega roots.
Proof.
have omega_squared_primitive : 5.-primitive_root (omega ^+ 2) :=
  lazard_primitive_fifth_squared omega_primitive.
rewrite -(I_phi (omega ^+ 2) omega_squared_primitive roots).
exact: I_phi_psi roots.
Qed.

(** Independence under squaring at every primitive fifth-root generator
    implies independence from the choice of any primitive generator. *)
Theorem lazard_all_primitive_fifth_roots_independent
    (F : fieldType) (omega : F)
    (omega_primitive : 5.-primitive_root omega)
    (A : Type) (I : F -> 5.-tuple F -> A)
    (I_squared : forall z : F, 5.-primitive_root z -> forall roots,
      I (z ^+ 2) roots = I z roots)
    (z : F) (z_primitive : 5.-primitive_root z)
    (roots : 5.-tuple F) :
  I z roots = I omega roots.
Proof.
have omega_squared_primitive : 5.-primitive_root (omega ^+ 2) :=
  lazard_primitive_fifth_squared omega_primitive.
have omega_fourth_primitive : 5.-primitive_root (omega ^+ 4).
  by rewrite (prim_root_exp_coprime 4 omega_primitive).
have [-> | [-> | [-> | ->]]] :=
  @lazard_primitive_fifth_root_cases
    F omega omega_primitive z z_primitive.
- reflexivity.
- exact: I_squared omega omega_primitive roots.
- transitivity (I (omega ^+ 4) roots).
  + rewrite -(RP.lazard_primitive_fifth_power8 omega_primitive)
      (@exprM F omega 4 2).
    exact: I_squared (omega ^+ 4) omega_fourth_primitive roots.
  + transitivity (I (omega ^+ 2) roots).
    * rewrite (@exprM F omega 2 2).
      exact: I_squared (omega ^+ 2) omega_squared_primitive roots.
    * exact: I_squared omega omega_primitive roots.
- transitivity (I (omega ^+ 2) roots).
  + rewrite (@exprM F omega 2 2).
    exact: I_squared (omega ^+ 2) omega_squared_primitive roots.
  + exact: I_squared omega omega_primitive roots.
Qed.

(** The formula-convention projection tuple is therefore independent of
    the primitive-generator change [omega -> omega^2]. *)
Theorem lazard_root_formula_convention_projection_values_squared
    (F : fieldType) (omega : F)
    (omega_primitive : 5.-primitive_root omega)
    (roots : 5.-tuple F) :
  lazard_root_formula_convention_projection_values (omega ^+ 2) roots =
    lazard_root_formula_convention_projection_values omega roots.
Proof.
eapply (@lazard_omega_squared_independent_of_phi_invariant
  F omega omega_primitive (4.-tuple F)
  (@lazard_root_formula_convention_projection_values F)).
- move=> z z_primitive r.
  exact: (@lazard_root_formula_convention_projection_values_phi_fixed F z r).
- exact: (@lazard_root_formula_convention_projection_values_phi_psi_fixed
    F omega omega_primitive).
Qed.

(** Consequently the formula-convention projection tuple is independent
    of every choice of primitive fifth-root generator. *)
Theorem lazard_root_formula_convention_projection_values_all_primitive
    (F : fieldType) (omega : F)
    (omega_primitive : 5.-primitive_root omega)
    (z : F) (z_primitive : 5.-primitive_root z)
    (roots : 5.-tuple F) :
  lazard_root_formula_convention_projection_values z roots =
    lazard_root_formula_convention_projection_values omega roots.
Proof.
apply: (@lazard_all_primitive_fifth_roots_independent
  F omega omega_primitive (4.-tuple F)
  (@lazard_root_formula_convention_projection_values F)
  (fun w w_primitive r =>
    @lazard_root_formula_convention_projection_values_squared
      F w w_primitive r)
  z z_primitive roots).
Qed.

Print Assumptions lazard_section_five_phi_psi_commute.
Print Assumptions lazard_primitive_fifth_root_cases.
Print Assumptions lazard_root_T_phi_eq_neg_printed_U.
Print Assumptions lazard_root_printed_U_phi_eq_T.
Print Assumptions lazard_section_five_fourier_s_o0_eq_zero.
Print Assumptions lazard_section_five_cyclic_S_five_cycle_fixed.
Print Assumptions lazard_section_five_x0_recovery_scaled.
Print Assumptions lazard_section_five_x0_recovery.
Print Assumptions lazard_root_fourier_orbit_squared.
Print Assumptions lazard_root_fourier_orbit_phi_psi_fixed.
Print Assumptions lazard_section_five_fourier_s_phi_psi_fixed.
Print Assumptions lazard_section_five_cyclic_S_phi_psi_fixed.
Print Assumptions lazard_root_quadratic_triple_phi_psi_fixed.
Print Assumptions lazard_root_fourier_fifth_orbit_phi_psi_fixed.
Print Assumptions lazard_omega_squared_independent_of_phi_invariant.
Print Assumptions lazard_all_primitive_fifth_roots_independent.
Print Assumptions
  lazard_root_formula_convention_projection_values_eq_printed_I1_I2_I3_neg_I4.
Print Assumptions
  lazard_root_formula_convention_projection_values_phi_fixed.
Print Assumptions
  lazard_root_formula_convention_projection_values_phi_psi_fixed.
Print Assumptions
  lazard_root_formula_convention_projection_values_squared.
Print Assumptions
  lazard_root_formula_convention_projection_values_all_primitive.

End PolynomialFormulasLazardQuinticSectionFiveCombinedAction.
