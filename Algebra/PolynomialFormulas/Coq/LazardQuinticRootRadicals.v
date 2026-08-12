From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The root-level nonvanishing facts used by Lazard's quintic formula.
    This file deliberately stops before the coefficient formulas [D]--[K]:
    it only treats an ordered tuple of five roots and the three raw products
    that occur in the first radical layer. *)
Module PolynomialFormulasLazardQuinticRootRadicals.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.

Section RootProducts.

Variable F : fieldType.

(** Lazard's first cyclic root-difference product [T']. *)
Definition lazard_root_T_prime (roots : 5.-tuple F) : F :=
  (tnth roots o0 - tnth roots o1) *
  (tnth roots o1 - tnth roots o2) *
  (tnth roots o2 - tnth roots o3) *
  (tnth roots o3 - tnth roots o4) *
  (tnth roots o4 - tnth roots o0).

(** Lazard's second cyclic root-difference product [U']. *)
Definition lazard_root_U_prime (roots : 5.-tuple F) : F :=
  (tnth roots o0 - tnth roots o2) *
  (tnth roots o1 - tnth roots o3) *
  (tnth roots o2 - tnth roots o4) *
  (tnth roots o3 - tnth roots o0) *
  (tnth roots o4 - tnth roots o1).

(** The five linear factors in Lazard's epsilon invariant, without its
    nonzero fifth-root-of-unity coefficient. *)
Definition lazard_epsilon_product (roots : 5.-tuple F) : F :=
  (tnth roots o1 - tnth roots o2 - tnth roots o3 + tnth roots o4) *
  (tnth roots o2 - tnth roots o3 - tnth roots o4 + tnth roots o0) *
  (tnth roots o3 - tnth roots o4 - tnth roots o0 + tnth roots o1) *
  (tnth roots o4 - tnth roots o0 - tnth roots o1 + tnth roots o2) *
  (tnth roots o0 - tnth roots o1 - tnth roots o2 + tnth roots o3).

Lemma lazard_root_sub_neq0 (roots : 5.-tuple F)
    (hroots : injective (tnth roots)) (i j : 'I_5) :
  i != j -> tnth roots i - tnth roots j != 0.
Proof.
by move=> hij; rewrite subr_eq0 (inj_eq hroots).
Qed.

Lemma lazard_root_T_prime_neq0 (roots : 5.-tuple F)
    (hroots : injective (tnth roots)) :
  lazard_root_T_prime roots != 0.
Proof.
have h01 : tnth roots o0 - tnth roots o1 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h12 : tnth roots o1 - tnth roots o2 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h23 : tnth roots o2 - tnth roots o3 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h34 : tnth roots o3 - tnth roots o4 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h40 : tnth roots o4 - tnth roots o0 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
rewrite /lazard_root_T_prime.
exact: mulf_neq0 (mulf_neq0 (mulf_neq0 (mulf_neq0 h01 h12) h23) h34) h40.
Qed.

Lemma lazard_root_U_prime_neq0 (roots : 5.-tuple F)
    (hroots : injective (tnth roots)) :
  lazard_root_U_prime roots != 0.
Proof.
have h02 : tnth roots o0 - tnth roots o2 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h13 : tnth roots o1 - tnth roots o3 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h24 : tnth roots o2 - tnth roots o4 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h30 : tnth roots o3 - tnth roots o0 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
have h41 : tnth roots o4 - tnth roots o1 != 0.
  by rewrite subr_eq0 (inj_eq hroots).
rewrite /lazard_root_U_prime.
exact: mulf_neq0 (mulf_neq0 (mulf_neq0 (mulf_neq0 h02 h13) h24) h30) h41.
Qed.

(** A local bridge exposing MathComp's packed ring operations to the
    standard [ring] tactic. *)
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

Lemma ring_addE (x y : F) : x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma ring_mulE (x y : F) : x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma ring_subE (x y : F) : x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma ring_oppE (x : F) : - x = ring_opp x. Proof. reflexivity. Qed.
Lemma ring_zeroE : (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma ring_oneE : @GRing.one F = ring_one. Proof. reflexivity. Qed.

Lemma lazard_mathcomp_ring_theory :
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

Add Ring lazard_quintic_ring : lazard_mathcomp_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_three_natrE : (3%:R : F) = 1 + 1 + 1.
Proof.
rewrite -lazard_two_natrE.
exact: (@natrD F 2 1).
Qed.

Lemma lazard_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_three_natrE.
exact: (@natrD F 3 1).
Qed.

Lemma lazard_five_natrE : (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_four_natrE.
exact: (@natrD F 4 1).
Qed.

Lemma lazard_eight_natrE :
    (8%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
Proof.
have h7 : (7%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1.
  have h6 : (6%:R : F) = 1 + 1 + 1 + 1 + 1 + 1.
    rewrite -lazard_five_natrE.
    exact: (@natrD F 5 1).
  rewrite -h6.
  exact: (@natrD F 6 1).
rewrite -h7.
exact: (@natrD F 7 1).
Qed.

Lemma lazard_nine_natrE : (9%:R : F) = 8%:R + 1.
Proof. exact: (@natrD F 8 1). Qed.

Lemma lazard_expr3E (x : F) : x ^+ 3 = x * x * x.
Proof. by rewrite exprSr expr2. Qed.

Lemma lazard_expr4E (x : F) : x ^+ 4 = x * x * x * x.
Proof. by rewrite exprSr lazard_expr3E. Qed.

Lemma lazard_expr5E (x : F) : x ^+ 5 = x * x * x * x * x.
Proof. by rewrite exprSr lazard_expr4E. Qed.

Lemma lazard_expr6E (x : F) : x ^+ 6 = x * x * x * x * x * x.
Proof. by rewrite exprSr lazard_expr5E. Qed.

Lemma lazard_expr7E (x : F) : x ^+ 7 = x * x * x * x * x * x * x.
Proof. by rewrite exprSr lazard_expr6E. Qed.

Lemma lazard_expr8E (x : F) : x ^+ 8 = x * x * x * x * x * x * x * x.
Proof. by rewrite exprSr lazard_expr7E. Qed.

Ltac finish_lazard_ring :=
  repeat first
    [ rewrite lazard_two_natrE | rewrite lazard_three_natrE
    | rewrite lazard_four_natrE | rewrite lazard_five_natrE
    | rewrite lazard_eight_natrE | rewrite lazard_nine_natrE
    | rewrite expr2 | rewrite lazard_expr3E
    | rewrite lazard_expr4E | rewrite lazard_expr5E
    | rewrite lazard_expr6E | rewrite lazard_expr7E
    | rewrite lazard_expr8E
    | rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** The ordered Vandermonde product, oriented as [xi - xj] for [i < j]. *)
Definition lazard_root_vandermonde_delta (roots : 5.-tuple F) : F :=
  (tnth roots o0 - tnth roots o1) *
  (tnth roots o0 - tnth roots o2) *
  (tnth roots o0 - tnth roots o3) *
  (tnth roots o0 - tnth roots o4) *
  (tnth roots o1 - tnth roots o2) *
  (tnth roots o1 - tnth roots o3) *
  (tnth roots o1 - tnth roots o4) *
  (tnth roots o2 - tnth roots o3) *
  (tnth roots o2 - tnth roots o4) *
  (tnth roots o3 - tnth roots o4).

(** [T' U'] differs from the ordered Vandermonde product only by sign. *)
Lemma lazard_root_T_prime_mul_U_primeE (roots : 5.-tuple F) :
  lazard_root_T_prime roots * lazard_root_U_prime roots =
    - lazard_root_vandermonde_delta roots.
Proof.
rewrite /lazard_root_T_prime /lazard_root_U_prime
  /lazard_root_vandermonde_delta.
finish_lazard_ring.
Qed.

Lemma lazard_root_T_prime_mul_U_prime_sqE (roots : 5.-tuple F) :
  (lazard_root_T_prime roots * lazard_root_U_prime roots) ^+ 2 =
    lazard_root_vandermonde_delta roots ^+ 2.
Proof.
rewrite lazard_root_T_prime_mul_U_primeE expr2.
finish_lazard_ring.
Qed.

Lemma lazard_root_vandermonde_delta_neq0 (roots : 5.-tuple F)
    (hroots : injective (tnth roots)) :
  lazard_root_vandermonde_delta roots != 0.
Proof.
have hproduct :
    lazard_root_T_prime roots * lazard_root_U_prime roots != 0 :=
  mulf_neq0 (lazard_root_T_prime_neq0 hroots)
    (lazard_root_U_prime_neq0 hroots).
move: hproduct.
by rewrite lazard_root_T_prime_mul_U_primeE oppr_eq0.
Qed.

(** If one epsilon factor vanishes and the first three elementary
    symmetric relations have depressed-quintic coefficients [p,q], then
    the distinguished root satisfies Lazard's cubic obstruction. *)
Lemma lazard_epsilon_factor_zero_implies_cubic
    (a b c d e p q : F)
    (h1 : a + b + c + d + e = 0)
    (h2 : a*b + a*c + a*d + a*e + b*c + b*d + b*e +
      c*d + c*e + d*e = p)
    (h3 : a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e +
      b*c*d + b*c*e + b*d*e + c*d*e = - q)
    (hf : b - c - d + e = 0) :
  5%:R * a ^+ 3 + 4%:R * p * a + 8%:R * q = 0.
Proof.
have hS : a + 2%:R * b + 2%:R * e = 0.
  have hS_identity :
      a + 2%:R * b + 2%:R * e =
        (a + b + c + d + e) + (b - c - d + e).
    finish_lazard_ring.
  by rewrite hS_identity h1 hf addr0.
have hT : a + 2%:R * c + 2%:R * d = 0.
  have hT_identity :
      a + 2%:R * c + 2%:R * d =
        (a + b + c + d + e) - (b - c - d + e).
    finish_lazard_ring.
  by rewrite hT_identity h1 hf subrr.
have hu : 4%:R * (b * e + c * d) - 4%:R * p - 3%:R * a ^+ 2 = 0.
  have hu_identity :
      4%:R * (b * e + c * d) - 4%:R * p - 3%:R * a ^+ 2 =
        4%:R *
          ((a*b + a*c + a*d + a*e + b*c + b*d + b*e +
              c*d + c*e + d*e) - p) -
        (2%:R * a + 2%:R * c + 2%:R * d) *
          (a + 2%:R * b + 2%:R * e) -
        a * (a + 2%:R * c + 2%:R * d).
    finish_lazard_ring.
  by rewrite hu_identity h2 hS hT subrr !mulr0 !subr0.
have final_identity :
    5%:R * a ^+ 3 + 4%:R * p * a + 8%:R * q =
      8%:R *
        ((a*b*c + a*b*d + a*b*e + a*c*d + a*c*e + a*d*e +
            b*c*d + b*c*e + b*d*e + c*d*e) + q) -
      a * (4%:R * (b * e + c * d) - 4%:R * p - 3%:R * a ^+ 2) -
      (2%:R * a * (a + 2%:R * c + 2%:R * d) -
          2%:R * a ^+ 2 + 4%:R * c * d) *
        (a + 2%:R * b + 2%:R * e) -
      (- (2%:R * a ^+ 2) + 4%:R * b * e) *
        (a + 2%:R * c + 2%:R * d).
  finish_lazard_ring.
by rewrite final_identity h3 hu hS hT addNr !mulr0 !subr0.
Qed.

Lemma lazard_epsilon_product_neq0
    (roots : 5.-tuple F) (p q : F)
    (h1 : tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4 = 0)
    (h2 : tnth roots o0 * tnth roots o1 +
      tnth roots o0 * tnth roots o2 +
      tnth roots o0 * tnth roots o3 +
      tnth roots o0 * tnth roots o4 +
      tnth roots o1 * tnth roots o2 +
      tnth roots o1 * tnth roots o3 +
      tnth roots o1 * tnth roots o4 +
      tnth roots o2 * tnth roots o3 +
      tnth roots o2 * tnth roots o4 +
      tnth roots o3 * tnth roots o4 = p)
    (h3 : tnth roots o0 * tnth roots o1 * tnth roots o2 +
      tnth roots o0 * tnth roots o1 * tnth roots o3 +
      tnth roots o0 * tnth roots o1 * tnth roots o4 +
      tnth roots o0 * tnth roots o2 * tnth roots o3 +
      tnth roots o0 * tnth roots o2 * tnth roots o4 +
      tnth roots o0 * tnth roots o3 * tnth roots o4 +
      tnth roots o1 * tnth roots o2 * tnth roots o3 +
      tnth roots o1 * tnth roots o2 * tnth roots o4 +
      tnth roots o1 * tnth roots o3 * tnth roots o4 +
      tnth roots o2 * tnth roots o3 * tnth roots o4 = - q)
    (hcubic : forall k : 'I_5,
      5%:R * tnth roots k ^+ 3 + 4%:R * p * tnth roots k +
        8%:R * q != 0) :
  lazard_epsilon_product roots != 0.
Proof.
have hf0 :
    tnth roots o1 - tnth roots o2 - tnth roots o3 + tnth roots o4 != 0.
  apply/eqP=> hf0.
  have hzero0 :
      5%:R * tnth roots o0 ^+ 3 + 4%:R * p * tnth roots o0 +
        8%:R * q = 0 :=
    @lazard_epsilon_factor_zero_implies_cubic
      (tnth roots o0) (tnth roots o1) (tnth roots o2)
      (tnth roots o3) (tnth roots o4) p q h1 h2 h3 hf0.
  by move: (hcubic o0); rewrite hzero0 eqxx.
have hf1 :
    tnth roots o2 - tnth roots o3 - tnth roots o4 + tnth roots o0 != 0.
  apply/eqP=> hf1.
  have hzero1 :
      5%:R * tnth roots o1 ^+ 3 + 4%:R * p * tnth roots o1 +
        8%:R * q = 0.
    apply: (@lazard_epsilon_factor_zero_implies_cubic
      (tnth roots o1) (tnth roots o2) (tnth roots o3)
      (tnth roots o4) (tnth roots o0) p q).
    - rewrite -h1; finish_lazard_ring.
    - rewrite -h2; finish_lazard_ring.
    - rewrite -h3; finish_lazard_ring.
    - exact: hf1.
  by move: (hcubic o1); rewrite hzero1 eqxx.
have hf2 :
    tnth roots o3 - tnth roots o4 - tnth roots o0 + tnth roots o1 != 0.
  apply/eqP=> hf2.
  have hzero2 :
      5%:R * tnth roots o2 ^+ 3 + 4%:R * p * tnth roots o2 +
        8%:R * q = 0.
    apply: (@lazard_epsilon_factor_zero_implies_cubic
      (tnth roots o2) (tnth roots o3) (tnth roots o4)
      (tnth roots o0) (tnth roots o1) p q).
    - rewrite -h1; finish_lazard_ring.
    - rewrite -h2; finish_lazard_ring.
    - rewrite -h3; finish_lazard_ring.
    - exact: hf2.
  by move: (hcubic o2); rewrite hzero2 eqxx.
have hf3 :
    tnth roots o4 - tnth roots o0 - tnth roots o1 + tnth roots o2 != 0.
  apply/eqP=> hf3.
  have hzero3 :
      5%:R * tnth roots o3 ^+ 3 + 4%:R * p * tnth roots o3 +
        8%:R * q = 0.
    apply: (@lazard_epsilon_factor_zero_implies_cubic
      (tnth roots o3) (tnth roots o4) (tnth roots o0)
      (tnth roots o1) (tnth roots o2) p q).
    - rewrite -h1; finish_lazard_ring.
    - rewrite -h2; finish_lazard_ring.
    - rewrite -h3; finish_lazard_ring.
    - exact: hf3.
  by move: (hcubic o3); rewrite hzero3 eqxx.
have hf4 :
    tnth roots o0 - tnth roots o1 - tnth roots o2 + tnth roots o3 != 0.
  apply/eqP=> hf4.
  have hzero4 :
      5%:R * tnth roots o4 ^+ 3 + 4%:R * p * tnth roots o4 +
        8%:R * q = 0.
    apply: (@lazard_epsilon_factor_zero_implies_cubic
      (tnth roots o4) (tnth roots o0) (tnth roots o1)
      (tnth roots o2) (tnth roots o3) p q).
    - rewrite -h1; finish_lazard_ring.
    - rewrite -h2; finish_lazard_ring.
    - rewrite -h3; finish_lazard_ring.
    - exact: hf4.
  by move: (hcubic o4); rewrite hzero4 eqxx.
rewrite /lazard_epsilon_product.
exact: mulf_neq0 (mulf_neq0 (mulf_neq0 (mulf_neq0 hf0 hf1) hf2) hf3) hf4.
Qed.

(** ** Lazard's two [U] conventions and the [E/F/G] change of basis *)

(** The two coefficients in Lazard's linear change of basis. *)
Definition lazard_fifth_root_A (omega : F) : F :=
  omega - omega ^+ 4.

Definition lazard_fifth_root_B (omega : F) : F :=
  omega ^+ 2 - omega ^+ 3.

(** The coefficient multiplying the raw epsilon product. *)
Definition lazard_fifth_root_discriminant_factor (omega : F) : F :=
  omega + omega ^+ 4 - omega ^+ 2 - omega ^+ 3.

Definition lazard_root_fifth_cyclotomic_value (omega : F) : F :=
  omega ^+ 4 + omega ^+ 3 + omega ^+ 2 + omega + 1.

(** [T = A T' + B U']. *)
Definition lazard_root_T (omega : F) (roots : 5.-tuple F) : F :=
  lazard_fifth_root_A omega * lazard_root_T_prime roots +
    lazard_fifth_root_B omega * lazard_root_U_prime roots.

(** The [U = B T' - A U'] printed in the earlier change-of-basis
    display of Lazard's paper. *)
Definition lazard_root_printed_U (omega : F) (roots : 5.-tuple F) : F :=
  lazard_fifth_root_B omega * lazard_root_T_prime roots -
    lazard_fifth_root_A omega * lazard_root_U_prime roots.

(** The convention actually used by Figure 3 and the reconstruction
    formulas.  It is the negative of the earlier printed [U]. *)
Definition lazard_root_formula_U (omega : F) (roots : 5.-tuple F) : F :=
  - lazard_root_printed_U omega roots.

Lemma lazard_root_formula_U_eq_neg_printed_U omega roots :
  lazard_root_formula_U omega roots = - lazard_root_printed_U omega roots.
Proof. reflexivity. Qed.

Definition lazard_root_epsilon (omega : F) (roots : 5.-tuple F) : F :=
  lazard_fifth_root_discriminant_factor omega *
    lazard_epsilon_product roots.

(** A primitive fifth root satisfies the fifth cyclotomic equation. *)
Lemma lazard_primitive_fifth_root_cyclotomic (omega : F)
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_fifth_cyclotomic_value omega = 0.
Proof.
have homega5 : omega ^+ 5 = 1 := prim_expr_order omega_primitive.
have homega_ne1 : omega != 1.
  apply/eqP=> homega1.
  have hbad : (5 %| 1)%N.
    by rewrite (prim_order_dvd omega_primitive) homega1 expr1.
  by move: hbad.
have hfactor :
    (omega - 1) * lazard_root_fifth_cyclotomic_value omega =
      omega ^+ 5 - 1.
  rewrite /lazard_root_fifth_cyclotomic_value.
  finish_lazard_ring.
have hproduct :
    (omega - 1) * lazard_root_fifth_cyclotomic_value omega = 0.
  by rewrite hfactor homega5 subrr.
have hsub : omega - 1 != 0 by rewrite subr_eq0.
apply: (mulfI hsub).
by rewrite mulr0 hproduct.
Qed.

(** The four coefficient identities needed by the root-side [E/F/G]
    reductions.  Each is proved by an explicit multiple of [Phi_5]. *)
Lemma lazard_fifth_root_coeff_square_sum_of_cyclotomic (omega : F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_fifth_root_A omega ^+ 2 + lazard_fifth_root_B omega ^+ 2 =
    - 5%:R.
Proof.
have hid :
    lazard_fifth_root_A omega ^+ 2 + lazard_fifth_root_B omega ^+ 2 =
      - 5%:R +
      (omega ^+ 4 - omega ^+ 3 + omega ^+ 2 - 5%:R * omega + 5%:R) *
        lazard_root_fifth_cyclotomic_value omega.
  rewrite /lazard_fifth_root_A /lazard_fifth_root_B
    /lazard_root_fifth_cyclotomic_value.
  finish_lazard_ring.
by rewrite hid hcyclo mulr0 addr0.
Qed.

Lemma lazard_fifth_root_discriminant_factor_sq_of_cyclotomic (omega : F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_fifth_root_discriminant_factor omega ^+ 2 = 5%:R.
Proof.
have hid :
    lazard_fifth_root_discriminant_factor omega ^+ 2 =
      5%:R +
      (omega ^+ 4 - 3%:R * omega ^+ 3 + omega ^+ 2 +
        5%:R * omega - 5%:R) *
        lazard_root_fifth_cyclotomic_value omega.
  rewrite /lazard_fifth_root_discriminant_factor
    /lazard_root_fifth_cyclotomic_value.
  finish_lazard_ring.
by rewrite hid hcyclo mulr0 addr0.
Qed.

Lemma lazard_fifth_root_change_relation_of_cyclotomic (omega : F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_fifth_root_B omega ^+ 2 +
      lazard_fifth_root_A omega * lazard_fifth_root_B omega -
      lazard_fifth_root_A omega ^+ 2 = 0.
Proof.
have hid :
    lazard_fifth_root_B omega ^+ 2 +
        lazard_fifth_root_A omega * lazard_fifth_root_B omega -
        lazard_fifth_root_A omega ^+ 2 =
      (- omega ^+ 4 + 2%:R * omega ^+ 3 - omega ^+ 2) *
        lazard_root_fifth_cyclotomic_value omega.
  rewrite /lazard_fifth_root_A /lazard_fifth_root_B
    /lazard_root_fifth_cyclotomic_value.
  finish_lazard_ring.
by rewrite hid hcyclo mulr0.
Qed.

(** The second change-of-basis identity is the factor that makes Lazard's
    alternate projection nonsingular when the standard denominator
    vanishes. *)
Lemma lazard_fifth_root_change_mixed_relation_of_cyclotomic (omega : F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_fifth_root_B omega ^+ 2 -
      lazard_fifth_root_A omega ^+ 2 -
      4%:R * lazard_fifth_root_A omega * lazard_fifth_root_B omega =
    5%:R * lazard_fifth_root_discriminant_factor omega.
Proof.
have hid :
    lazard_fifth_root_B omega ^+ 2 -
        lazard_fifth_root_A omega ^+ 2 -
        4%:R * lazard_fifth_root_A omega * lazard_fifth_root_B omega =
      5%:R * lazard_fifth_root_discriminant_factor omega +
      (- 5%:R * omega + 9%:R * omega ^+ 2 -
        3%:R * omega ^+ 3 - omega ^+ 4) *
        lazard_root_fifth_cyclotomic_value omega.
  rewrite /lazard_fifth_root_A /lazard_fifth_root_B
    /lazard_fifth_root_discriminant_factor
    /lazard_root_fifth_cyclotomic_value.
  finish_lazard_ring.
by rewrite hid hcyclo mulr0 addr0.
Qed.

Lemma lazard_fifth_root_change_coeff_product_of_cyclotomic (omega : F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_fifth_root_A omega * lazard_fifth_root_B omega =
    - lazard_fifth_root_discriminant_factor omega.
Proof.
have hid :
    lazard_fifth_root_A omega * lazard_fifth_root_B omega =
      - lazard_fifth_root_discriminant_factor omega +
      (omega ^+ 3 - 2%:R * omega ^+ 2 + omega) *
        lazard_root_fifth_cyclotomic_value omega.
  rewrite /lazard_fifth_root_A /lazard_fifth_root_B
    /lazard_fifth_root_discriminant_factor
    /lazard_root_fifth_cyclotomic_value.
  finish_lazard_ring.
by rewrite hid hcyclo mulr0 addr0.
Qed.

(** Root-side [E]: the quadratic norm is independent of the [U] sign. *)
Theorem lazard_root_E_change_of_basis (omega : F) (roots : 5.-tuple F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_T omega roots ^+ 2 +
      lazard_root_formula_U omega roots ^+ 2 =
    - 5%:R *
      (lazard_root_T_prime roots ^+ 2 + lazard_root_U_prime roots ^+ 2).
Proof.
have hsum := lazard_fifth_root_coeff_square_sum_of_cyclotomic hcyclo.
have hprinted :
    lazard_root_T omega roots ^+ 2 +
        lazard_root_printed_U omega roots ^+ 2 =
      (lazard_fifth_root_A omega ^+ 2 +
        lazard_fifth_root_B omega ^+ 2) *
      (lazard_root_T_prime roots ^+ 2 +
        lazard_root_U_prime roots ^+ 2).
  rewrite /lazard_root_T /lazard_root_printed_U.
  finish_lazard_ring.
rewrite /lazard_root_formula_U sqrrN hprinted hsum.
reflexivity.
Qed.

(** Root-side [F].  Squaring makes it insensitive to the paper's [U]
    sign discrepancy. *)
Theorem lazard_root_F_change_of_basis (omega : F) (roots : 5.-tuple F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_epsilon omega roots *
      (lazard_root_T omega roots ^+ 2 -
        lazard_root_formula_U omega roots ^+ 2) =
    - 5%:R * lazard_epsilon_product roots *
      (lazard_root_T_prime roots ^+ 2 +
        4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
Proof.
have hzero := lazard_fifth_root_change_relation_of_cyclotomic hcyclo.
have hab := lazard_fifth_root_change_coeff_product_of_cyclotomic hcyclo.
have hsquare :=
  lazard_fifth_root_discriminant_factor_sq_of_cyclotomic hcyclo.
have hdiff :
    lazard_root_T omega roots ^+ 2 -
        lazard_root_printed_U omega roots ^+ 2 =
      (lazard_fifth_root_A omega * lazard_fifth_root_B omega) *
      (lazard_root_T_prime roots ^+ 2 +
        4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
  have hid :
      lazard_root_T omega roots ^+ 2 -
          lazard_root_printed_U omega roots ^+ 2 =
        (lazard_fifth_root_A omega * lazard_fifth_root_B omega) *
          (lazard_root_T_prime roots ^+ 2 +
            4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
            lazard_root_U_prime roots ^+ 2) -
        (lazard_root_T_prime roots ^+ 2 -
          lazard_root_U_prime roots ^+ 2) *
          (lazard_fifth_root_B omega ^+ 2 +
            lazard_fifth_root_A omega * lazard_fifth_root_B omega -
            lazard_fifth_root_A omega ^+ 2).
    rewrite /lazard_root_T /lazard_root_printed_U.
    finish_lazard_ring.
  by rewrite hid hzero mulr0 subr0.
rewrite /lazard_root_formula_U sqrrN /lazard_root_epsilon hdiff hab.
have hfinal :
    lazard_fifth_root_discriminant_factor omega *
        lazard_epsilon_product roots *
        ((- lazard_fifth_root_discriminant_factor omega) *
          (lazard_root_T_prime roots ^+ 2 +
            4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
            lazard_root_U_prime roots ^+ 2)) =
      - (lazard_fifth_root_discriminant_factor omega ^+ 2) *
        lazard_epsilon_product roots *
        (lazard_root_T_prime roots ^+ 2 +
          4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
          lazard_root_U_prime roots ^+ 2).
  finish_lazard_ring.
by rewrite hfinal hsquare.
Qed.

(** Root-side [G] with the [U] printed earlier in the paper: its sign is
    the negative of the one used by Figure 3. *)
Theorem lazard_root_G_printed_change_of_basis
    (omega : F) (roots : 5.-tuple F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_epsilon omega roots * lazard_root_T omega roots *
      lazard_root_printed_U omega roots =
    - 5%:R * lazard_epsilon_product roots *
      (lazard_root_T_prime roots ^+ 2 -
        lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
Proof.
have hzero := lazard_fifth_root_change_relation_of_cyclotomic hcyclo.
have hab := lazard_fifth_root_change_coeff_product_of_cyclotomic hcyclo.
have hsquare :=
  lazard_fifth_root_discriminant_factor_sq_of_cyclotomic hcyclo.
have hprod :
    lazard_root_T omega roots * lazard_root_printed_U omega roots =
      (lazard_fifth_root_A omega * lazard_fifth_root_B omega) *
      (lazard_root_T_prime roots ^+ 2 -
        lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
  have hid :
      lazard_root_T omega roots * lazard_root_printed_U omega roots =
        (lazard_fifth_root_A omega * lazard_fifth_root_B omega) *
          (lazard_root_T_prime roots ^+ 2 -
            lazard_root_T_prime roots * lazard_root_U_prime roots -
            lazard_root_U_prime roots ^+ 2) +
        (lazard_root_T_prime roots * lazard_root_U_prime roots) *
          (lazard_fifth_root_B omega ^+ 2 +
            lazard_fifth_root_A omega * lazard_fifth_root_B omega -
            lazard_fifth_root_A omega ^+ 2).
    rewrite /lazard_root_T /lazard_root_printed_U.
    finish_lazard_ring.
  by rewrite hid hzero mulr0 addr0.
rewrite /lazard_root_epsilon -mulrA hprod hab.
have hfinal :
    lazard_fifth_root_discriminant_factor omega *
        lazard_epsilon_product roots *
        ((- lazard_fifth_root_discriminant_factor omega) *
          (lazard_root_T_prime roots ^+ 2 -
            lazard_root_T_prime roots * lazard_root_U_prime roots -
            lazard_root_U_prime roots ^+ 2)) =
      - (lazard_fifth_root_discriminant_factor omega ^+ 2) *
        lazard_epsilon_product roots *
        (lazard_root_T_prime roots ^+ 2 -
          lazard_root_T_prime roots * lazard_root_U_prime roots -
          lazard_root_U_prime roots ^+ 2).
  finish_lazard_ring.
by rewrite hfinal hsquare.
Qed.

(** Root-side [G] with the convention used by the formulas.  The extra
    negation exactly changes the preceding minus sign to the advertised
    positive sign. *)
Theorem lazard_root_G_formula_change_of_basis
    (omega : F) (roots : 5.-tuple F)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_epsilon omega roots * lazard_root_T omega roots *
      lazard_root_formula_U omega roots =
    5%:R * lazard_epsilon_product roots *
      (lazard_root_T_prime roots ^+ 2 -
        lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
Proof.
rewrite /lazard_root_formula_U mulrN
  (@lazard_root_G_printed_change_of_basis omega roots hcyclo).
finish_lazard_ring.
Qed.

(** Primitive-root corollaries package the cyclotomic hypothesis in the
    form used by the rest of the quintic development. *)
Corollary lazard_root_E_change_of_basis_primitive
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_T omega roots ^+ 2 +
      lazard_root_formula_U omega roots ^+ 2 =
    - 5%:R *
      (lazard_root_T_prime roots ^+ 2 + lazard_root_U_prime roots ^+ 2).
Proof.
exact: @lazard_root_E_change_of_basis omega roots
  (lazard_primitive_fifth_root_cyclotomic omega_primitive).
Qed.

Corollary lazard_root_F_change_of_basis_primitive
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_epsilon omega roots *
      (lazard_root_T omega roots ^+ 2 -
        lazard_root_formula_U omega roots ^+ 2) =
    - 5%:R * lazard_epsilon_product roots *
      (lazard_root_T_prime roots ^+ 2 +
        4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
Proof.
exact: @lazard_root_F_change_of_basis omega roots
  (lazard_primitive_fifth_root_cyclotomic omega_primitive).
Qed.

Corollary lazard_root_G_formula_change_of_basis_primitive
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega) :
  lazard_root_epsilon omega roots * lazard_root_T omega roots *
      lazard_root_formula_U omega roots =
    5%:R * lazard_epsilon_product roots *
      (lazard_root_T_prime roots ^+ 2 -
        lazard_root_T_prime roots * lazard_root_U_prime roots -
        lazard_root_U_prime roots ^+ 2).
Proof.
exact: @lazard_root_G_formula_change_of_basis omega roots
  (lazard_primitive_fifth_root_cyclotomic omega_primitive).
Qed.

End RootProducts.

End PolynomialFormulasLazardQuinticRootRadicals.
