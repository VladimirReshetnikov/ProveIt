From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaOrbit QuinticThetaValues.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Chapman's no-collision argument for the six scalar theta values.  The
    proof in this file is deliberately independent of the construction of a
    splitting field and of the later Galois-group criterion. *)
Module PolynomialFormulasQuinticChapman.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticThetaOrbit.
Import PolynomialFormulasQuinticThetaValues.

Local Open Scope ring_scope.

Section AlgebraicIdentities.

Variable R : comNzRingType.

(** The familiar ten-term expression represented by the theta exponent
    table. *)
Definition quintic_theta_formula (roots : 5.-tuple R) : R :=
  tnth roots o0 ^+ 2 * tnth roots o1 * tnth roots o4 +
  tnth roots o0 ^+ 2 * tnth roots o2 * tnth roots o3 +
  tnth roots o1 ^+ 2 * tnth roots o0 * tnth roots o2 +
  tnth roots o1 ^+ 2 * tnth roots o3 * tnth roots o4 +
  tnth roots o2 ^+ 2 * tnth roots o0 * tnth roots o4 +
  tnth roots o2 ^+ 2 * tnth roots o1 * tnth roots o3 +
  tnth roots o3 ^+ 2 * tnth roots o0 * tnth roots o1 +
  tnth roots o3 ^+ 2 * tnth roots o2 * tnth roots o4 +
  tnth roots o4 ^+ 2 * tnth roots o0 * tnth roots o3 +
  tnth roots o4 ^+ 2 * tnth roots o1 * tnth roots o2.

(** A local bridge exposing MathComp's packed commutative-ring operations to
    the standard [ring] tactic. *)
Let ring_carrier : Type := R.
Local Definition ring_zero : ring_carrier := @GRing.zero R.
Local Definition ring_one : ring_carrier := @GRing.one R.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add R.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul R.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp R.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma ring_addE (x y : R) : x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma ring_mulE (x y : R) : x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma ring_subE (x y : R) : x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma ring_oppE (x : R) : - x = ring_opp x. Proof. reflexivity. Qed.
Lemma ring_zeroE : (0 : R) = ring_zero. Proof. reflexivity. Qed.
Lemma ring_oneE : @GRing.one R = ring_one. Proof. reflexivity. Qed.

Lemma mathcomp_ring_theory :
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

Add Ring quintic_chapman_ring : mathcomp_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_quintic_ring :=
  repeat first
    [ rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma quintic_table_value_thetaE roots :
  quintic_table_value roots theta_exponent_table =
    quintic_theta_formula roots.
Proof.
rewrite /quintic_table_value /theta_exponent_table
  /quintic_monomial_value /quintic_theta_formula /=.
rewrite !big_cons big_nil !big_ord_recl !big_ord0 /=.
rewrite ?mulr1 ?mul1r ?expr0 ?expr1 ?addr0.
have h0 : (@ord0 4) = o0 by apply/val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = o1 by apply/val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = o2
  by apply/val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = o3
  by apply/val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0)))) = o4
  by apply/val_inj.
rewrite ?h4 ?h3 ?h2 ?h1 ?h0 /=.
rewrite /o0 /o1 /o2 /o3 /o4 /=.
rewrite !expr2.
finish_quintic_ring.
Qed.

Lemma quintic_table_image_valueE roots s :
  quintic_table_value roots (theta_table_image s) =
    quintic_theta_formula (permute_quintic_roots s roots).
Proof.
rewrite /theta_table_image -quintic_table_value_permute.
exact: quintic_table_value_thetaE.
Qed.

Lemma quintic_theta_value_formulaE roots i :
  quintic_theta_value roots i =
    quintic_theta_formula
      (permute_quintic_roots ((representative i)^-1)%g roots).
Proof. exact: quintic_table_image_valueE. Qed.

Lemma three_cycle_o0E : three_cycle o0 = o2.
Proof. by rewrite /three_cycle permM !tpermL. Qed.

Lemma three_cycle_o1E : three_cycle o1 = o0.
Proof.
rewrite /three_cycle permM tpermR.
by rewrite (tpermD (x := o1) (y := o2) (z := o0)).
Qed.

Lemma three_cycle_o2E : three_cycle o2 = o1.
Proof.
rewrite /three_cycle permM.
by rewrite (tpermD (x := o0) (y := o1) (z := o2)) // tpermR.
Qed.

Lemma three_cycle_o3E : three_cycle o3 = o3.
Proof.
rewrite /three_cycle permM.
by rewrite (tpermD (x := o0) (y := o1) (z := o3)) //
  (tpermD (x := o1) (y := o2) (z := o3)).
Qed.

Lemma three_cycle_o4E : three_cycle o4 = o4.
Proof.
rewrite /three_cycle permM.
by rewrite (tpermD (x := o0) (y := o1) (z := o4)) //
  (tpermD (x := o1) (y := o2) (z := o4)).
Qed.

Lemma three_cycle_inv_o0E : (three_cycle^-1)%g o0 = o1.
Proof. exact: inverse_imageE three_cycle_o1E. Qed.

Lemma three_cycle_inv_o1E : (three_cycle^-1)%g o1 = o2.
Proof. exact: inverse_imageE three_cycle_o2E. Qed.

Lemma three_cycle_inv_o2E : (three_cycle^-1)%g o2 = o0.
Proof. exact: inverse_imageE three_cycle_o0E. Qed.

Lemma three_cycle_inv_o3E : (three_cycle^-1)%g o3 = o3.
Proof. exact: inverse_imageE three_cycle_o3E. Qed.

Lemma three_cycle_inv_o4E : (three_cycle^-1)%g o4 = o4.
Proof. exact: inverse_imageE three_cycle_o4E. Qed.

(** Chapman's first factorization.  The inverse appears first because the
    Coq value layer indexes theta by inverse coset representatives. *)
Lemma theta_formula_three_cycle_factor roots :
  quintic_theta_formula
      (permute_quintic_roots (three_cycle^-1)%g roots) -
    quintic_theta_formula
      (permute_quintic_roots three_cycle roots) =
  (tnth roots o0 - tnth roots o3) *
  (tnth roots o2 - tnth roots o4) *
    ((tnth roots o1 - tnth roots o0) *
       (tnth roots o1 - tnth roots o3) -
     (tnth roots o1 - tnth roots o2) *
       (tnth roots o1 - tnth roots o4)).
Proof.
rewrite /quintic_theta_formula !tnth_permute_quintic_roots.
rewrite !three_cycle_inv_o0E !three_cycle_inv_o1E
  !three_cycle_inv_o2E !three_cycle_inv_o3E !three_cycle_inv_o4E.
rewrite !three_cycle_o0E !three_cycle_o1E !three_cycle_o2E
  !three_cycle_o3E !three_cycle_o4E.
rewrite !expr2.
finish_quintic_ring.
Qed.

(** Chapman's second factorization, comparing the [(0 1)] and [(1 2)]
    conjugates. *)
Lemma theta_formula_swap_factor roots :
  quintic_theta_formula
      (permute_quintic_roots (tperm o0 o1) roots) -
    quintic_theta_formula
      (permute_quintic_roots (tperm o1 o2) roots) =
  (tnth roots o2 - tnth roots o3) *
  (tnth roots o0 - tnth roots o4) *
    ((tnth roots o1 - tnth roots o2) *
       (tnth roots o1 - tnth roots o3) -
     (tnth roots o1 - tnth roots o0) *
       (tnth roots o1 - tnth roots o4)).
Proof.
rewrite /quintic_theta_formula !tnth_permute_quintic_roots.
rewrite !tpermL !tpermR.
rewrite !(tpermD (x := o0) (y := o1)) //.
rewrite !(tpermD (x := o1) (y := o2)) //.
rewrite !expr2.
finish_quintic_ring.
Qed.

End AlgebraicIdentities.

Section CollisionAlgebra.

Variable F : fieldType.

Add Ring quintic_chapman_field_ring : (mathcomp_ring_theory F).

Ltac finish_quintic_field_ring :=
  repeat first
    [ rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (@ring_eq F lhs rhs)
  end;
  ring.

Definition theta_i0 : 'I_6 := @Ordinal 6 0 (erefl true).
Definition theta_i1 : 'I_6 := @Ordinal 6 1 (erefl true).
Definition theta_i2 : 'I_6 := @Ordinal 6 2 (erefl true).
Definition theta_i3 : 'I_6 := @Ordinal 6 3 (erefl true).
Definition theta_i4 : 'I_6 := @Ordinal 6 4 (erefl true).
Definition theta_i5 : 'I_6 := @Ordinal 6 5 (erefl true).

Lemma theta_value_12_factor (roots : 5.-tuple F) :
  quintic_theta_value roots theta_i1 -
      quintic_theta_value roots theta_i2 =
    (tnth roots o0 - tnth roots o3) *
    (tnth roots o2 - tnth roots o4) *
      ((tnth roots o1 - tnth roots o0) *
         (tnth roots o1 - tnth roots o3) -
       (tnth roots o1 - tnth roots o2) *
         (tnth roots o1 - tnth roots o4)).
Proof.
rewrite !quintic_theta_value_formulaE.
rewrite /theta_i1 /theta_i2 /representative /representative_table /= invgK.
exact: theta_formula_three_cycle_factor.
Qed.

Lemma theta_value_34_factor (roots : 5.-tuple F) :
  quintic_theta_value roots theta_i3 -
      quintic_theta_value roots theta_i4 =
    (tnth roots o2 - tnth roots o3) *
    (tnth roots o0 - tnth roots o4) *
      ((tnth roots o1 - tnth roots o2) *
         (tnth roots o1 - tnth roots o3) -
       (tnth roots o1 - tnth roots o0) *
         (tnth roots o1 - tnth roots o4)).
Proof.
rewrite !quintic_theta_value_formulaE.
rewrite /theta_i3 /theta_i4 /representative /representative_table /= !tpermV.
exact: theta_formula_swap_factor.
Qed.

Lemma injective_root_difference_neq0 (roots : 5.-tuple F)
    (hroots : injective (tnth roots)) i j :
  i != j -> tnth roots i - tnth roots j != 0.
Proof.
move=> hij; rewrite subr_eq0.
apply/negP=> /eqP hvalue.
have hindex : i = j by apply: hroots.
by move: hij; rewrite hindex eqxx.
Qed.

(** The algebraic heart of Chapman's argument: the two distinguished
    collisions make the second root the midpoint of both remaining pairs. *)
Lemma chapman_midpoints_of_collisions (roots : 5.-tuple F)
    (hroots : injective (tnth roots))
    (h12 : quintic_theta_value roots theta_i1 =
      quintic_theta_value roots theta_i2)
    (h34 : quintic_theta_value roots theta_i3 =
      quintic_theta_value roots theta_i4) :
  tnth roots o1 + tnth roots o1 = tnth roots o0 + tnth roots o2 /\
  tnth roots o1 + tnth roots o1 = tnth roots o3 + tnth roots o4.
Proof.
have h03 : tnth roots o0 - tnth roots o3 != 0 :=
  injective_root_difference_neq0 hroots (i := o0) (j := o3) isT.
have h24 : tnth roots o2 - tnth roots o4 != 0 :=
  injective_root_difference_neq0 hroots (i := o2) (j := o4) isT.
have h23 : tnth roots o2 - tnth roots o3 != 0 :=
  injective_root_difference_neq0 hroots (i := o2) (j := o3) isT.
have h04 : tnth roots o0 - tnth roots o4 != 0 :=
  injective_root_difference_neq0 hroots (i := o0) (j := o4) isT.
have h20 : tnth roots o2 - tnth roots o0 != 0 :=
  injective_root_difference_neq0 hroots (i := o2) (j := o0) isT.
have h43 : tnth roots o4 - tnth roots o3 != 0 :=
  injective_root_difference_neq0 hroots (i := o4) (j := o3) isT.
have hA :
    (tnth roots o1 - tnth roots o0) *
        (tnth roots o1 - tnth roots o3) -
      (tnth roots o1 - tnth roots o2) *
        (tnth roots o1 - tnth roots o4) = 0.
  have hprod :
      (tnth roots o0 - tnth roots o3) *
      (tnth roots o2 - tnth roots o4) *
        ((tnth roots o1 - tnth roots o0) *
           (tnth roots o1 - tnth roots o3) -
         (tnth roots o1 - tnth roots o2) *
           (tnth roots o1 - tnth roots o4)) = 0.
    by rewrite -theta_value_12_factor h12 subrr.
  have hprodb :
      (tnth roots o0 - tnth roots o3) *
      (tnth roots o2 - tnth roots o4) *
        ((tnth roots o1 - tnth roots o0) *
           (tnth roots o1 - tnth roots o3) -
         (tnth roots o1 - tnth roots o2) *
           (tnth roots o1 - tnth roots o4)) == 0.
    by apply/eqP.
  apply/eqP.
  by move: hprodb; rewrite !mulf_eq0 (negbTE h03) (negbTE h24) /=.
have hB :
    (tnth roots o1 - tnth roots o2) *
        (tnth roots o1 - tnth roots o3) -
      (tnth roots o1 - tnth roots o0) *
        (tnth roots o1 - tnth roots o4) = 0.
  have hprod :
      (tnth roots o2 - tnth roots o3) *
      (tnth roots o0 - tnth roots o4) *
        ((tnth roots o1 - tnth roots o2) *
           (tnth roots o1 - tnth roots o3) -
         (tnth roots o1 - tnth roots o0) *
           (tnth roots o1 - tnth roots o4)) = 0.
    by rewrite -theta_value_34_factor h34 subrr.
  have hprodb :
      (tnth roots o2 - tnth roots o3) *
      (tnth roots o0 - tnth roots o4) *
        ((tnth roots o1 - tnth roots o2) *
           (tnth roots o1 - tnth roots o3) -
         (tnth roots o1 - tnth roots o0) *
           (tnth roots o1 - tnth roots o4)) == 0.
    by apply/eqP.
  apply/eqP.
  by move: hprodb; rewrite !mulf_eq0 (negbTE h23) (negbTE h04) /=.
have hright_prod :
    (tnth roots o2 - tnth roots o0) *
      ((tnth roots o1 - tnth roots o3) +
       (tnth roots o1 - tnth roots o4)) = 0.
  have hid :
      (tnth roots o2 - tnth roots o0) *
        ((tnth roots o1 - tnth roots o3) +
         (tnth roots o1 - tnth roots o4)) =
      ((tnth roots o1 - tnth roots o0) *
          (tnth roots o1 - tnth roots o3) -
       (tnth roots o1 - tnth roots o2) *
          (tnth roots o1 - tnth roots o4)) -
      ((tnth roots o1 - tnth roots o2) *
          (tnth roots o1 - tnth roots o3) -
       (tnth roots o1 - tnth roots o0) *
          (tnth roots o1 - tnth roots o4)).
    finish_quintic_field_ring.
  by rewrite hid hA hB subrr.
have hleft_prod :
    (tnth roots o4 - tnth roots o3) *
      ((tnth roots o1 - tnth roots o0) +
       (tnth roots o1 - tnth roots o2)) = 0.
  have hid :
      (tnth roots o4 - tnth roots o3) *
        ((tnth roots o1 - tnth roots o0) +
         (tnth roots o1 - tnth roots o2)) =
      ((tnth roots o1 - tnth roots o0) *
          (tnth roots o1 - tnth roots o3) -
       (tnth roots o1 - tnth roots o2) *
          (tnth roots o1 - tnth roots o4)) +
      ((tnth roots o1 - tnth roots o2) *
          (tnth roots o1 - tnth roots o3) -
       (tnth roots o1 - tnth roots o0) *
          (tnth roots o1 - tnth roots o4)).
    finish_quintic_field_ring.
  by rewrite hid hA hB addr0.
have hright :
    (tnth roots o1 - tnth roots o3) +
      (tnth roots o1 - tnth roots o4) = 0.
  have hp :
      (tnth roots o2 - tnth roots o0) *
        ((tnth roots o1 - tnth roots o3) +
         (tnth roots o1 - tnth roots o4)) == 0.
    by apply/eqP.
  apply/eqP.
  by move: hp; rewrite mulf_eq0 (negbTE h20) /=.
have hleft :
    (tnth roots o1 - tnth roots o0) +
      (tnth roots o1 - tnth roots o2) = 0.
  have hp :
      (tnth roots o4 - tnth roots o3) *
        ((tnth roots o1 - tnth roots o0) +
         (tnth roots o1 - tnth roots o2)) == 0.
    by apply/eqP.
  apply/eqP.
  by move: hp; rewrite mulf_eq0 (negbTE h43) /=.
split.
- have hid :
      tnth roots o1 + tnth roots o1 -
        (tnth roots o0 + tnth roots o2) =
      (tnth roots o1 - tnth roots o0) +
        (tnth roots o1 - tnth roots o2).
    finish_quintic_field_ring.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  by rewrite hid hleft.
- have hid :
      tnth roots o1 + tnth roots o1 -
        (tnth roots o3 + tnth roots o4) =
      (tnth roots o1 - tnth roots o3) +
        (tnth roots o1 - tnth roots o4).
    finish_quintic_field_ring.
  apply/eqP; rewrite -subr_eq0; apply/eqP.
  by rewrite hid hright.
Qed.

Lemma five_natr_fieldE : (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
have h2 : (2%:R : F) = 1 + 1 := @natrD F 1 1.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -h2; exact: (@natrD F 2 1).
have h4 : (4%:R : F) = 1 + 1 + 1 + 1.
  rewrite -h3; exact: (@natrD F 3 1).
rewrite -h4.
exact: (@natrD F 4 1).
Qed.

Lemma chapman_five_mul_center (roots : 5.-tuple F)
    (hmid :
      tnth roots o1 + tnth roots o1 = tnth roots o0 + tnth roots o2 /\
      tnth roots o1 + tnth roots o1 = tnth roots o3 + tnth roots o4) :
  5%:R * tnth roots o1 =
    tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4.
Proof.
case: hmid=> hleft hright.
have hleft0 :
    tnth roots o1 + tnth roots o1 -
      (tnth roots o0 + tnth roots o2) = 0.
  by rewrite hleft subrr.
have hright0 :
    tnth roots o1 + tnth roots o1 -
      (tnth roots o3 + tnth roots o4) = 0.
  by rewrite hright subrr.
have hid :
    (1 + 1 + 1 + 1 + 1) * tnth roots o1 -
      (tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4) =
    (tnth roots o1 + tnth roots o1 -
      (tnth roots o0 + tnth roots o2)) +
    (tnth roots o1 + tnth roots o1 -
      (tnth roots o3 + tnth roots o4)).
  finish_quintic_field_ring.
apply/eqP; rewrite -subr_eq0; apply/eqP.
by rewrite five_natr_fieldE hid hleft0 hright0 add0r.
Qed.

Lemma chapman_five_mul_center_of_collisions (roots : 5.-tuple F)
    (hroots : injective (tnth roots))
    (h12 : quintic_theta_value roots theta_i1 =
      quintic_theta_value roots theta_i2)
    (h34 : quintic_theta_value roots theta_i3 =
      quintic_theta_value roots theta_i4) :
  5%:R * tnth roots o1 =
    tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4.
Proof.
apply: chapman_five_mul_center.
exact: chapman_midpoints_of_collisions hroots h12 h34.
Qed.

End CollisionAlgebra.

Section FiveCycleAction.

Variable R : fieldType.

(** In the inverse-representative indexing used by the Coq value layer, the
    standard five-cycle fixes index zero and cycles the other five indices in
    the order [1,4,3,2,5]. *)
Definition chapman_cycle_index_table : 6.-tuple 'I_6 :=
  [tuple theta_i0; theta_i4; theta_i5;
    theta_i2; theta_i3; theta_i1].

Definition chapman_cycle_index (i : 'I_6) : 'I_6 :=
  tnth chapman_cycle_index_table i.

Lemma chapman_cycle_index_i0 : chapman_cycle_index theta_i0 = theta_i0.
Proof. by []. Qed.

Lemma chapman_cycle_index_i1 : chapman_cycle_index theta_i1 = theta_i4.
Proof. by []. Qed.

Lemma chapman_cycle_index_i2 : chapman_cycle_index theta_i2 = theta_i5.
Proof. by []. Qed.

Lemma chapman_cycle_index_i3 : chapman_cycle_index theta_i3 = theta_i2.
Proof. by []. Qed.

Lemma chapman_cycle_index_i4 : chapman_cycle_index theta_i4 = theta_i3.
Proof. by []. Qed.

Lemma chapman_cycle_index_i5 : chapman_cycle_index theta_i5 = theta_i1.
Proof. by []. Qed.

Lemma ord6_cases (i : 'I_6) :
  i = theta_i0 \/ i = theta_i1 \/ i = theta_i2 \/
  i = theta_i3 \/ i = theta_i4 \/ i = theta_i5.
Proof.
case: i=> [[|[|[|[|[|[|n]]]]]]] hi; last by move: hi.
- left; by apply/val_inj.
- right; left; by apply/val_inj.
- right; right; left; by apply/val_inj.
- right; right; right; left; by apply/val_inj.
- right; right; right; right; left; by apply/val_inj.
- right; right; right; right; right; by apply/val_inj.
Qed.

Add Ring quintic_chapman_cycle_ring : (mathcomp_ring_theory R).

Ltac finish_quintic_cycle_ring :=
  repeat first
    [ rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (@ring_eq R lhs rhs)
  end;
  ring.

Lemma quintic_theta_value_five_cycle (roots : 5.-tuple R) i :
  quintic_theta_value (permute_quintic_roots five_cycle roots) i =
    quintic_theta_value roots (chapman_cycle_index i).
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite /chapman_cycle_index /chapman_cycle_index_table /=.
all: rewrite !quintic_theta_value_formulaE
  /representative /representative_table /= ?invg1 ?invgK ?tpermV ?perm1.
all: rewrite /quintic_theta_formula !tnth_permute_quintic_roots.
all: rewrite ?three_cycle_inv_o0E ?three_cycle_inv_o1E
  ?three_cycle_inv_o2E ?three_cycle_inv_o3E ?three_cycle_inv_o4E.
all: rewrite ?three_cycle_o0E ?three_cycle_o1E ?three_cycle_o2E
  ?three_cycle_o3E ?three_cycle_o4E.
all: rewrite ?five_cycle_o0 ?five_cycle_o1 ?five_cycle_o2
  ?five_cycle_o3 ?five_cycle_o4.
all: rewrite ?tpermL ?tpermR.
all: rewrite ?(tpermD (x := o0) (y := o1)) //.
all: rewrite ?(tpermD (x := o1) (y := o2)) //.
all: rewrite ?(tpermD (x := o0) (y := o2)) //.
all: rewrite ?perm1.
all: rewrite ?five_cycle_o0 ?five_cycle_o1 ?five_cycle_o2
  ?five_cycle_o3 ?five_cycle_o4.
all: rewrite ?expr2.
all: finish_quintic_cycle_ring.
Qed.

End FiveCycleAction.

#[local] Hint Rewrite chapman_cycle_index_i0 chapman_cycle_index_i1
  chapman_cycle_index_i2 chapman_cycle_index_i3 chapman_cycle_index_i4
  chapman_cycle_index_i5 : chapman_cycle.

Section CollisionPropagation.

Variable A : Type.

(** One collision propagated by the five-cycle contains both pairs used in
    the two Chapman factorizations. *)
Lemma five_cycle_collision_propagates (v : 'I_6 -> A)
    (hstep : forall i j, v i = v j ->
      v (chapman_cycle_index i) = v (chapman_cycle_index j))
    i j :
  i != j -> v i = v j ->
  v theta_i1 = v theta_i2 /\ v theta_i3 = v theta_i4.
Proof.
move=> hij h0.
have h1 := hstep _ _ h0.
have h2 := hstep _ _ h1.
have h3 := hstep _ _ h2.
have h4 := hstep _ _ h3.
case: (ord6_cases i)=> [hi|[hi|[hi|[hi|[hi|hi]]]]]; subst i.
all: case: (ord6_cases j)=> [hj|[hj|[hj|[hj|[hj|hj]]]]]; subst j.
all: autorewrite with chapman_cycle in h1, h2, h3, h4.
all: try by move: hij; rewrite eqxx.
all: split; congruence.
Qed.

End CollisionPropagation.

Section MapValues.

Variables (R S : comNzRingType) (f : {rmorphism R -> S}).

(** Theta evaluation commutes with arbitrary commutative-ring morphisms.
    Keeping the monomial and table layers separate makes the later
    automorphism argument a one-line specialization. *)
Lemma quintic_monomial_value_map (roots : 5.-tuple R) d :
  f (quintic_monomial_value roots d) =
    quintic_monomial_value (map_tuple f roots) d.
Proof.
rewrite /quintic_monomial_value rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphXn tnth_map.
Qed.

Lemma quintic_table_value_map (roots : 5.-tuple R) table :
  f (quintic_table_value roots table) =
    quintic_table_value (map_tuple f roots) table.
Proof.
rewrite /quintic_table_value rmorph_sum.
apply: eq_bigr=> d _.
exact: quintic_monomial_value_map.
Qed.

Lemma quintic_theta_value_map (roots : 5.-tuple R) i :
  f (quintic_theta_value roots i) =
    quintic_theta_value (map_tuple f roots) i.
Proof. exact: quintic_table_value_map. Qed.

End MapValues.

Section RationalCenter.

Variable F : fieldType.
Variable ratrF : {rmorphism rat -> F}.

(** If the sum of the five roots is rational, Chapman's center equation
    forces its distinguished root to be rational as well. *)
Lemma chapman_center_is_rational (roots : 5.-tuple F)
    (hcenter :
      5%:R * tnth roots o1 =
        tnth roots o0 + tnth roots o1 + tnth roots o2 +
          tnth roots o3 + tnth roots o4)
    (hsum : exists q : rat,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = ratrF q) :
  exists q : rat, tnth roots o1 = ratrF q.
Proof.
case: hsum=> q hsum.
have h5F : (5%:R : F) != 0.
  by rewrite -[5%:R](rmorph_nat ratrF 5) fmorph_eq0.
exists (q / 5%:R).
apply: (mulIf h5F).
rewrite rmorph_div ?unitfE // rmorph_nat divfK //.
by rewrite mulrC hcenter hsum.
Qed.

End RationalCenter.

Section IrreducibleRoot.

Variables (p : {poly rat}) (F : fieldType).
Variable ratrF : {rmorphism rat -> F}.

(** A degree-five irreducible polynomial over the rationals cannot acquire
    a root already in the embedded copy of the rationals.  This proof uses
    only the ordinary linear-factor theorem and irreducibility. *)
Lemma irreducible_quintic_root_not_rational
    (p_size : size p = 6%N) (p_irr : irreducible_poly p) x :
  root (map_poly ratrF p) x ->
  forall q : rat, x <> ratrF q.
Proof.
move=> hx q hxq; subst x.
have hpq : root p q.
  move: hx.
  by rewrite !rootE horner_map fmorph_eq0.
have hdiv : ('X - q%:P) %| p by rewrite dvdp_XsubCl.
have hsize : size ('X - q%:P) != 1%N by rewrite size_XsubC.
have heqp := p_irr.2 _ hsize hdiv.
have hs := eqp_size heqp.
by move: hs; rewrite size_XsubC p_size.
Qed.

End IrreducibleRoot.

Section FiveCycleNaturality.

Variable F : fieldType.

(** A ring endomorphism which sends each root along the standard five-cycle
    sends each theta value along the verified six-index cycle. *)
Lemma quintic_theta_value_five_cycle_rmap
    (roots : 5.-tuple F) (sigma : {rmorphism F -> F})
    (hsigma : forall k : 'I_5,
      sigma (tnth roots k) = tnth roots (five_cycle k)) i :
  sigma (quintic_theta_value roots i) =
    quintic_theta_value roots (chapman_cycle_index i).
Proof.
rewrite quintic_theta_value_map.
have hmap : map_tuple sigma roots = permute_quintic_roots five_cycle roots.
  apply: eq_from_tnth=> k.
  by rewrite tnth_map tnth_permute_quintic_roots hsigma.
rewrite hmap.
exact: quintic_theta_value_five_cycle.
Qed.

End FiveCycleNaturality.

Section CollisionExclusion.

Variables (p : {poly rat}) (F : fieldType).
Variable ratrF : {rmorphism rat -> F}.
Variable roots : 5.-tuple F.

Lemma chapman_collisions_impossible_for_irreducible_quintic
    (p_size : size p = 6%N) (p_irr : irreducible_poly p)
    (hroots : injective (tnth roots))
    (hroot1 : root (map_poly ratrF p) (tnth roots o1))
    (hsum : exists q : rat,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = ratrF q) :
  ~ (quintic_theta_value roots theta_i1 =
       quintic_theta_value roots theta_i2 /\
     quintic_theta_value roots theta_i3 =
       quintic_theta_value roots theta_i4).
Proof.
move=> [h12 h34].
have hcenter := chapman_five_mul_center_of_collisions hroots h12 h34.
have [q hq] := chapman_center_is_rational hcenter hsum.
have hnonrat := irreducible_quintic_root_not_rational
  p_size p_irr hroot1 (q := q).
exact: hnonrat hq.
Qed.

(** Strong form: bijectivity of the endomorphism is unnecessary once its
    action on the five roots is known. *)
Theorem quintic_theta_value_injective_of_five_cycle_endomorphism
    (p_size : size p = 6%N) (p_irr : irreducible_poly p)
    (hroots : injective (tnth roots))
    (hroot1 : root (map_poly ratrF p) (tnth roots o1))
    (hsum : exists q : rat,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = ratrF q)
    (sigma : {rmorphism F -> F})
    (hsigma : forall k : 'I_5,
      sigma (tnth roots k) = tnth roots (five_cycle k)) :
  injective (quintic_theta_value roots).
Proof.
move=> i j hij.
case hijb: (i == j).
- exact/eqP.
- exfalso.
  have hne : i != j by rewrite hijb.
  have hstep a b
      (hab : quintic_theta_value roots a = quintic_theta_value roots b) :
      quintic_theta_value roots (chapman_cycle_index a) =
        quintic_theta_value roots (chapman_cycle_index b).
    have hs := congr1 sigma hab.
    by rewrite !quintic_theta_value_five_cycle_rmap in hs.
  have hcoll := five_cycle_collision_propagates hstep hne hij.
  exact: (chapman_collisions_impossible_for_irreducible_quintic
    p_size p_irr hroots hroot1 hsum hcoll).
Qed.

(** Requested automorphism formulation.  A MathComp ring automorphism is a
    bijective ring endomorphism; the preceding theorem shows that only its
    explicitly stated root action is needed by the argument. *)
Theorem quintic_theta_value_injective_of_five_cycle_automorphism
    (p_size : size p = 6%N) (p_irr : irreducible_poly p)
    (hroots : injective (tnth roots))
    (hall_roots : forall k : 'I_5,
      root (map_poly ratrF p) (tnth roots k))
    (hsum : exists q : rat,
      tnth roots o0 + tnth roots o1 + tnth roots o2 +
        tnth roots o3 + tnth roots o4 = ratrF q)
    (sigma : {rmorphism F -> F}) (_hsigma_bijective : bijective sigma)
    (hsigma : forall k : 'I_5,
      sigma (tnth roots k) = tnth roots (five_cycle k)) :
  injective (quintic_theta_value roots).
Proof.
apply: (quintic_theta_value_injective_of_five_cycle_endomorphism
  p_size p_irr hroots (hall_roots o1) hsum hsigma).
Qed.

End CollisionExclusion.

End PolynomialFormulasQuinticChapman.
