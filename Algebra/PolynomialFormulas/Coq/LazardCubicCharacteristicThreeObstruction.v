From mathcomp Require Import
  all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The characteristic-three obstruction to Lazard's cubic formula

    The paper globally excludes characteristics two and five, but its
    Section 4 cubic formula divides by three and uses a primitive third root
    of unity.  The prime field [F_3] satisfies the printed exclusions while
    providing neither operation.

    This is not merely an inseparability issue: [X^3 - X - 1] is rootless,
    hence irreducible, over [F_3], and its derivative is the nonzero constant
    [-1].  Thus the displayed cubic formula needs an additional
    characteristic-not-three hypothesis, together with an ambient field
    containing the required roots of unity and radicals. *)
Module PolynomialFormulasLazardCubicCharacteristicThreeObstruction.

Import GRing.Theory.

Local Open Scope ring_scope.

Local Notation F3 := 'F_3.

Section ArbitraryCharacteristicThreeField.

Variable K : fieldType.
Hypothesis K_pchar_three : 3 \in [pchar K].

(** Division by three collapses in every characteristic-three field, not
    only in the prime field used for the concrete cubic below. *)
Lemma characteristic_three_div_three_eq_zero (x : K) :
  x / (3%:R : K) = 0.
Proof.
by rewrite (GRing.pcharf0 K_pchar_three) invr0 mulr0.
Qed.

(** No characteristic-three field can acquire a primitive third root in an
    extension.  Frobenius gives [(omega - 1)^3 = omega^3 - 1], so every
    third root of unity is one. *)
Theorem characteristic_three_no_primitive_cube_root :
  ~ exists omega : K, 3.-primitive_root omega.
Proof.
move=> [omega omega_primitive].
have homega3 : omega ^+ 3 = 1 := prim_expr_order omega_primitive.
have hfreshman :
    (omega - 1) ^+ 3 = omega ^+ 3 - (1 : K) ^+ 3.
  exact: (pFrobenius_autB_comm K_pchar_three (commr1 omega)).
have hsubcube : (omega - 1) ^+ 3 = 0.
  by rewrite hfreshman homega3 expr1n subrr.
have hsubcubeb : (omega - 1) ^+ 3 == 0.
  apply/eqP.
  exact: hsubcube.
have hsubb : omega - 1 == 0.
  move: hsubcubeb.
  by rewrite expf_eq0.
have homega_one : omega = 1.
  apply/eqP.
  by rewrite -subr_eq0 hsubb.
have hbad : (3 %| 1)%N.
  by rewrite (prim_order_dvd omega_primitive) homega_one expr1.
by move: hbad.
Qed.

Theorem characteristic_three_formula_obstruction :
  (forall x : K, x / (3%:R : K) = 0) /\
  ~ exists omega : K, 3.-primitive_root omega.
Proof.
exact: conj characteristic_three_div_three_eq_zero
  characteristic_three_no_primitive_cube_root.
Qed.

End ArbitraryCharacteristicThreeField.

(** The coefficient field really has characteristic three. *)
Lemma F3_pchar_three : 3 \in [pchar F3].
Proof. exact: pchar_Fp. Qed.

Lemma F3_pchar_not_two : 2 \notin [pchar F3].
Proof. by rewrite (GRing.pcharf_eq F3_pchar_three). Qed.

Lemma F3_pchar_not_five : 5 \notin [pchar F3].
Proof. by rewrite (GRing.pcharf_eq F3_pchar_three). Qed.

Theorem F3_satisfies_lazard_printed_characteristic_exclusions :
  (2 \notin [pchar F3]) /\ (5 \notin [pchar F3]).
Proof. exact: conj F3_pchar_not_two F3_pchar_not_five. Qed.

Lemma F3_three_eq_zero : (3%:R : F3) = 0.
Proof. exact: GRing.pcharf0 F3_pchar_three. Qed.

(** Division by the integer three is the zero operation in characteristic
    three, so the displayed Cardano normalization cannot be interpreted as
    division by a unit. *)
Lemma F3_div_three_eq_zero (x : F3) : x / (3%:R : F3) = 0.
Proof.
exact: characteristic_three_div_three_eq_zero F3 F3_pchar_three x.
Qed.

(** [F_3] has no primitive third root.  Finite-field Frobenius gives
    [omega^3 = omega], whereas exact order three gives [omega^3 = 1]. *)
Theorem F3_no_primitive_cube_root :
  ~ exists omega : F3, 3.-primitive_root omega.
Proof.
exact: characteristic_three_no_primitive_cube_root F3 F3_pchar_three.
Qed.

(** A concrete irreducible, separable cubic in the allowed characteristic. *)
Definition lazard_F3_irreducible_cubic : {poly F3} :=
  'X ^+ 3 - 'X - (1 : F3)%:P.

Lemma lazard_F3_irreducible_cubic_horner (x : F3) :
  lazard_F3_irreducible_cubic.[x] = - (1 : F3).
Proof.
have x_cube_self := expf_card x.
rewrite card_Fp in x_cube_self.
rewrite /lazard_F3_irreducible_cubic !hornerE
  x_cube_self subrr sub0r.
all: by [].
Qed.

Lemma lazard_F3_irreducible_cubic_has_no_root (x : F3) :
  ~~ root lazard_F3_irreducible_cubic x.
Proof.
by rewrite rootE lazard_F3_irreducible_cubic_horner
  oppr_eq0 oner_eq0.
Qed.

Lemma lazard_F3_irreducible_cubic_size :
  size lazard_F3_irreducible_cubic = 4.
Proof.
have hlinear :
    size (('X ^+ 3 : {poly F3}) + - 'X) = 4.
  have hdegree :
      ltn (size (- 'X : {poly F3})) (size ('X ^+ 3 : {poly F3})).
    by rewrite size_polyN size_polyX size_polyXn.
  have hcube_size : size ('X ^+ 3 : {poly F3}) = 4.
    by rewrite size_polyXn.
  exact: etrans (size_polyDl hdegree) hcube_size.
have hconstant :
    ltn (size (- (1 : F3)%:P))
      (size (('X ^+ 3 : {poly F3}) + - 'X)).
  by rewrite hlinear size_polyN size_polyC oner_neq0.
change (size (((('X ^+ 3 : {poly F3}) + - 'X) +
  - (1 : F3)%:P)) = 4).
exact: etrans (size_polyDl hconstant) hlinear.
Qed.

Theorem lazard_F3_irreducible_cubic_irreducible :
  irreducible_poly lazard_F3_irreducible_cubic.
Proof.
apply: cubic_irreducible.
- by rewrite lazard_F3_irreducible_cubic_size.
- exact: lazard_F3_irreducible_cubic_has_no_root.
Qed.

Lemma lazard_F3_irreducible_cubic_derivative :
  lazard_F3_irreducible_cubic^`() = - (1 : {poly F3}).
Proof.
by rewrite /lazard_F3_irreducible_cubic !derivB derivXn derivX derivC
  subr0 -scaler_nat F3_three_eq_zero scale0r sub0r.
Qed.

Theorem lazard_F3_irreducible_cubic_separable :
  separable_poly lazard_F3_irreducible_cubic.
Proof.
have minus_oneE :
    (-1 : {poly F3}) = (-1 : F3) *: (1 : {poly F3}).
  by rewrite scaleN1r.
rewrite unlock /separable_poly
  lazard_F3_irreducible_cubic_derivative minus_oneE.
by rewrite coprimepZr ?oppr_eq0 ?oner_eq0 // coprimep1.
Qed.

(** Closed package of the scope counterexample: all printed global
    characteristic assumptions hold, the cubic is irreducible and separable,
    but division by three collapses and no primitive cube root exists. *)
Theorem lazard_section_four_scope_counterexample :
  ((2 \notin [pchar F3]) /\ (5 \notin [pchar F3])) /\
  irreducible_poly lazard_F3_irreducible_cubic /\
  separable_poly lazard_F3_irreducible_cubic /\
  (forall x : F3, x / (3%:R : F3) = 0) /\
  ~ exists omega : F3, 3.-primitive_root omega.
Proof.
split.
- exact: F3_satisfies_lazard_printed_characteristic_exclusions.
- split.
  + exact: lazard_F3_irreducible_cubic_irreducible.
  + split.
    * exact: lazard_F3_irreducible_cubic_separable.
    * split.
      -- exact: F3_div_three_eq_zero.
      -- exact: F3_no_primitive_cube_root.
Qed.

Print Assumptions characteristic_three_formula_obstruction.
Print Assumptions lazard_section_four_scope_counterexample.

End PolynomialFormulasLazardCubicCharacteristicThreeObstruction.
