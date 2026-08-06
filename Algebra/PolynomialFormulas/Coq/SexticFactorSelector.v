From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  SexticRecursiveCore QuinticRecursiveFactor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** A transparent selector for the bounded linear-factor branch of the
    recursive sextic decision.

    The default value is irrelevant whenever the search succeeds.  Keeping
    the selector as a direct [find]/[nth] program is important: the quintic
    quotient handed to the next decision stage is computed from the sextic
    coefficients, without invoking a semantic choice principle. *)
Module PolynomialFormulasSexticFactorSelector.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasQuinticRecursiveFactor.

Definition selected_sextic_linear_coefficient
    (f : monic_sextic) : int :=
  let candidates := symmetric_interval (root_bound f) in
  nth 0 candidates
    (find (fun c => linear_factor c %| monic_polynomial f) candidates).

Lemma selected_sextic_linear_coefficient_divides (f : monic_sextic) :
  PolynomialFormulasSexticRecursiveCore.has_bounded_linear_factor f ->
  linear_factor (selected_sextic_linear_coefficient f) %|
    monic_polynomial f.
Proof.
rewrite /PolynomialFormulasSexticRecursiveCore.has_bounded_linear_factor
  /selected_sextic_linear_coefficient.
exact: nth_find.
Qed.

Lemma linear_factor_XsubC (c : int) :
  linear_factor c = 'X - (- c)%:P.
Proof. by rewrite /linear_factor rmorphN opprK. Qed.

Lemma linear_divisor_remainder_zero (f : monic_sextic) (c : int) :
  linear_factor c %| monic_polynomial f ->
  linear_remainder_zerob f c.
Proof.
move=> hdiv.
apply/linear_remainder_zeroP.
have hprod : linear_factor c %|
    linear_factor c * linear_quotient f c :=
  dvdp_mulIl _ _.
have hrem : linear_factor c %|
    (f`_0 - c * linear_q0 f c)%:P.
  by move: hdiv; rewrite (linear_division_identity f c)
    (@dvdp_addr _ _ _ _ hprod).
have hrzero : f`_0 - c * linear_q0 f c = 0.
  apply/eqP/negPn/negP=> hrnz.
  have hCne : (f`_0 - c * linear_q0 f c)%:P != 0.
    by rewrite polyC_eq0.
  have hle := dvdp_leq hCne hrem.
  move: hle.
  by rewrite size_linear_factor size_polyC hrnz.
exact: subr0_eq hrzero.
Qed.

Lemma selected_sextic_linear_remainder_zero (f : monic_sextic) :
  PolynomialFormulasSexticRecursiveCore.has_bounded_linear_factor f ->
  linear_remainder_zerob f (selected_sextic_linear_coefficient f).
Proof.
move=> hlinear.
apply: linear_divisor_remainder_zero.
exact: selected_sextic_linear_coefficient_divides hlinear.
Qed.

Theorem selected_sextic_linear_factorization_quintic (f : monic_sextic) :
  PolynomialFormulasSexticRecursiveCore.has_bounded_linear_factor f ->
  monic_polynomial f =
    linear_factor (selected_sextic_linear_coefficient f) *
      quintic_polynomial
        (sextic_linear_quotient_quintic f
          (selected_sextic_linear_coefficient f)).
Proof.
move=> hlinear.
apply: sextic_linear_factorization_quintic.
exact: selected_sextic_linear_remainder_zero hlinear.
Qed.

End PolynomialFormulasSexticFactorSelector.
