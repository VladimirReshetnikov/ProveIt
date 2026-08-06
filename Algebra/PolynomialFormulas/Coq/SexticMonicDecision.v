From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability QuinticRecursiveFactor
  SexticRecursiveCore SexticRationalRootSearch SexticCanonicalVieta
  SexticMonicizationSemantics SexticReducibleDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Composition of the reducible and irreducible branches of the monic
    sextic decision.  The only parameter left here is the already isolated
    monic-quintic Boolean and its exact radical-solvability reflector. *)
Module PolynomialFormulasSexticMonicDecision.

Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SCV := PolynomialFormulasSexticCanonicalVieta.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module SRR := PolynomialFormulasSexticRationalRootSearch.
Module SMS := PolynomialFormulasSexticMonicizationSemantics.
Module QRD := PolynomialFormulasQuinticRadicalDecidability.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Definition irreducible_sextic_radical_branch
    (f : SRC.monic_sextic) : bool :=
  SRR.pair_scaled_rational_rootb f
      (SCV.pair_total_separating_parameter f) ||
  SRR.triple_scaled_rational_rootb f
      (SCV.triple_total_separating_parameter f).

Lemma canonical_rational_monic_sextic_neq0 (f : SRC.monic_sextic) :
  SCV.rational_monic_sextic f != 0.
Proof.
apply/eqP=> hzero.
by move: (SCV.size_rational_monic_sextic f); rewrite hzero size_poly0.
Qed.

Theorem irreducible_sextic_radical_branchP
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (irreducible_sextic_radical_branch f).
Proof.
apply: (equivP (SCV.canonical_sextic_scaled_resolvent_solvableP hfactor)).
split.
- move=> hsolvable.
  have hradical := elimT
    (AbelGaloisPolyRat (SCV.rational_monic_sextic f)) hsolvable.
  exact: (solvable_formula (canonical_rational_monic_sextic_neq0 f)).1
    hradical.
- move=> hformula.
  have hradical :=
    (solvable_formula (canonical_rational_monic_sextic_neq0 f)).2
      hformula.
  exact: introT (AbelGaloisPolyRat (SCV.rational_monic_sextic f))
    hradical.
Qed.

Definition monic_sextic_radical_decision
    (quintic_decision : QRF.monic_quintic -> bool)
    (f : SRC.monic_sextic) : bool :=
  if SRC.has_bounded_proper_factor f
  then SRD.reducible_sextic_radical_branch quintic_decision f
  else irreducible_sextic_radical_branch f.

Theorem monic_sextic_radical_decisionP
    (quintic_decision : QRF.monic_quintic -> bool)
    (quintic_decisionP : forall q,
      reflect
        (radical_formula_solves
          (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
        (quintic_decision q))
    (f : SRC.monic_sextic) :
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (monic_sextic_radical_decision quintic_decision f).
Proof.
case hfactor: (SRC.has_bounded_proper_factor f).
- rewrite /monic_sextic_radical_decision hfactor.
  have hproper : SRC.has_bounded_proper_factor f by rewrite hfactor.
  exact: (@SRD.reducible_sextic_radical_branchP
    quintic_decision quintic_decisionP f hproper).
- rewrite /monic_sextic_radical_decision hfactor.
  exact: irreducible_sextic_radical_branchP hfactor.
Qed.

Lemma sextic_leading_coefficient_neq0 (p : {poly int})
    (hp_size : size p = 7%N) : p`_6 != 0.
Proof.
have hp0 : p != 0 by rewrite -size_poly_eq0 hp_size.
move: hp0.
by rewrite -lead_coef_eq0 lead_coefE hp_size.
Qed.

(** The total coefficient-level Boolean rejects non-sextics and otherwise
    applies integral monicization before running the monic dispatcher. *)
Definition integer_sextic_radical_decision
    (quintic_decision : QRF.monic_quintic -> bool)
    (p : {poly int}) : bool :=
  (size p == 7%N) &&
  SRC.is_sexticb (SRC.coefficients_of_poly p) &&
  monic_sextic_radical_decision quintic_decision
    (SRC.monicize (SRC.coefficients_of_poly p)).

Theorem integer_sextic_radical_decisionP
    (quintic_decision : QRF.monic_quintic -> bool)
    (quintic_decisionP : forall q,
      reflect
        (radical_formula_solves
          (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
        (quintic_decision q))
    (p : {poly int}) (hp_size : size p = 7%N) :
  reflect
    (QRD.all_roots_radical_int p)
    (integer_sextic_radical_decision quintic_decision p).
Proof.
have hp6 := sextic_leading_coefficient_neq0 hp_size.
have his_sextic : SRC.is_sexticb (SRC.coefficients_of_poly p) = true.
  rewrite /SRC.is_sexticb
    (SRC.coefficients_of_poly_nthE p (i := 6%N) isT).
  exact: hp6.
rewrite /integer_sextic_radical_decision hp_size eqxx his_sextic /=.
apply: (equivP (@monic_sextic_radical_decisionP
  quintic_decision quintic_decisionP
  (SRC.monicize (SRC.coefficients_of_poly p)))).
exact: iff_sym (SMS.all_roots_radical_int_monicize hp_size hp6).
Qed.

Definition all_roots_radical_sextic_int_decidable
    (quintic_decision : QRF.monic_quintic -> bool)
    (quintic_decisionP : forall q,
      reflect
        (radical_formula_solves
          (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
        (quintic_decision q))
    (p : {poly int}) (hp_size : size p = 7%N) :
  {QRD.all_roots_radical_int p} + {~ QRD.all_roots_radical_int p}.
Proof.
case hdecision: (integer_sextic_radical_decision quintic_decision p).
- left.
  exact: elimT (@integer_sextic_radical_decisionP
    quintic_decision quintic_decisionP p hp_size) hdecision.
- right=> hradical.
  have := introT (@integer_sextic_radical_decisionP
    quintic_decision quintic_decisionP p hp_size) hradical.
  by rewrite hdecision.
Defined.

End PolynomialFormulasSexticMonicDecision.
