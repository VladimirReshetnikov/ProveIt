From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From PolynomialFormulas Require Import
  AbelRuffini LowDegreeRadicals SexticRecursiveCore QuinticRecursiveFactor
  SexticFactorSelector SexticReducibleSemantics ReducibleRadicalSemantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Reusable correctness lemmas for the reducible branches of the sextic
    coefficient decision.  The linear branch delegates exactly one monic
    quintic to a lower-degree Boolean; the nonlinear branch is immediately
    radical-solvable because both factors have degree at most four. *)
Module PolynomialFormulasSexticReducibleDecision.

Module LDR := PolynomialFormulasLowDegreeRadicals.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SFS := PolynomialFormulasSexticFactorSelector.
Module SRS := PolynomialFormulasSexticReducibleSemantics.
Module RRS := PolynomialFormulasReducibleRadicalSemantics.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Definition selected_sextic_quintic_quotient
    (f : SRC.monic_sextic) : QRF.monic_quintic :=
  QRF.sextic_linear_quotient_quintic f
    (SFS.selected_sextic_linear_coefficient f).

Definition rational_monic_sextic (f : SRC.monic_sextic) : {poly rat} :=
  map_poly (intr : int -> rat) (SRC.monic_polynomial f).

Definition rational_selected_linear_factor
    (f : SRC.monic_sextic) : {poly rat} :=
  map_poly (intr : int -> rat)
    (SRC.linear_factor (SFS.selected_sextic_linear_coefficient f)).

Definition rational_selected_quintic
    (f : SRC.monic_sextic) : {poly rat} :=
  map_poly (intr : int -> rat)
    (QRF.quintic_polynomial (selected_sextic_quintic_quotient f)).

(** A successful quadratic/cubic search is already a complete positive
    answer for the radical predicate. *)
Theorem bounded_nonlinear_branch_radical_formula
    (f : SRC.monic_sextic) :
  SRC.has_bounded_nonlinear_factor f ->
  radical_formula_solves (rational_monic_sextic f).
Proof.
exact: RRS.bounded_nonlinear_factor_radical_formula.
Qed.

(** Mapping the selector's exact integer factorization to the rationals
    preserves the selected quotient literally. *)
Lemma selected_linear_factorization_rat (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  rational_monic_sextic f =
    rational_selected_linear_factor f * rational_selected_quintic f.
Proof.
move=> hlinear.
have hfactor := congr1 (map_poly (intr : int -> rat))
  (SFS.selected_sextic_linear_factorization_quintic hlinear).
move: hfactor.
rewrite /rational_monic_sextic /rational_selected_linear_factor
  /rational_selected_quintic /selected_sextic_quintic_quotient rmorphM.
by [].
Qed.

Lemma selected_linear_factor_radical_formula (f : SRC.monic_sextic) :
  radical_formula_solves (rational_selected_linear_factor f).
Proof.
apply: LDR.low_degree_radical_formula.
- by rewrite -size_poly_gt0 /rational_selected_linear_factor
    size_rat_int_poly SRC.size_linear_factor.
- by rewrite /rational_selected_linear_factor
    size_rat_int_poly SRC.size_linear_factor.
Qed.

(** On the selected linear branch, the linear factor contributes no
    additional condition: the sextic is radical-solvable exactly when its
    computed monic quintic quotient is. *)
Theorem selected_linear_branch_radical_formula_iff
    (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  (radical_formula_solves (rational_monic_sextic f) <->
   radical_formula_solves (rational_selected_quintic f)).
Proof.
move=> hlinear.
rewrite (selected_linear_factorization_rat hlinear)
  SRS.radical_formula_solves_mul.
split.
- by move=> [_ hquintic].
- move=> hquintic; split=> //.
  exact: selected_linear_factor_radical_formula.
Qed.

Definition selected_linear_radical_branch
    (quintic_decision : QRF.monic_quintic -> bool)
    (f : SRC.monic_sextic) : bool :=
  quintic_decision (selected_sextic_quintic_quotient f).

Theorem selected_linear_radical_branchP
    (quintic_decision : QRF.monic_quintic -> bool)
    (quintic_decisionP : forall q,
      reflect
        (radical_formula_solves
          (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
        (quintic_decision q))
    (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  reflect
    (radical_formula_solves (rational_monic_sextic f))
    (selected_linear_radical_branch quintic_decision f).
Proof.
move=> hlinear.
apply: (iffP (quintic_decisionP (selected_sextic_quintic_quotient f))).
- exact: (selected_linear_branch_radical_formula_iff hlinear).2.
- exact: (selected_linear_branch_radical_formula_iff hlinear).1.
Qed.

(** The final reducible dispatcher recurses only in the selected linear
    branch.  If no bounded linear factor exists, bounded reducibility forces
    a quadratic/cubic factor and the answer is unconditionally positive. *)
Definition reducible_sextic_radical_branch
    (quintic_decision : QRF.monic_quintic -> bool)
    (f : SRC.monic_sextic) : bool :=
  if SRC.has_bounded_linear_factor f
  then selected_linear_radical_branch quintic_decision f
  else SRC.has_bounded_nonlinear_factor f.

Theorem reducible_sextic_radical_branchP
    (quintic_decision : QRF.monic_quintic -> bool)
    (quintic_decisionP : forall q,
      reflect
        (radical_formula_solves
          (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
        (quintic_decision q))
    (f : SRC.monic_sextic) :
  SRC.has_bounded_proper_factor f ->
  reflect
    (radical_formula_solves (rational_monic_sextic f))
    (reducible_sextic_radical_branch quintic_decision f).
Proof.
move=> hproper.
case hlinear: (SRC.has_bounded_linear_factor f).
- rewrite /reducible_sextic_radical_branch hlinear.
  have hlinearP : SRC.has_bounded_linear_factor f by rewrite hlinear.
  exact: (@selected_linear_radical_branchP
    quintic_decision quintic_decisionP f hlinearP).
- have hnonlinear : SRC.has_bounded_nonlinear_factor f.
    move: hproper.
    by rewrite /SRC.has_bounded_proper_factor hlinear /=.
  rewrite /reducible_sextic_radical_branch hlinear hnonlinear.
  exact: ReflectT (bounded_nonlinear_branch_radical_formula hnonlinear).
Qed.

End PolynomialFormulasSexticReducibleDecision.
