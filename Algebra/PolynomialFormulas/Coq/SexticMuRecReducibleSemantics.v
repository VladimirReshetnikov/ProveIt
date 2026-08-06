From Stdlib Require Import Bool Vector.
From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Undecidability.Shared.Libs.DLW Require Import vec.
From Undecidability.MuRec.Util Require Import recomp.
From PolynomialFormulas Require Import
  AbelRuffini LowDegreeRadicals SexticRecursiveCore QuinticRecursiveFactor
  SexticFactorSelector SexticReducibleSemantics ReducibleRadicalSemantics
  SexticReducibleDecision SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecQuinticBranch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** Semantic correctness of the bounded existential linear branch used by
    the recursive sextic program.  Unlike the selector-based presentation,
    the main proof works for every successful candidate in the bounded
    search and factors out that argument below. *)
Module PolynomialFormulasSexticMuRecReducibleSemantics.

Module LDR := PolynomialFormulasLowDegreeRadicals.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SFS := PolynomialFormulasSexticFactorSelector.
Module SRS := PolynomialFormulasSexticReducibleSemantics.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module SMFD := PolynomialFormulasSexticMuRecFactorDecision.
Module SMQB := PolynomialFormulasSexticMuRecQuinticBranch.

Import LeanProofs.PolynomialFormulasAbelRuffini.

(** A vector Boolean has the required quintic semantics only on canonical
    encodings of MathComp monic quintics.  No claim is needed about arbitrary
    five-vectors. *)
Definition encoded_quintic_radical_correct
    (quintic_decisionb : Vector.t nat 5 -> bool) : Type :=
  forall q : QRF.monic_quintic,
    reflect
      (radical_formula_solves
        (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
      (quintic_decisionb (SMQB.encode_monic_quintic_coefficients q)).

(** Specialize the vector Boolean to the tuple interface expected by the
    existing selector-based semantic dispatcher. *)
Definition encoded_quintic_radical_decision
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (q : QRF.monic_quintic) : bool :=
  quintic_decisionb (SMQB.encode_monic_quintic_coefficients q).

Lemma encoded_quintic_radical_decisionP quintic_decisionb :
  encoded_quintic_radical_correct quintic_decisionb ->
  forall q : QRF.monic_quintic,
    reflect
      (radical_formula_solves
        (map_poly (intr : int -> rat) (QRF.quintic_polynomial q)))
      (encoded_quintic_radical_decision quintic_decisionb q).
Proof. exact. Qed.

Definition rational_linear_factor (candidate : int) : {poly rat} :=
  map_poly (intr : int -> rat) (SRC.linear_factor candidate).

Definition rational_candidate_quintic
    (f : SRC.monic_sextic) (candidate : int) : {poly rat} :=
  map_poly (intr : int -> rat)
    (QRF.quintic_polynomial
      (QRF.sextic_linear_quotient_quintic f candidate)).

(** Synthetic division at any zero-remainder candidate gives the exact
    rational factorization used in both directions of the search proof. *)
Lemma linear_candidate_factorization_rat
    (f : SRC.monic_sextic) (candidate : int) :
  SRC.linear_remainder_zerob f candidate ->
  SRD.rational_monic_sextic f =
    rational_linear_factor candidate *
    rational_candidate_quintic f candidate.
Proof.
move=> hremainder.
have hfactor := congr1 (map_poly (intr : int -> rat))
  (@QRF.sextic_linear_factorization_quintic f candidate hremainder).
move: hfactor.
rewrite /SRD.rational_monic_sextic /rational_linear_factor
  /rational_candidate_quintic rmorphM.
by [].
Qed.

Lemma linear_candidate_factor_radical_formula (candidate : int) :
  radical_formula_solves (rational_linear_factor candidate).
Proof.
apply: LDR.low_degree_radical_formula.
- by rewrite -size_poly_gt0 /rational_linear_factor
    size_rat_int_poly SRC.size_linear_factor.
- by rewrite /rational_linear_factor
    size_rat_int_poly SRC.size_linear_factor.
Qed.

(** Since a rational linear factor is always solvable by radicals, the
    sextic and the candidate's monic quintic quotient have precisely the
    same radical-solvability semantics. *)
Theorem linear_candidate_radical_formula_iff
    (f : SRC.monic_sextic) (candidate : int) :
  SRC.linear_remainder_zerob f candidate ->
  (radical_formula_solves (SRD.rational_monic_sextic f) <->
   radical_formula_solves (rational_candidate_quintic f candidate)).
Proof.
move=> hremainder.
rewrite (linear_candidate_factorization_rat hremainder)
  SRS.radical_formula_solves_mul.
split.
- by move=> [_ hquintic].
- move=> hquintic; split=> //.
  exact: linear_candidate_factor_radical_formula.
Qed.

(** The bounded existential computation is semantically complete under the
    same hypothesis that makes the selector branch meaningful. *)
Theorem bounded_reducible_linear_branchP
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (SMQB.bounded_reducible_linear_branchb quintic_decisionb f).
Proof.
move=> hlinear.
rewrite /SMQB.bounded_reducible_linear_branchb.
apply: (iffP hasP).
- move=> [candidate hmember /andP [hremainder hdecision]].
  have hquintic := elimT (quintic_decisionP _) hdecision.
  exact: (linear_candidate_radical_formula_iff hremainder).2 hquintic.
- move=> hsextic.
  have [candidate [hmember hdivides]] :=
    elimT (SRC.has_bounded_linear_factorP f) hlinear.
  have hremainder : SRC.linear_remainder_zerob f candidate :=
    SFS.linear_divisor_remainder_zero hdivides.
  have hquintic :=
    (linear_candidate_radical_formula_iff hremainder).1 hsextic.
  have hdecision := introT (quintic_decisionP _) hquintic.
  exists candidate.
  - exact hmember.
  - by apply/andP; split.
Qed.

(** Both implementations reflect the same proposition, so under the
    quintic contract the bounded existential search agrees extensionally
    with the canonical selector branch. *)
Theorem bounded_reducible_linear_branchb_selected
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  SMQB.bounded_reducible_linear_branchb quintic_decisionb f =
  SRD.selected_linear_radical_branch
    (encoded_quintic_radical_decision quintic_decisionb) f.
Proof.
move=> hlinear.
have hbounded := @bounded_reducible_linear_branchP
  quintic_decisionb quintic_decisionP f hlinear.
have hselected := @SRD.selected_linear_radical_branchP
  (encoded_quintic_radical_decision quintic_decisionb)
  (encoded_quintic_radical_decisionP quintic_decisionP) f hlinear.
apply Bool.eq_true_iff_eq; split.
- move=> hbranch.
  exact: introT hselected (elimT hbounded hbranch).
- move=> hbranch.
  exact: introT hbounded (elimT hselected hbranch).
Qed.

(** Compatibility at the six-coefficient recursive-program interface. *)
Theorem encoded_monic_reducible_linear_branchb_selected
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) :
  SRC.has_bounded_linear_factor f ->
  SMQB.encoded_monic_reducible_linear_branchb quintic_decisionb
      (SMFD.encode_monic_sextic_coefficients f) =
  SRD.selected_linear_radical_branch
    (encoded_quintic_radical_decision quintic_decisionb) f.
Proof.
move=> hlinear.
rewrite SMQB.encoded_monic_reducible_linear_branchb_mathcomp.
exact: bounded_reducible_linear_branchb_selected hlinear.
Qed.

Theorem encoded_monic_reducible_linear_branch_relation_selected
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) out :
  SRC.has_bounded_linear_factor f ->
  SMQB.encoded_monic_reducible_linear_branch_relation quintic_decisionb
      (SMFD.encode_monic_sextic_coefficients f) out <->
  out = bool_to_nat
    (SRD.selected_linear_radical_branch
      (encoded_quintic_radical_decision quintic_decisionb) f).
Proof.
move=> hlinear.
rewrite SMQB.encoded_monic_reducible_linear_branch_relation_mathcomp.
rewrite (bounded_reducible_linear_branchb_selected
  quintic_decisionP hlinear).
reflexivity.
Qed.

Theorem encoded_monic_reducible_linear_branch_code_relation_selected
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) out :
  SRC.has_bounded_linear_factor f ->
  SMQB.encoded_monic_reducible_linear_branch_code_relation quintic_decisionb
      (inject (SMFD.encode_monic_sextic_coefficients f) ## vec_nil) out <->
  out = bool_to_nat
    (SRD.selected_linear_radical_branch
      (encoded_quintic_radical_decision quintic_decisionb) f).
Proof.
move=> hlinear.
rewrite SMQB.encoded_monic_reducible_linear_branch_code_relation_mathcomp.
rewrite (bounded_reducible_linear_branchb_selected
  quintic_decisionP hlinear).
reflexivity.
Qed.

(** Drop-in reducible dispatcher: only its linear arm is replaced by the
    bounded existential program. *)
Definition bounded_search_reducible_sextic_radical_branch
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (f : SRC.monic_sextic) : bool :=
  if SRC.has_bounded_linear_factor f
  then SMQB.bounded_reducible_linear_branchb quintic_decisionb f
  else SRC.has_bounded_nonlinear_factor f.

Theorem bounded_search_reducible_sextic_radical_branch_selected
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) :
  bounded_search_reducible_sextic_radical_branch quintic_decisionb f =
  SRD.reducible_sextic_radical_branch
    (encoded_quintic_radical_decision quintic_decisionb) f.
Proof.
rewrite /bounded_search_reducible_sextic_radical_branch
  /SRD.reducible_sextic_radical_branch.
case hlinear: (SRC.has_bounded_linear_factor f).
- have hlinearP : SRC.has_bounded_linear_factor f by rewrite hlinear.
  exact: bounded_reducible_linear_branchb_selected hlinearP.
- reflexivity.
Qed.

Theorem bounded_search_reducible_sextic_radical_branchP
    (quintic_decisionb : Vector.t nat 5 -> bool)
    (quintic_decisionP : encoded_quintic_radical_correct quintic_decisionb)
    (f : SRC.monic_sextic) :
  SRC.has_bounded_proper_factor f ->
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (bounded_search_reducible_sextic_radical_branch quintic_decisionb f).
Proof.
move=> hproper.
rewrite (bounded_search_reducible_sextic_radical_branch_selected
  quintic_decisionP).
exact: (@SRD.reducible_sextic_radical_branchP
  (encoded_quintic_radical_decision quintic_decisionb)
  (encoded_quintic_radical_decisionP quintic_decisionP) f hproper).
Qed.

Print Assumptions linear_candidate_radical_formula_iff.
Print Assumptions bounded_reducible_linear_branchP.
Print Assumptions bounded_reducible_linear_branchb_selected.
Print Assumptions encoded_monic_reducible_linear_branchb_selected.
Print Assumptions encoded_monic_reducible_linear_branch_relation_selected.
Print Assumptions encoded_monic_reducible_linear_branch_code_relation_selected.
Print Assumptions bounded_search_reducible_sextic_radical_branchP.

End PolynomialFormulasSexticMuRecReducibleSemantics.
