(* ===================================================================== *)
(*  Semantic target for the concrete Mu-recursive sextic dispatcher.     *)
(* ===================================================================== *)

From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.

From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability QuinticCanonicalDecision
  SexticRecursiveCore SexticReducibleDecision SexticMonicizationSemantics
  SexticMuRecSeparatingInstance.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecSemanticDecision.

Module QCD := PolynomialFormulasQuinticCanonicalDecision.
Module QRD := PolynomialFormulasQuinticRadicalDecidability.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module SMS := PolynomialFormulasSexticMonicizationSemantics.
Module MSI := PolynomialFormulasSexticMuRecSeparatingInstance.

Import LeanProofs.PolynomialFormulasAbelRuffini.

(* --------------------------------------------------------------------- *)
(* The projected separating search gives the same semantic dispatcher.   *)

Definition projected_monic_sextic_radicalb
    (f : SRC.monic_sextic) : bool :=
  if SRC.has_bounded_proper_factor f
  then SRD.reducible_sextic_radical_branch QCD.quintic_radicalb f
  else MSI.projected_irreducible_resolventb f.

Theorem projected_monic_sextic_radicalP (f : SRC.monic_sextic) :
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (projected_monic_sextic_radicalb f).
Proof.
case hfactor: (SRC.has_bounded_proper_factor f).
- rewrite /projected_monic_sextic_radicalb hfactor.
  have hproper : SRC.has_bounded_proper_factor f by rewrite hfactor.
  exact: (@SRD.reducible_sextic_radical_branchP
    QCD.quintic_radicalb QCD.quintic_radicalP f hproper).
- rewrite /projected_monic_sextic_radicalb hfactor.
  exact: MSI.projected_irreducible_resolvent_radicalP hfactor.
Qed.

(* --------------------------------------------------------------------- *)
(* Seven signed coefficients as an actual integer polynomial.            *)

Definition coefficient_polynomial
    (coefficients : SRC.sextic_coefficients) : {poly int} :=
  Poly coefficients.

Lemma coefficient_polynomial_coef
    (coefficients : SRC.sextic_coefficients) index :
  (coefficient_polynomial coefficients)`_index = coefficients`_index.
Proof. exact: coef_Poly. Qed.

Lemma size_coefficient_polynomial
    (coefficients : SRC.sextic_coefficients)
    (hleading : coefficients`_6 != 0) :
  size (coefficient_polynomial coefficients) = 7%N.
Proof.
apply: (SRC.size_poly_from_top_coefficient (n := 6%N)).
- by rewrite coefficient_polynomial_coef.
- move=> index Hindex.
  rewrite coefficient_polynomial_coef nth_default // size_tuple.
  exact Hindex.
Qed.

Lemma coefficients_of_coefficient_polynomial
    (coefficients : SRC.sextic_coefficients) :
  SRC.coefficients_of_poly (coefficient_polynomial coefficients) =
  coefficients.
Proof.
apply: eq_from_tnth=> index.
by rewrite SRC.coefficients_of_polyE coefficient_polynomial_coef
  (tnth_nth 0 coefficients index).
Qed.

(** This is the Coq counterpart of Lean's [AllRootsRadical] on a fixed
    seven-coefficient representation: the leading coefficient is nonzero,
    and every complex root of the represented integer polynomial is radical
    over the rationals. *)
Definition all_roots_radical_coefficients
    (coefficients : SRC.sextic_coefficients) : Prop :=
  coefficients`_6 <> 0 /\
  QRD.all_roots_radical_int (coefficient_polynomial coefficients).

Definition coefficient_sextic_radicalb
    (coefficients : SRC.sextic_coefficients) : bool :=
  SRC.is_sexticb coefficients &&
  projected_monic_sextic_radicalb (SRC.monicize coefficients).

Theorem coefficient_sextic_radicalP coefficients :
  reflect
    (all_roots_radical_coefficients coefficients)
    (coefficient_sextic_radicalb coefficients).
Proof.
case hsextic: (SRC.is_sexticb coefficients).
- rewrite /coefficient_sextic_radicalb hsextic /=.
  have hleading : coefficients`_6 <> 0 :=
    elimT (SRC.is_sexticP coefficients) hsextic.
  have hleadingb : coefficients`_6 != 0 by exact/eqP.
  have hsize := size_coefficient_polynomial hleadingb.
  have hp6 : (coefficient_polynomial coefficients)`_6 != 0.
    by rewrite coefficient_polynomial_coef.
  apply: (equivP
    (projected_monic_sextic_radicalP (SRC.monicize coefficients))).
  split.
  + move=> hformula; split=> //.
    apply: (@SMS.all_roots_radical_int_monicize
      (coefficient_polynomial coefficients) hsize hp6).2.
    rewrite coefficients_of_coefficient_polynomial.
    exact hformula.
  + move=> [_ hradical].
    have hformula := (@SMS.all_roots_radical_int_monicize
      (coefficient_polynomial coefficients) hsize hp6).1 hradical.
    rewrite coefficients_of_coefficient_polynomial in hformula.
    exact hformula.
- rewrite /coefficient_sextic_radicalb hsextic /=.
  apply: ReflectF=> [[hleading _]].
  have htrue := introT (SRC.is_sexticP coefficients) hleading.
  by rewrite hsextic in htrue.
Qed.

Corollary coefficient_sextic_radicalb_correct coefficients :
  coefficient_sextic_radicalb coefficients = true <->
  all_roots_radical_coefficients coefficients.
Proof.
split.
- exact: elimT (coefficient_sextic_radicalP coefficients).
- exact: introT (coefficient_sextic_radicalP coefficients).
Qed.

End PolynomialFormulasSexticMuRecSemanticDecision.

Print Assumptions
  PolynomialFormulasSexticMuRecSemanticDecision.projected_monic_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecSemanticDecision.coefficient_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticMuRecSemanticDecision.coefficient_sextic_radicalb_correct.
