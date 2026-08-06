From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability QuinticRecursiveFactor
  QuinticCanonicalDecision SexticRecursiveCore SexticReducibleDecision
  SexticMonicDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Import LeanProofs.PolynomialFormulasAbelRuffini.
Local Open Scope ring_scope.

(** The parameter-free coefficient decision obtained by instantiating the
    sextic dispatcher with the proved Frobenius--Dummit quintic Boolean. *)
Module PolynomialFormulasSexticConcreteDecision.

Module QCD := PolynomialFormulasQuinticCanonicalDecision.
Module QRD := PolynomialFormulasQuinticRadicalDecidability.
Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SRD := PolynomialFormulasSexticReducibleDecision.
Module SMD := PolynomialFormulasSexticMonicDecision.

Definition monic_sextic_radicalb (f : SRC.monic_sextic) : bool :=
  SMD.monic_sextic_radical_decision QCD.quintic_radicalb f.

Theorem monic_sextic_radicalP (f : SRC.monic_sextic) :
  reflect
    (radical_formula_solves (SRD.rational_monic_sextic f))
    (monic_sextic_radicalb f).
Proof.
exact: (@SMD.monic_sextic_radical_decisionP
  QCD.quintic_radicalb QCD.quintic_radicalP f).
Qed.

Definition integer_sextic_radicalb (p : {poly int}) : bool :=
  SMD.integer_sextic_radical_decision QCD.quintic_radicalb p.

Theorem integer_sextic_radicalP (p : {poly int})
    (hp_size : size p = 7%N) :
  reflect (QRD.all_roots_radical_int p) (integer_sextic_radicalb p).
Proof.
exact: (@SMD.integer_sextic_radical_decisionP
  QCD.quintic_radicalb QCD.quintic_radicalP p hp_size).
Qed.

(** A total statement on arbitrary integer polynomials.  This form makes the
    exact-degree condition part of the proposition, matching Lean's
    [AllRootsRadical] predicate. *)
Theorem integer_polynomial_is_radical_solvable_sexticP (p : {poly int}) :
  reflect
    (size p = 7%N /\ QRD.all_roots_radical_int p)
    (integer_sextic_radicalb p).
Proof.
case hdecision: (integer_sextic_radicalb p).
- apply: ReflectT.
  have hsize : size p == 7%N.
    case hsize: (size p == 7%N) => //.
    move: hdecision.
    by rewrite /integer_sextic_radicalb
      /SMD.integer_sextic_radical_decision hsize.
  have hp_size : size p = 7%N := eqP hsize.
  split=> //.
  exact: elimT (@integer_sextic_radicalP p hp_size) hdecision.
- apply: ReflectF=> [[hp_size hradical]].
  have := introT (@integer_sextic_radicalP p hp_size) hradical.
  by rewrite hdecision.
Qed.

(** Here "decidable" has Coq's constructive sum meaning: the result contains
    either a proof of the all-roots radical predicate or a proof of its
    negation.  The choice is computed by [integer_sextic_radicalb]. *)
Definition all_roots_radical_sextic_int_decidable
    (p : {poly int}) (hp_size : size p = 7%N) :
  {QRD.all_roots_radical_int p} + {~ QRD.all_roots_radical_int p} :=
  @SMD.all_roots_radical_sextic_int_decidable
    QCD.quintic_radicalb QCD.quintic_radicalP p hp_size.

Definition integer_polynomial_is_radical_solvable_sextic_decidable
    (p : {poly int}) :
  {size p = 7%N /\ QRD.all_roots_radical_int p} +
  {~ (size p = 7%N /\ QRD.all_roots_radical_int p)}.
Proof.
case hdecision: (integer_sextic_radicalb p).
- left.
  exact: elimT (integer_polynomial_is_radical_solvable_sexticP p) hdecision.
- right=> hradical.
  have := introT (integer_polynomial_is_radical_solvable_sexticP p) hradical.
  by rewrite hdecision.
Defined.

End PolynomialFormulasSexticConcreteDecision.

Print Assumptions
  PolynomialFormulasSexticConcreteDecision.monic_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticConcreteDecision.integer_sextic_radicalP.
Print Assumptions
  PolynomialFormulasSexticConcreteDecision.integer_polynomial_is_radical_solvable_sexticP.
Print Assumptions
  PolynomialFormulasSexticConcreteDecision.all_roots_radical_sextic_int_decidable.
Print Assumptions
  PolynomialFormulasSexticConcreteDecision.integer_polynomial_is_radical_solvable_sextic_decidable.
