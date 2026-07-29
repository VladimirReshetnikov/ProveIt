From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From PolynomialFormulas Require Import Basic Cubic CubicComplex Quartic.

Open Scope R_scope.

(** Exact evaluations of the degree-one-through-four solver functions. *)

Import LeanProofs.PolynomialFormulas.
Import LeanProofs.PolynomialFormulasCubic.
Import LeanProofs.PolynomialFormulasQuartic.

Example solve_linear_example : solve_linear 2 4 = -2.
Proof. unfold solve_linear; field. Qed.

Example solve_quadratic_example : solve_quadratic 1 (-5) 6 1 = (3, 2).
Proof. unfold solve_quadratic; f_equal; field. Qed.

Example solve_cubic_example : solve_cubic 1 0 0 (-1) 1 0 1 = (1, (1, 1)).
Proof. unfold solve_cubic; repeat f_equal; field. Qed.

Example solve_quartic_example :
  solve_quartic 1 0 (-5) 0 4 2 3 0 1 1 = (2, (1, (-1, -2))).
Proof. unfold solve_quartic; repeat f_equal; field. Qed.

Example solve_quartic_example_correct :
  let roots := solve_quartic 1 0 (-5) 0 4 2 3 0 1 1 in
  quartic 1 0 (-5) 0 4 (fst roots) = 0 /\
  quartic 1 0 (-5) 0 4 (fst (snd roots)) = 0 /\
  quartic 1 0 (-5) 0 4 (fst (snd (snd roots))) = 0 /\
  quartic 1 0 (-5) 0 4 (snd (snd (snd roots))) = 0.
Proof.
  apply solve_quartic_correct.
  - lra.
  - unfold quartic_p; field.
  - unfold quartic_q; field.
  - unfold quartic_r; field.
  - field.
  - field.
Qed.

(** The complex cubic solver is exhaustive with a concrete primitive cube
    root of unity. *)
Example solve_cubic_complex_example_exhaustive (x : C) :
  LeanProofs.PolynomialFormulasCubicComplex.cubic
    (RtoC 1) (RtoC 0) (RtoC 0) (RtoC (-1)) x = RtoC 0 <->
  let roots := LeanProofs.PolynomialFormulasCubicComplex.solve_cubic
    (RtoC 1) (RtoC 0) (RtoC 0) (RtoC (-1))
    (RtoC 1) (RtoC 0)
    LeanProofs.PolynomialFormulasCubicComplex.primitive_omega in
  x = fst roots \/ x = fst (snd roots) \/ x = snd (snd roots).
Proof.
  apply LeanProofs.PolynomialFormulasCubicComplex.cubic_eq_zero_iff
    with (s := RtoC (1 / 2)).
  - exact LeanProofs.PolynomialFormulasCubicComplex.c1_neq_0.
  - unfold LeanProofs.PolynomialFormulasCubicComplex.cubic_delta,
      LeanProofs.PolynomialFormulasCubicComplex.cubic_p,
      LeanProofs.PolynomialFormulasCubicComplex.cubic_q,
      LeanProofs.PolynomialFormulasCubicComplex.c0,
      LeanProofs.PolynomialFormulasCubicComplex.c1,
      LeanProofs.PolynomialFormulasCubicComplex.c2,
      LeanProofs.PolynomialFormulasCubicComplex.c3.
    apply injective_projections; cbn; field.
  - unfold LeanProofs.PolynomialFormulasCubicComplex.cubic_q,
      LeanProofs.PolynomialFormulasCubicComplex.c2,
      LeanProofs.PolynomialFormulasCubicComplex.c3.
    apply injective_projections; cbn; field.
  - unfold LeanProofs.PolynomialFormulasCubicComplex.cubic_q,
      LeanProofs.PolynomialFormulasCubicComplex.c2,
      LeanProofs.PolynomialFormulasCubicComplex.c3.
    apply injective_projections; cbn; field.
  - unfold LeanProofs.PolynomialFormulasCubicComplex.cubic_p,
      LeanProofs.PolynomialFormulasCubicComplex.c3.
    apply injective_projections; cbn; field.
  - exact LeanProofs.PolynomialFormulasCubicComplex.primitive_omega_spec.
Qed.
