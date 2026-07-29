From Stdlib Require Import Reals Ring Field Psatz.
From PolynomialFormulas Require Import Basic Cubic Quartic.

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
