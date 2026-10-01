# Exact finite checks

Run `python verification/verify.py` from the package root, or run the script
by its absolute path. It writes `results.json` next to itself and prints
the same JSON to standard output. Assertions stop the run on a failed check.

## What is checked

1. The four orientation formulas and the binary reflection identities are
   verified by exact symbolic expansion.
2. For n = 4,...,36, the reference polygons and explicitly specified small
   **rational** perturbations are checked for strict triangle containment,
   positive orientation of every increasing triple, the exact slack zero
   pattern, and a nonzero rank-three slack minor.
3. For N = 1,...,31, the actual reflection-lift inequalities are constructed.
   All candidate active bases are solved by rational Gaussian elimination.
   The images of the feasible vertices are exactly (j,j^2), j = 0,...,N.
4. The symbolic reference slacks for n = 4,...,12 have the claimed zeros
   and positive leading coefficients at powers 0, 1, or 2 of rho.
5. The nonnegative column normalization and a PSD trace-congruence identity
   are checked in finite examples. Integer rounding in the article's table
   is computed without floating-point arithmetic.

## Reusing the small formulation compiler

`reflection_lift(N)` returns `(A, b, x, y)` with exact rational coefficients.
The extension is `A z <= b`, and its output is `(x dot z, y dot z)`.
It uses twice the binary length of N inequalities (N >= 1).

The manuscript proves the image theorem for every finite N. The finite
vertex enumeration in this script is a regression check of the compiler,
not its general proof.

## What is not checked

The script does not implement arbitrary surreal arithmetic. It does not
numerically test all orders, establish algebraic independence, solve an
extension-complexity optimization problem, or formally verify the paper.
The rational perturbations are not witnesses for the generic lower bounds.
The large n in the complexity table are evaluated as integer formulas;
those polygons are not enumerated.
