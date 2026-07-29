# Polynomial formulas through degree four

This project gives independent Lean 4 and Rocq/Coq proofs of the classical
formulas for polynomial equations of degrees one through four.  The proofs are
algebraic: they expand the proposed values and kernel-check that the defining
polynomial vanishes.

Radicals are represented by field elements together with the equations they
satisfy (`s² = D` for a square root and `u³ = z` for a cube root).  This keeps
analytic branch choices and root-existence facts out of the algebraic
correctness claim.  The Lean statements are generic over characteristic-zero
fields.  The Coq statements are independently checked over the real numbers,
where `ring`, `field`, and `nra` produce proof terms checked by the kernel.

The linear theorem proves uniqueness.  The quadratic development proves both
formula branches, their factorization, and that they exhaust every root.
The cubic development proves the Tschirnhaus translation to depressed form,
the compatible radical-pair identity in Cardano's formula, its discriminant
equation, and the formula for an arbitrary cubic after normalization. The
`solveLinear`, `solveQuadratic`, and `solveCubic` functions (with snake-case
counterparts in Coq) return fixed-size root collections; their correctness
theorems prove that every returned entry zeros the input polynomial. Ferrari's
quartic development normalizes and depresses a general quartic, proves the
cubic-resolvent parameter equations imply a difference-of-squares
factorization, and exposes a four-entry `solveQuartic` function with the same
entrywise correctness guarantee.

## Calculator interface and scope

The solver functions are ordinary reducible definitions.  For example, the
committed examples evaluate

```text
x² - 5x + 6  ->  (3, 2)
x⁴ - 5x² + 4 ->  (2, 1, -1, -2).
```

For degrees two through four, the function arguments include the square/cube
radicals used by the classical formulas.  Their correctness theorems require
the corresponding equations (`s² = D`, `u³ = z`, the Cardano branch-product
condition, and the Ferrari resolvent equations).  This is intentional: a bare
characteristic-zero field does not provide total radical operations, and the
installed Coq real-number library cannot represent nonreal roots.  Once
certified radical values are supplied, the functions compute fixed-size root
collections and the theorem proves every entry correct.  No unproved radical
oracle or hidden branch convention is introduced.

## Checking

From the repository root:

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build +PolynomialFormulas

coqc -Q Algebra/PolynomialFormulas/Coq PolynomialFormulas `
  Algebra/PolynomialFormulas/Coq/Basic.v
coqc -Q Algebra/PolynomialFormulas/Coq PolynomialFormulas `
  Algebra/PolynomialFormulas/Coq/Cubic.v
coqc -Q Algebra/PolynomialFormulas/Coq PolynomialFormulas `
  Algebra/PolynomialFormulas/Coq/Quartic.v
coqc -Q Algebra/PolynomialFormulas/Coq PolynomialFormulas `
  Algebra/PolynomialFormulas/Coq/Examples.v
coqc -Q Algebra/PolynomialFormulas/Coq PolynomialFormulas `
  Algebra/PolynomialFormulas/Coq/Audit.v
```
