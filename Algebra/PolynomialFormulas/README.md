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
```
