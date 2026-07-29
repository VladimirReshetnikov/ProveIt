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
Cardano's cubic formula and Ferrari's quartic formula are developed in the
subsequent modules.

## Checking

From the repository root:

```powershell
$env:LEAN_NUM_THREADS = '0'
lake build +PolynomialFormulas

coqc -Q Algebra/PolynomialFormulas/Coq PolynomialFormulas `
  Algebra/PolynomialFormulas/Coq/Basic.v
```
