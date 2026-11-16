# Sources and reuse notes

## Requested pages

- Bring radical: https://en.wikipedia.org/wiki/Bring_radical
- Quintic equation: https://en.wikipedia.org/wiki/Quintic_equation
- Quintic Equation (MathWorld): https://mathworld.wolfram.com/QuinticEquation.html

Pages were inspected on 2026-11-16. Mathematical formulas were rederived and audited; historical attributions were not treated as iPRA theorems.

## ProveIt material reused

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected head: `b73ff58ad10e9c446fa997777c5f502844249929`

Relevant paths:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Algebra/PolynomialFormulas.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/lagrange_inversion_ipra/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/algebra/ipra_polynomial_formulas_abel_ruffini/`

The report distinguishes the checked `Derivations` layer from human proof packets and from the new uncompiled Lean blueprint.

## Classical references

The PDF bibliography includes Abel, Galois, Hermite, Klein, Runge, Spearman–Williams, Adamchik–Jeffrey, Dummit, Doyle–McMullen, and King.

## Independent exact checker

`code/verify.py` uses exact SymPy polynomial arithmetic and explicit Python finite groups. It performs no floating-point proof step. The one decimal shown for `BR(3)` is derived only after an exact rational interval has been constructed.
