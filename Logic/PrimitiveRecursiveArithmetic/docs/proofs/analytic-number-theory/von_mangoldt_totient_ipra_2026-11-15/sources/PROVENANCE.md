# Provenance and source snapshot

Access date: **2026-11-15**.

## Requested reference pages

1. Wikipedia, “Von Mangoldt function”  
   https://en.wikipedia.org/wiki/Von_Mangoldt_function
2. MathWorld, “Mangoldt Function”  
   https://mathworld.wolfram.com/MangoldtFunction.html
3. Wikipedia, “Euler's totient function”  
   https://en.wikipedia.org/wiki/Euler%27s_totient_function
4. MathWorld, “Totient Function”  
   https://mathworld.wolfram.com/TotientFunction.html

The report paraphrases and proves mathematical claims; it does not reproduce the pages verbatim.

## ProveIt snapshot

- Repository: https://github.com/VladimirReshetnikov/ProveIt
- Main revision inspected: `5fb2ca5dda188a4a3c7ce9ba6f28030bd0fe8322`
- Relevant files:
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
  - `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
  - `.../TeqRec.lean`
  - `.../Interpretation.lean`
  - `.../BiInterpretation.lean`
  - `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analytic-number-theory/prime_reciprocal_ipra_2026-11-15/prime_reciprocal_ipra.tex`

The existing prime-reciprocal package is reused conceptually for the finite Euler-product witness in the totient liminf theorem.

## Mathlib snapshot

Revision inspected through GitHub search/fetch: `cbe1882f5b62496bdfc6bbe540a2b3f2db852440`.

- `Mathlib/Data/Nat/Totient.lean`
- `Mathlib/NumberTheory/ArithmeticFunction/VonMangoldt.lean`
- `Mathlib/NumberTheory/Chebyshev.lean`

These files are host-level specifications and comparison points only.  Importing them is not treated as an object-theory proof in iPRA.

## Toolchain note

The inspected current mathlib `lean-toolchain` contained:

```text
leanprover/lean4:v4.36.0-rc2
```

The supplied Lean scaffolds were not compiled in this environment because Lean/Lake was not installed.
