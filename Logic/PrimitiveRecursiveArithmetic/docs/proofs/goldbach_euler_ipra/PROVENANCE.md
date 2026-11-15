# Provenance

Research and repository inspection date: 2026-11-15.

## Mathematical sources

- Goldbach--Euler theorem overview:
  https://en.wikipedia.org/wiki/Goldbach%E2%80%93Euler_theorem
- Doron Zeilberger, *A Proof of the Celebrated Goldbach's Theorem* (2006):
  https://sites.math.rutgers.edu/~zeilberg/goldbach.pdf
- Pelegrí Viader, Lluís Bibiloni, and Jaume Paradís,
  *On a Series of Goldbach and Euler*, American Mathematical Monthly 113
  (2006), 206--220, DOI 10.2307/27641889.

The paper's proof is a finitization of the canonical-root/geometric-series
idea, but avoids completed infinite sums and infinite reindexing.

## ProveIt / ConciseIPRA

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected `main` revision:
`a85c645dd7213a1adbe35b0965d1e44e06c942be`.

Relevant paths:

- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/PR.lean`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/NativeBiInterpretation.lean`

The current repository defines the ordinary iPRA presentation `PRAAx` and
proves `pra_iff_native`, enabling the final transfer described in this archive.
