# Source and provenance manifest

Consulted 16 November 2026.

## Primary requested pages

1. Wikipedia, **Hypergeometric function**  
   `https://en.wikipedia.org/wiki/Hypergeometric_function`
2. Eric W. Weisstein, **Hypergeometric Function**, MathWorld  
   `https://mathworld.wolfram.com/HypergeometricFunction.html`

The source-row inventory records the displayed definitions, differential
formulae, transformations, specializations, integrals, summations, contiguous
relations, Kummer forms, and isolated values found on those pages.  Page
statements were not accepted blindly: normalization and branch conditions were
re-derived or explicitly qualified.

## Supporting references

- NIST Digital Library of Mathematical Functions, Chapter 15:  
  `https://dlmf.nist.gov/15`
- W. N. Bailey, *Generalized Hypergeometric Series* (1935).
- A. Erdélyi et al., *Higher Transcendental Functions*, Vol. I (1953).
- G. E. Andrews, R. Askey, R. Roy, *Special Functions* (1999).

## ProveIt repository

Repository: `https://github.com/VladimirReshetnikov/ProveIt`

The main branch was inspected through the GitHub connector.  The newest
commit observed during preparation was:

```text
c6643d49ab37d30d1204c689bf7f800db1a04c7b
Derive Fibonacci and Lucas identities in iPRA
2026-11-16T18:45:55Z
```

Relevant paths:

- `Logic/PrimitiveRecursiveArithmetic/README.md`
- `Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/`
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Core/Definitions.lean`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/taylor_cauchy_ipra/`
- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/gamma_ipra/`
- `Analysis/FabiusFunction/Lean/FabiusFunction/ClassicalHypergeometricLimit.lean`

The repository README distinguishes kernel-checked `ConciseIPRA` and
`Derivations` material from research packets that may contain uncompiled
outlines.  This archive preserves the same distinction.

## Computational checks

The exact checker was run with Python 3 and the standard library.  The
high-precision audit used the installed `mpmath` package at 100 decimal digits.
Symbolic spot checks of the isolated values were also made with a Wolfram
Language kernel.  No numerical or computer-algebra output is treated as a
proof of a general identity.

## Scope warnings

- The report does not quantify over a completed type of all real or complex
  functions inside first-order iPRA.
- Analytic equalities are schemas for fixed primitive-recursive rational or
  complex-rational names and explicit certificates.
- The Lean files are outlines and were not compiled in the production
  environment.
- MathWorld equations (18)–(24) are numerically verified but their modular
  proofs are not reconstructed.
