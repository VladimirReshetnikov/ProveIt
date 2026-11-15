# Apéry's theorem in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

## Result

This package contains a fully developed, human-readable finite arithmetic
proof of Apéry's theorem, with a quantitative constructive conclusion.
Let

\[
Z_M=\sum_{j=1}^{M}j^{-3},\qquad
a_n=\sum_{k=0}^{n}\binom nk^2\binom{n+k}{k}^2.
\]

For a positive denominator q, define

\[
n=42^{q+1},\qquad h=(n+1)^3a_{n+1},\qquad N(q)=a_nh.
\]

For every integer p, the proof establishes the entirely finite disjunction

\[
\frac pq+\frac1N<Z_N
\quad\lor\quad
Z_N+\frac1{2N^2}+\frac1N<\frac pq.
\]

The interval `[Z_N, Z_N+1/(2N²)]` contains every later partial sum and
represents the usual zeta value. Thus the result proves irrationality with
an explicit positive separation from every rational. All witnesses and
cutoffs are primitive recursive. The large bound is chosen to simplify the
proof, not for practical evaluation.

## Contents

| File | Purpose and status |
| --- | --- |
| `apery_ipra.pdf` | Compiled mathematical article. |
| `apery_ipra.tex` | Complete LaTeX source, including the proof, iPRA induction audit, and Lean plan. |
| `lean/AperySpec.lean` | Explicit finite arithmetic definitions and final checker; uncompiled. |
| `lean/FiniteAlgebraSpec.lean` | Finite polynomial/rational-function and auxiliary definitions; uncompiled. |
| `lean/AlgebraCertificates.lean` | Proof scripts for fixed polynomial and numerical certificates; uncompiled. |
| `lean/ObjectTheoryTarget.lean` | The exact internal iPRA target and conditional transport through ConciseIPRA; uncompiled. |
| `lean/FORMALIZATION_ROADMAP.md` | Detailed path from the definitions to a completed internal Lean derivation. |
| `code/verify.py` | Exact symbolic and rational regression checks. |
| `code/verification_report.json` | Successful output from the verifier. |
| `references/REPOSITORY_AUDIT.md` | Pinned ProveIt interfaces, inspected draft status, and certification boundaries. |
| `references/provenance.json` | Source URLs and exact repository revision. |
| `Makefile` | Ordinary PDF and verification commands. |
| `SHA256SUMS` | Checksums of the deliverable files. |

## Proof architecture

The classical Nesterenko–Zudilin rational function supplies the approximation
coefficients. A finite partial-fraction functional derives the recurrence
without assuming irrationality or comparing coefficients of actual zeta
values. The exact Wronskian and a rational growth bound give small positive
errors. Explicit auxiliary cutoffs replace all limit arguments. A short
Hanson-style multinomial calculation proves only the sparse denominator
bound needed here:

\[
\operatorname{lcm}(1,\ldots,42^k)^3\le28^{42^k}.
\]

A decidable integer comparison then gives the displayed two-branch
separation certificate. The proof uses no real integration, prime number
theorem, asymptotic factorial estimate, choice principle, or induction over
arbitrary formulas.

## Exact status

The complete mathematical argument and the finite iPRA proof audit are in
the article. The Python certificate and regression checks have passed.

**The Lean files are an uncompiled specification and formalization outline,
not a completed machine-checked proof.** No Lean/Lake/Elan toolchain was
available in the authoring environment. Missing proofs are explicit
obligations; they are not supplied as axioms or `sorry` terms. Conditional
transport theorems do not assert that their internal-proof hypotheses have
been constructed.

A complete formalization must construct a term of type
`Prf PRAAx [] aperyFormula` in the repository's object language. An ordinary
Lean theorem about real zeta, an external proof that the checker computes
zero, or finite testing alone does not provide that internal derivation.

## Reproduce

For the PDF, use a normal TeX Live installation:

```sh
make pdf
```

For exact certificate and regression checks, use Python 3.10 or newer with
SymPy installed:

```sh
make verify
```

The verifier does not attempt to compute the astronomical sum `Z_N` in the
universal witness. Its polynomial certificate check is symbolic. The
finite-range checks catch transcription and normalization errors; the
article's arguments prove the universal statements.

The inspected ProveIt revision is
`d72c8b24637e342816dc92d11bef337748683e51`, with declared Lean and Mathlib
version 4.32.0. Integration/build instructions and all remaining internal
proof obligations are in the Lean roadmap. No change was committed or
pushed to the repository.

## Attribution

The rational function and telescoper are classical; see Wadim Zudilin,
*An elementary proof of Apéry's theorem* (2002), arXiv:math/0202159.
The sparse denominator argument is a self-contained variant of the
multinomial method in Denis Hanson, *On the product of the primes* (1972).
The package claims a complete finite presentation and explicit iPRA
arithmetization, not a new discovery of Apéry's theorem.
