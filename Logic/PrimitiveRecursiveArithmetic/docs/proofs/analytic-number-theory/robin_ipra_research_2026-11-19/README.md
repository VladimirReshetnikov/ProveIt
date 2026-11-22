# Robin's theorem and intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 19 November 2026.

## Status

**This archive does not contain a completed proof of Robin's equivalence in iPRA.**
It contains complete human proofs of finite constructive components, exact
finite arithmetic certificates, a compiled constructive Lean logical core,
and a detailed specification of the remaining analytic and object-theory work.
No impossibility or independence result is claimed.

The requested theorem is

    RH iff, for every n >= 5041, sigma(n) < exp(gamma) * n * log(log(n)).

This equivalence is distinct from proving RH itself.

## Start here

- paper/report.pdf: the complete research report.
- paper/report.tex: main LaTeX source, with the four included section files.
- lean/RobinCertificateLogic.lean: locally compiled constructive logical
  reductions and bounded search.
- certificates/summary.json: exact finite verification results.
- sources/proveit_audit.md: pinned repository audit and proof boundaries.

## Mathematical results supplied

1. Explicit rational log, Euler-constant and exponential enclosures with
   primitive-recursive precision schedules.
2. Exact verification for every integer from 2 through 100,000, including all
   strict failures in that range. All 99,999 signs were decided.
3. An elementary proof of Robin's inequality for every n >= 5041 with at most
   three distinct prime factors.
4. A complete finite LCM reduction: for m >= 16, a certified inequality
   -log(F(m^2)) > 12/m produces a strict Robin counterexample at
   lcm(1,...,m^2). Here
   F(P) = exp(gamma) log(theta(P)) product_{prime p<=P}(1-1/p).
5. A proof-theoretic transfer result: an actual classical PRA proof of the
   appropriately encoded Pi1--Pi2 equivalence would suffice for iPRA.

The RH-dependent weighted explicit formula, sharp exponent budget, and
Nicolas--Landau converse have not been internalized in iPRA in this work.
The eta/winding zero checker is specified in detail but not implemented.
The report identifies each obligation separately.

## Reproduce the arithmetic

Python 3.10 or later, standard library only:

    python3 code/robin_certificates.py --verify certificates/finite_robin_certificates.csv

Regenerate the same table:

    python3 code/robin_certificates.py --limit 100000 --output certificates

Independent exact-rational audit:

    python3 verification/independent_arithmetic_audit.py

All acceptance decisions use integers or exact fractions. No floating-point
value decides an inequality. The independent audit uses rational polynomial
references and independent prime-factor divisor sums.

The finite computation is not itself a universal theorem or a formal iPRA
proof. It does not cover the large finite startup range required by the
classical analytic proof.

## Reproduce the checked Lean core

The included lean/lean-toolchain pins Lean 4.32.0.
From the lean directory:

    lean RobinCertificateLogic.lean

No Mathlib dependency is needed. All eight printed axiom checks are empty.
The conditional criterion theorem visibly takes the missing analytic
transformations as hypotheses; it is not advertised as Robin's theorem.
An arbitrary Lean function parameter is not automatically primitive recursive.

## Rebuild the PDF

From the paper directory, with a normal LaTeX distribution:

    pdflatex -halt-on-error report.tex
    pdflatex -halt-on-error report.tex

The report uses standard LaTeX packages and includes its bibliography.

## Sources and verification

ProveIt was inspected at
eb8eb6653c85aa44f1e18dd4efa243f41b5a9e98.
Selected source snapshots and their original license are under
sources/proveit; these are evidence/reference copies, not a standalone build
of ProveIt or all of its dependencies. Their manifest gives exact paths,
immutable URLs and Git blob hashes.

The external classical Lean project kimihiro64/Robin1984 was inspected at
acab1a31f31e0499518a4416b63281e0b4838f9c.
Its reported kernel audit was not independently replayed here. Its proof
organization is a useful source, but is not an iPRA proof.

Verification records distinguish:

- locally compiled Lean logical lemmas;
- executed finite arithmetic and independent arithmetic checks;
- mathematical source inspection;
- human proofs not yet translated into object derivations;
- remaining analytic obligations.

SHA256SUMS.txt records the substantive archive files.
