# Simultaneous Convolution Divisors of Fabius-Type Laws

A prime-adic Hall criterion, finite certificates, linear rigidity, and a sharp
regularity transition. Research article prepared for the ProveIt project,
29 September 2026.

## Contents

- `article.pdf`: the complete 23-page article, with proofs, examples, source
  provenance, references, and nine proposed further research projects.
- `article.tex`: standalone LaTeX source; it does not import repository files.
- `verify.py`: exact finite certificate routines and reproducible tests.
- `verification.json`: output of the executed companion tests.
- `build.sh`: runs the tests and compiles the article in three direct passes.
- `SOURCES.md`: the full source links underlying the bibliography.

## Main result

Let p be prime and X_p = sum_{k>=0} p^(-k) U_k, with independent U_k uniform
on [-1,1]. A summable family of uniform widths a_j can be removed as an
independent convolution factor exactly when a_j = 1/n_j for positive integers
n_j and, for every K >= 0,

    #{j : v_p(n_j) <= K} <= K + 1.

The same condition is equivalent to entire extensibility of the Fourier quotient.
A nested matching supplies an explicit positive residual. The article extends
this to prime-power targets, gives finite tests for geometric streams, proves
coordinate-direction rigidity in several dimensions, and classifies residual
regularity from a digit-slack sequence.

Normalization matters: X_2 is supported on [-2,2]. The classical Rvachev up-law
on [-1,1] is the law of X_2/2.

## Reproduce the exact tests

Python 3.10 or later; standard library only. No network or package installation
is required.

    python verify.py --output verification.json

The recorded execution passed 9,100 finite-family cases, 8,855 geometric-family
cases, 96 uniform partition checks, 1,056 rational moment identities, and
153,390 period-drift identities. It also checked the base-six Laurent identity
and deliberate invalid-input/resource-limit cases.

These are finite implementation tests, not machine verification of the analytic
or infinite theorems. Those theorems are justified by the manuscript's proofs.

### Use the certificate routines

    from verify import Stream, finite_certificate, stream_certificate

    finite_certificate(2, [2, 3])       # accepted: widths 1/2 and 1/3
    finite_certificate(2, [1, 3])       # rejected: zero-order witness at 3*pi
    finite_certificate(2, [2, 3], power=2)  # target base 4, not base 2

    stream_certificate([Stream(1, 2), Stream(1, 2)])
    # Two streams with deadlines 1,3,5,...; accepted and critical.

`finite_certificate` takes the actual positive integer denominators. Its `power`
argument means that the target base is p**power. `stream_certificate` takes
valuation starts and steps for a prime-base target. The optional `finite`
argument contains additional finite deadlines, not denominators.

The finite-window algorithm can have a large least-common-multiple period.
A resource limit raises `ResourceLimitError`; it is never a rejection certificate.
Primality checking in the companion is elementary trial division, intended for
small prime bases rather than cryptographic-size inputs.

## Compile the article

Use a TeX installation with pdfLaTeX, Latin Modern, AMS packages, mathtools,
microtype, booktabs, tabularx, enumitem, fancyhdr, xurl, hyperref, and cleveref.

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

On a Unix-like system, `bash build.sh` runs both the tests and these three passes.
No bibliography processor or external figures are needed. Rebuilding may change
PDF metadata and binary hashes while preserving mathematical content and layout.

## Proof and novelty status

The article is a proof-bearing research manuscript. It has not been peer reviewed
or checked in Lean. The existing repository's scalar reciprocal-integer
single-copy theorem is explicitly treated as prior work, not as a new discovery.
The proposed extensions were developed after targeted source review; no exhaustive
repository audit or worldwide priority claim is made. The main arguments do not
assume the correctness of unverified repository research claims.

No repository files were modified or uploaded as part of preparing this package.
