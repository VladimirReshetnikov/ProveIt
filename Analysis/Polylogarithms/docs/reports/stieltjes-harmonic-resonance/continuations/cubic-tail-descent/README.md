# Cubic Invariant Tail Descent

Research continuation for Vladimir Reshetnikov's ProveIt program, 10 October 2026.

The article proves an all-degree depth-descent theorem for weighted symmetric
products of odd Hurwitz-zeta tails, including exact cubic and quartic moments,
a closed meromorphic symmetric-digamma cube, all-index algebraic Stieltjes
traces, Lerch/polylogarithmic order derivatives, and anchored antiderivatives.

## Main files

- `article.pdf`: the complete research article.
- `article.tex`: standalone LaTeX source; bibliography is included.
- `manuscript/cubic-tail-insert.tex`: a compact proposed manuscript insertion.
- `verification/verify.py`: reproducible exact and numerical checks.
- `verification/exact_results.json`: 596 passed exact assertions.
- `verification/numeric_results.json`: 31 passed numerical checks at 50 digits.
- `verification/coefficient_catalog.json`: all 35 coefficient identities with
  `0 <= a <= 4`, `2 <= d <= 8`, including weight and representation-depth bound.
- `notes/INTEGRATION.md`: placement, dependencies, and acceptance boundaries.
- `notes/SOURCE_AUDIT.md`: source scope, proof provenance, and audit findings.
- `notes/THEOREM_INDEX.json`: machine-readable theorem and status index.

The analytic proofs are in the article. Numerical checks are diagnostics, not
interval proofs. The exact program certifies finite polynomial and rational
identities, not the infinite-dimensional analytic hypotheses.

## Reproduction

Tested with Python 3.13.5, SymPy 1.14.0 and mpmath 1.3.0. The actual versions
are also recorded in each result file. A standard pdfLaTeX installation with
amsmath, amsthm, mathtools, lmodern, microtype and hyperref is sufficient.

```sh
python verification/verify.py --exact-only
python verification/verify.py --numeric-only --dps 50
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Running without either mode flag executes both suites and writes a combined
`verification_results.json`. No network access is used. To preserve delivered
results, replay in a working copy. Only mpmath and SymPy are required by the
Python program. Dependency versions are descriptive, not a requirement to
replace a working compatible environment.

## Provenance and limitations

Repository source anchor exposed by connector search:
`87c7db629552afbc2e803001526debe3430a31b0`.
The principal prior theorem is the first mixed Rogers–Dougall resonance in
`Analysis/Polylogarithms/docs/manuscript/chapters/07-mixed-dougall-identities.tex`.
The article includes a derivation of its required specialization, credits the
prior theorem, and develops its cubic invariant consequences.

The incoming ZIP inventory and intake instructions were read, but the binary
members of the incoming ZIPs were not audited. No live repository edits,
commits, extractions or integration actions were performed.

The Gaussian S6 and revised S8 conjectures remain open in this report.
There is no claim of historical priority for every special identity, no
arithmetic independence claim, and no Lean/proof-assistant verification claim.

This delivery is intended for review and integration under the repository's
existing intake policy. No separate license is asserted over upstream material.
