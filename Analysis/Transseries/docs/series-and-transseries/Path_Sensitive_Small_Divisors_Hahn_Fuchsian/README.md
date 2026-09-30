# Path-Sensitive Small Divisors in Hahn–Fuchsian Systems

**Exact convergence criteria, resonance amplification, and stable analytic renormalization**  
Research report prepared for Vladimir Reshetnikov — 29 September 2026.

## Read

`path_sensitive_hahn.pdf` is the 21-page article. Its editable source is
`path_sensitive_hahn.tex`. The source includes an embedded bibliography and
loads the supplied `results/crossover_table.tex`.

## Research target and results

Section 11 of the ProveIt Hahn–Fuchsian manuscript asks for a universal
convergence criterion when the permitted coefficient supports and matrix
directions are smaller than the whole exponent semigroup. It specifically
suggests a triangular three-dimensional system with an accumulating
two-letter sumset.

This article resolves the question for any finite acyclic matrix pattern,
a real diagonal constant matrix, positive well-ordered real edge supports,
and independently variable scalar edge coefficients. Exact resonances are
allowed. For a directed path p, let E_p be its exponent sumset and rho_p its
endpoint spectral difference. Universal absolute convergence holds exactly
when every E_p has a positive gap from rho_p after exact equality is removed.
Equivalently, rho_p is not a left accumulation point of that same path's sumset.

Theorem 5.1 gives the exact weighted independent-input criterion using an
explicit polynomial-logarithmic path kernel. Theorems 6.1 and 7.3 give the
unweighted gap equivalence and its transfer to the normalized log-free gauge.
Failure yields arbitrarily small inputs whose normalizer diverges absolutely
at every positive radius. Examples show why both the whole-semigroup test
and an edge-by-edge test can give the wrong answer.

Theorem 9.1 constructs an r-dimensional resonant chain with the exact
normalization condition sum(n^(r-1) |c_n|) < infinity, although the original
input only needs sum(|c_n|) < infinity. For c_n = n^(-p), the sharp thresholds
are p > 1 for the input and p > r for the gauge. Theorems 10.1 and 11.1 give a
stable analytic realization under the weaker input condition, fixed-prefix
asymptotics, and a uniform accumulation crossover with an explicit error bound.

Section 13 develops ten further research directions, including cycles,
nonzero Jordan constant terms, correlated matrix directions, optimal weights,
moving spectra, multiplicative realization, nonlinear tree kernels, effective
infinite supports, irregular sectors, and formal verification.

## Mathematical status

The article supplies conventional mathematical proofs. It does not claim a
Lean formalization, independent peer review, or established worldwide priority.
The novelty comparison is targeted to the inspected repository questions and
selected primary literature, not an exhaustive audit of every repository file.
Classical Frobenius normalization and general transseries foundations are credited.

The acyclicity, diagonal constant term, positive well-ordered supports, and
independent edge-input hypotheses are retained explicitly. The criterion is
universal over an input class, not necessary for every individual input with
special cancellations. The analytic realization theorem is for the explicit
resonant chain, not an unrestricted summation theorem for all Hahn series.

## Rebuild the PDF

A standard TeX Live installation with pdfLaTeX and the packages listed in the
source preamble is sufficient. From this directory, run:

```sh
sh build.sh
```

This performs three passes in `build/` and replaces `path_sensitive_hahn.pdf`.
It does not regenerate or overwrite the recorded verification results. No
bibliography processor, repository checkout, network access, or private fonts
are required. For a manual build, run pdfLaTeX three times on the main source
from this directory, keeping `results/crossover_table.tex` in place.

## Reproduce the computational checks

Python 3.10 or newer and mpmath are sufficient. The executed environment was
Python 3.13.5 with mpmath 1.3.0. Run without Python's `-O` flag, because the
verification uses assertions.

```sh
python -m pip install -r requirements.txt
python verification/verify.py --outdir build/recheck
```

The optional output directory keeps the distributed results unchanged. Omitting
`--outdir` writes to `results/`, including the table used by the article.
The recorded seed is 20260929. The successful run contains:

| Check | Count |
| --- | ---: |
| Scalar polynomial-inverse identities | 105 |
| Kernel degree and leading-coefficient identities | 210 |
| Finite triangular systems | 30 |
| Differential-equation entry checks | 540 |
| Normalized-gauge entry checks | 540 |
| Constant-connection entry checks | 540 |
| Weighted path bounds | 349 |
| Resonant-chain formulas | 49 |
| Numerical crossover cases | 96 |

The finite algebra uses exact rational arithmetic. The numerical illustrations
use 75 decimal digits and analytic bounds on truncated positive series, but are
not directed-rounding interval certificates. Neither the finite checks nor the
numerical evaluations replace the infinite-support proofs or establish their
universal quantifiers.

## Contents and provenance

- `path_sensitive_hahn.tex`, `path_sensitive_hahn.pdf`: article and compiled PDF.
- `verification/verify.py`, `requirements.txt`: reproducible checking program.
- `results/verification.json`, `results/crossover_table.tex`: actual recorded run.
- `build.sh`: PDF build script.
- `notes/proof_audit.md`: hypotheses, dependencies, and verification boundaries.
- `notes/repository_provenance.json`: pinned sources and inspection scope.
- `notes/build_report.json`: actual compilation and visual-check record.
- `SHA256SUMS`: delivery-file integrity ledger.

Repository: `VladimirReshetnikov/ProveIt`. Pinned snapshot reference:
`9250bbf8af80dacf7b252d9d0320b122c80961ba`.
Sources were read through the connected GitHub tools; primary public literature
was checked separately. No repository files were changed. External source
corpora and font files are not redistributed in this package.
