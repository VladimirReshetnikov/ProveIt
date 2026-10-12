# Resonant Polylogarithm Inversion

**Uniform Order Crossover, Gamma–Zeta Fold Loci, and Convergent Exponential Sectors**  
Research contribution prepared for Vladimir Reshetnikov with OpenAI assistance.  
Project date: 11 October 2026.

## Read first

`article.pdf` is the complete article; `article.tex` is its editable source.
The package is self-contained and does not modify the ProveIt repository.

The main candidate contributions are the moving-order primary/secondary
inverse charts, the all-integer Gamma–zeta critical-locus formula, the
exceptional undetuned dilogarithm fold, and the leading coefficient of every
exponential sector of its two inverse branches. Classical continuation,
Gamma expansions, Lambert reductions, analytic implicit functions, and
square-root mechanisms are explicitly credited.

For a representative theorem, fix `lambda_k = 2*pi*i*k`, `k != 0`, put
`epsilon = lambda_k/X`, and let `X` tend to positive infinity. The equation

    zeta(2+epsilon) - Li_(2+epsilon)(exp(-t)) = exp(-X)

has exactly two roots in a fixed sufficiently small neighborhood of
`t/exp(-X) = 1`, counted locally, with

    t_+/- = exp(-X) * [1 +/- sqrt(-2*K*lambda_k/X)
                       + (1-gamma-4*K/3)*lambda_k/X + O_k(X^(-3/2))],
    K = gamma_1 + ((gamma-1)^2 + zeta(2) + 1)/2 > 0.

Both roots belong to the same local logarithm branch. Their full expansions
are convergent in `X^(-1/2)` and `X*exp(-X)`. The article gives an explicit
binomial formula for every additional exponential action, not just the
first correction.

## Evidence and limits

All named mathematical results have conventional proofs in the article.
This is unrefereed work, not a Lean formalization. Global publication
priority is not established by the bounded literature search.

Two fresh computational replays passed:

- 150 exact symbolic assertions (SymPy 1.14.0).
- 73 floating-point diagnostics at 180 decimal digits (mpmath 1.3.0).

The numerical checks are not interval certificates, do not prove root
counts, and do not establish independence of any constants. Direct
polylogarithm and normal-form evaluations are different routes in the same
numerical library, not two independent software engines.

The audit confirms a historical overstatement already superseded by the
canonical editorial ledger. It does not claim a newly discovered false
statement in the current canonical material, or an exhaustive corpus audit.

## Contents

| File or directory | Purpose |
| --- | --- |
| `article.tex`, `article.pdf` | Complete manuscript and compiled reading copy |
| `code/verify_exact.py` | Finite exact coefficient, residue, and elimination checks |
| `code/verify_numeric.py` | Direct evaluations and inverse/critical-point diagnostics |
| `results/` | Complete receipts, symbolic coefficients, numerical table, validation record |
| `provenance/` | Source identifiers, read scope, search log, attribution boundaries |
| `integration/` | Proposed placement, result-by-result status, historical note |
| `requirements.txt`, `Makefile` | Replay and build configuration |
| `SHA256SUMS` | Content checksums, excluding the checksum file itself |

## Replay

Python 3.13.5 was used for the supplied receipts. The scripts use standard
Python syntax compatible with Python 3.10 or later; only the tested runtime
is claimed as executed.

    python -m pip install -r requirements.txt
    python code/verify_exact.py
    python code/verify_numeric.py --dps 180
    make pdf

`make verify` runs both mathematical check programs. The numerical replay
can take several minutes. Use at least 180 decimal digits for the supplied
fixed comparison tolerances; the default is 180. No network is needed after
dependencies are installed. A TeX installation with the packages listed in
the manuscript preamble is needed to rebuild the PDF.

`make clean` removes TeX auxiliary files only. It does not remove the PDF,
mathematical receipts, or source files.

## Integration

Suggested primary placement:

    Analysis/Polylogarithms/docs/reports/resonant-polylogarithm-inversion/

Add a cross-link in the Transseries research registry. Full details and
scope-preserving summary text are in `integration/INTEGRATION.md`. No commit,
pull request, upload, or remote file change was performed.
