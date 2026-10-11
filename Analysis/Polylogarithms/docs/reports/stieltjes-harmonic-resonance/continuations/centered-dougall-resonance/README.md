# Centered Dougall Resonance

**Exact Stieltjes Jets, Harmonic Identities, Polylogarithmic Subtraction, and Zeta Antiderivatives**  
Prepared for Vladimir Reshetnikov's ProveIt programme, 10 October 2026.

## Main result

The article answers the fixed-Dougall-family target in Section 9, question 1,
of the Gauss–Hurwitz continuation. For the normalized Rogers–Dougall 5F4
family, centering at `n + kappa` removes all odd inverse-power corrections.
A polynomial differential law cancels every lower Hurwitz counterterm at
every nonpositive integer spectral parameter. The resulting value is a
single explicit digamma expression with polar-counterterm coefficient

`rho_N = (-1)^N (d0)_N (1-b)_N (1-c)_N / N!`.

The Gamma-product residue itself is `rho_N/2`.

The article also proves a zero-safe formula for every spectral jet, an
interlaced half-integer zeta tower, harmonic/Stieltjes identities, all Euler
primitive endpoints of a first harmonic jet, and finite center-parameter
antiderivatives at every integral resonance.

The Rogers–Dougall summation and the parameter-differentiation and
negative-polygamma methods have classical antecedents. The article credits
these separately from the continuation developed here. Global literature
priority is not established. The S6 and revised S8 conjectures are not
resolved by this package. No repository files were changed remotely.

## Contents

| File | Purpose |
|---|---|
| `article.pdf` | The complete 22-page article, with proofs and eight further research questions. |
| `article.tex` | Standalone LaTeX source with embedded bibliography. |
| `code/dougall.py` | Gamma-safe Taylor arithmetic, coefficient generation, and evaluators. |
| `code/verify_exact.py` | 485 exact symbolic and rational regression assertions. |
| `code/verify_numeric.py` | 293 high-precision diagnostics, runnable in two parts. |
| `code/build_tables.py` | Regenerates exact truncation tables and the TeX-linked identity index. |
| `results/exact_checks.json` | Exact assertion counts and environment. |
| `results/numerical_checks.json` | All numerical parameters, values, residuals, and tolerances. |
| `results/document_preflight.json` | PDF page, reference, layout, and rendering checks. |
| `results/residue_table.json` | Exact residues and coefficient derivatives for six rational triples. |
| `results/half_parameter_coefficients.json` | The two terminating centered coefficient families through N = 12. |
| `identities.json` | Machine-readable index of the principal proved formulas and domains. |
| `integration/centered-dougall-resonance.tex` | A compact additive manuscript section with core proofs. |
| `integration/core-preview.pdf` | A compiled preview of that section. |
| `notes/SOURCE_AUDIT.md` | Inspected sources, identifiers, and audit limits. |
| `notes/CORRECTIONS_AND_GUARDS.md` | Required normalization and zero-handling safeguards. |
| `integration/README.md` | Suggested placement, bibliography, and review instructions. |
| `SHA256SUMS` | Integrity hashes for the delivered files, excluding this manifest itself. |

## Reproduce

The executed environment was Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0.
Only that Python environment is claimed to have been tested.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py --part 1
python code/verify_numeric.py --part 2
python code/build_tables.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The two numerical parts together execute the same assertions as
`python code/verify_numeric.py`. The split form is useful in constrained
execution environments. When both part reports exist, the program writes
the combined numerical report. No network is required after dependencies
and TeX packages are installed.

A small evaluation example:

```python
import sys
sys.path.insert(0, "code")
import mpmath as mp
from dougall import Params, collapsed, closed_resonance_jet

mp.mp.dps = 70
p = Params.parse("3/4", "2/3", "4/5")
print(collapsed(p, 2))
# The returned array contains ordinary Taylor coefficients, not derivatives.
print(closed_resonance_jet(p, N=2, m=3))
```

## Proof and diagnostic status

All central identities have analytic or algebraic proofs in the article.
The exact assertions are finite regression tests, not a proof-assistant
formalization. The numerical evaluations use finite asymptotic tails, not
rigorous interval enclosures. The largest observed scaled discrepancy over
all 293 diagnostics was `2.18454477481895e-48`; the finer central spectral
run had maximum `1.54137402015147e-58`. These observations do **not** certify
that many correct decimal places.

The denominator Gamma factors must be treated as entire reciprocal-Gamma
functions before taking jets. A summand that vanishes at a resonance may
have a nonzero derivative. In particular, the article's first-resonance
harmonic identity requires the explicit initial contribution `1/6`.

Re-running a test rewrites result files and timing metadata, so the
corresponding SHA-256 hashes change. The delivered manifest is an integrity
record of this package, not a mathematical certificate.

## Integrity check

On systems providing `sha256sum`, run `sha256sum -c SHA256SUMS` before
regenerating any outputs. The archive contains no external font files.
