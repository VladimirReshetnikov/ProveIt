# Alternating Tails and Higher Spectral Defects

Research continuation for Vladimir Reshetnikov's ProveIt programme, 11 October 2026.

**Repository anchor:** `73f18ef013d5b74eafc883efb2c15210642df12a` (11 October 2026, 18:22:01 UTC).

## Read and build

- `Alternating_Tails_and_Spectral_Defects.pdf` is the complete article.
- `Alternating_Tails_and_Spectral_Defects.tex` is the complete standalone source.
- `article.tex`, `preamble.tex`, `sections/`, and `references.tex` are the modular source.
- `build_article.py` regenerates the standalone source, so edits should normally be made in the modular files.

```bash
python build_article.py --compile
```

This uses `latexmk -pdf` and a standard TeX Live installation with Latin Modern, AMS packages, mathrsfs, microtype, booktabs, longtable, enumitem, fancyhdr, hyperref, and bookmark. It needs no bibliography download or network access.

## Results and scope

1. A finite adjacent-tail certificate proves a rational-tail square law. Its continuous-order extension gives ordinary convergent all-index generalized Stieltjes identities, a sine-square resolvent evaluation, mixed-order polygamma convolutions, and an anchored Gamma primitive.
2. A cyclotomic rational-tail generator works at every conductor with an arbitrary outer character. It reduces the specified conjugation/parity sector to a finite trigonometric and digamma expression. Explicit conductor-four examples and their Gamma primitive are included.
3. Every spectral derivative of the conjugate-factor defect is computed for every polynomial weight. The formula includes both an ordinary convergent logarithmic sum and all finite Hurwitz/Stieltjes terms, including the extra coefficient supplied by a pole. No nonzero polynomial has an identically vanishing second defect as a function of the positive mass.
4. The second derivative for any number of quadratic factors is evaluated for every even polynomial weight. Its logarithmic correction is a normalized double primitive of an explicit digamma divided difference. Every coincident-mass coefficient has a finite polygamma/Bernoulli evaluation.
5. Exact Bernoulli congruences prove full first-prefix formal rank for order eight outside `b = 8001 mod 16384` and for order ten outside `b = 962 mod 2048`, with all required small cases verified exactly. The exceptional progressions remain open.

The general gap-six and arbitrary unequal-order rank conjectures remain open. The Gaussian weight-six and revised weight-eight conjectures are not settled here. Classical colored parity and the first-derivative multiplicative anomaly are credited as background. Novelty is relative to the inspected project corpus; global literature priority and proof-assistant formalization are not claimed.

## Reproduce the verification

The recorded environment used Python 3.12.14, SymPy 1.14.0, and mpmath 1.3.0. Install the two dependencies from `requirements.txt` in your preferred environment.

```bash
python verification/run_all.py
```

Independent suites can run concurrently with `--jobs 2` (or a larger value up to 5). The programs rewrite result JSON files; run in a copy to preserve the delivered evidence. The full determinant replay rebuilds both multivariate polynomial identities and all modular/base-case checks. Its quick mode intentionally omits the two large determinant reconstructions:

```bash
python verification/verify_rank_refinement.py --quick
```

The delivered full replay passed. The two analytic exact suites contain 290 assertions in total. There are 62 independent numerical diagnostics at 60–75 decimal digits. Numerical agreement is not an interval certificate or an infinite-family proof. The determinant certificate uses exact rational and modular arithmetic throughout and is counted separately from the 290 assertions.

## Package contents

| Path | Purpose |
|---|---|
| `sections/` | Full proofs, source reconciliation, and 14 concrete research questions |
| `verification/` | Portable Python replay programs |
| `data/rank_*_certificate.json` | Sparse exact order-eight and order-ten determinant numerators |
| `data/direct_rank_checks.json` | Original finite source-matrix determinants and ratios |
| `data/*verification*.json`, `data/rank_refinement_checks.json` | Recorded exact and numerical outputs |
| `data/claim_ledger.json` | Proved, inherited, advanced, and open claims with source question mapping |
| `data/provenance.json` | Repository pin and inspected source/archive metadata |
| `INTEGRATION_NOTES.md` | Thematic placement, source updates, and qualifications to retain |

No repository file was edited or pushed. Suggested destination: a continuation report under `Analysis/Polylogarithms/docs/reports/`, cross-referenced by the harmonic-tail and spectral/Stieltjes themes. Keep the delivered package and its proof-status distinctions intact during placement; later unified-manuscript editing can use the modular sections.

