# Polylogarithm Certificates and Sharp Euler Bounds

**A research continuation for Vladimir Reshetnikov’s ProveIt project — 10 October 2026**

This package contains a comprehensive article, complete proofs, exact finite
certificates, reproducible numerical illustrations, and proposed integration
notes. It is based on ProveIt commit
`4c173c06cc32c9cea554b39be1837ad2ae897fc1`, including the manuscript and
all six archives then in `docs/incoming`. The repository has not been modified.

## Principal proved results

1. **The rational tetralogarithm conjecture is proved.** The six-argument
   formula at 1/2, 1/3, 2/3, 1/4, 3/4, and 1/9 follows from a printed
   42-row rational tensor certificate, exact lower-weight descent, and
   explicit branch and endpoint calculations. The same certificate proves
   a one-parameter functional identity and a further 25-argument rational
   specialization at parameter 1/3.
2. **The fractional Euler tail has a complete expansion.** A compensated
   integral works for every positive real outer and inner order, including
   total orders below one. Two sequences of logarithmic powers are needed.
   For integral inner order and nonintegral outer order, the combined
   coefficients have a proved factorial growth law.
3. **The fixed-total comparison has an exact phase description.** For outer
   order at least one, the axis dominates at every truncation and the
   positive differences have a Hausdorff moment representation. For outer
   order between zero and one, there is exactly one simple continuous
   truncation-order crossing. At half orders, exact rational arithmetic
   proves that the first positive integer comparison is N=21.
4. **The sharp global late-Euler asymptotic is proved.** The conjecture
   C_N−1 ~ c N^(−p) is established with its stated constants. For
   N ≥ ceil(exp(24)) = 26,489,122,130, the global supremum reduces exactly
   to the zero outer-order axis. The article also proves a second
   asymptotic scale, a maximizing-order displacement, monotone axis
   maxima and locations, and necessary concentration of near maximizers.
5. **The Lerch saturation bound is polynomial.** The reciprocal-gamma
   Appell mesh is at least 4/[n(n−1)(n−2)] for n≥3. A sufficient
   uniform derivative order is
   ceil((16+6n(n−1)(n−2)H_(n−1))²) ~ 36n⁶(log n)².
   The theorem counts all positive zeros, proves their simplicity, and
   gives a uniform logarithmic location error below 8/sqrt(k).

The article does not assert worldwide priority for identities obtainable
from classical functional equations. The proofs and status changes are
relative to the inspected project material. Numerical agreement is
distinguished from proof throughout.

## Package contents

| Path | Purpose |
| --- | --- |
| `ProveIt_Polylogarithms_Continuation_2026-10-10.pdf` | Complete article |
| `article.tex`, `abstract.tex`, `references.tex` | Standalone LaTeX entry point and supporting sources |
| `sections/` | Modular mathematical proof and research-agenda sections |
| `code/verify_tetra.py` and adjacent tetralogarithm JSON files | Exact tensor cancellation, endpoint descent, both rational specializations, and branch audit |
| `code/verify_fractional.py` | Integer specializations and rigorous half-order interval arithmetic |
| `code/verify_fractional_threshold.py` | Exact signs at N=20 and N=21; explicitly imports the adjacent fractional engine |
| `code/verify_polynomial_mesh.py` and adjacent JSON | Exact rational auxiliary roots, mesh bounds, moments, and finite thresholds |
| `code/verify_late_euler.py` | Exact derivative-polynomial checks and non-certified positive-integral diagnostics |
| `code/replay.py` | Replays the packaged checks and writes a structured receipt |
| `code/make_figures.py` | Recreates the publication figure from exact threshold data |
| `code/build_article.py` | Compiles the PDF and rejects unresolved references or overflowing boxes |
| `data/` | Frozen results, source provenance, environment versions, and replay receipts |
| `figures/` | Vector PDF and 300-dpi PNG of the Lerch threshold comparison |
| `integration/status_updates.md` | Exact source-path and theorem-label status map |
| `integration/manuscript_wording.patch` | A single proposed correction to an unsupported nonreducibility claim |
| `MANIFEST.sha256` | Checksums of the delivered files, excluding the manifest itself |

Keep the certificate JSON files next to their replay scripts. All script
paths are resolved relative to the package, so the checks do not depend on
the original workspace path.

## Reproduce the finite checks

Python 3.12 was used. The supplied `requirements.txt` records the versions
used for SymPy, mpmath, NumPy, and Matplotlib. No network access is needed
once these dependencies are installed.

From the package directory:

```bash
python code/replay.py
```

This checks the exact algebra, rational root isolation, interval signs,
and the independent tetralogarithm branch audit. It writes
`data/verification_receipt.json` and individual replay logs.

The delivered run passed:

- 42 tensor rows and all 230 touched tensor coordinates;
- the exact functional identity, the six-argument conjecture, and the
  additional 25-argument identity;
- 64 integer-density specializations and eight coefficient groupings;
- the two rigorous threshold signs at N=20 and N=21;
- all 135 auxiliary roots for 2≤n≤16 through rational isolation;
- 90 finite-multiplier coefficient identities and seven exact gamma
  moment inequalities;
- the Euler derivative-polynomial identities.

The dedicated half-order threshold script reuses
`verify_fractional.py`. It records that dependency and its SHA256 and
does not claim a second arithmetic engine. The all-N half-order
classification requires the article’s unique-crossing theorem as well
as the two finite signs.

## Reproduce the numerical illustrations

The longer Euler quadratures and optimizer table are numerical diagnostics,
not interval certificates or substitutes for the analytic proofs.

```bash
python code/verify_late_euler.py --optimizers --output-dir data
python code/make_figures.py
```

Alternatively, `python code/replay.py --numerical` adds the longer Euler
diagnostics to the standard replay. The option
`python code/verify_late_euler.py --quick --output-dir data/quick` produces
a shorter illustrative table without replacing the frozen full table.

The second Euler asymptotic correction converges very slowly. The
supplied data include large values up to N=10^10000 to illustrate this
point; they should not be treated as an effective finite-N remainder
estimate.

## Compile the article

A TeX Live installation with the packages loaded by `article.tex` and
the Latin Modern fonts is sufficient.

```bash
python code/build_article.py
```

The script runs pdfLaTeX three times. It rejects unresolved references,
duplicate page anchors, and overflowing horizontal or vertical boxes.
The delivered PDF was also rendered and visually inspected. A PDF reader
provides the table of contents and internal theorem/equation links.

## Integration and remaining questions

Use `integration/status_updates.md` to map the proved results to existing
labels and archive members. Preserve the original equation labels or
provide an explicit mapping. The mathematical sections can be adapted
into the manuscript, but the exact coefficient data should remain
adjacent to the tetralogarithm proof.

The wording patch was checked with `git apply --check` against the pinned
revision. It softens the claim about the imaginary part of Li_3(1+i)
to say that the displayed transformations do not reduce it to elementary
constants. It changes no formula and has not been applied to the repository.

The article leaves the Gaussian S_6, S_8, S_10, S_12 identities and the
higher golden reconstructions unresolved. It also leaves global axis
reduction at all smaller N, sharp Lerch saturation thresholds, optimal
Appell mesh, and effective second-scale remainders open. Two explicit
conjectures concern all-N axis reduction and the near-critical growth of
the unique reversal order. Their conjectural status is explicit.

No proof-assistant formalization or arithmetic independence of the
polylogarithm constants is claimed.
