# Central Poupard Numbers

**Two OEIS conjectural statements, complete asymptotic sectors, and a universal transition for shifted moments**

Research article prepared for Vladimir Reshetnikov, 1 October 2026. The PDF has 28 pages.

## Main results and their scope

The article studies

    T_n = (2n+1)! [z^(2n+1)] tan(z),
    A_n(c) = sum_{k=0}^n binomial(n,k) c^(n-k) T_k.

The central Poupard numbers are a_n = A_n(1), OEIS A125054.

Theorem 3.3 proves the continued fraction labeled conjectural in the inspected OEIS entry (Peter Bala, 15 December 2025). Theorem 4.1 proves a_n = 3 modulo 9 for every n >= 1, stronger than the displayed observation that the 3-adic valuation is one. The proofs are all-index arguments using formal continued fractions and weighted paths, not extrapolations from the supplied tests.

The analytic development gives exact convergent odd-pole sectors with a positive tail bound (Theorem 6.1), arbitrary-order expansions of each fixed sector (Theorem 6.2), a uniform all-order endpoint-saddle expansion for c = tau n^2 (Theorem 8.1), the displaced coexistence window and probability laws (Section 9), and a universal leading transition for moments of y^p under an exponentially decaying probability tail (Theorem 10.1). Positivity promotes the real transition to a locally uniform complex limit and locates an array of simple polynomial zeros (Theorem 11.1). Section 12 gives Lambert-W inverse corrections and an exponentially small displacement relative to an exact one-sector inverse.

The central transition has tau_* = 0.2624665433684190267... and a logarithmic finite-size displacement. The exact definitions, not these floating-point digits, are the mathematical statements. For the universal theorem p > 1 is essential. The full all-order assertion is proved for the tangent model; an arbitrary tail with only a relative O(1/y) description receives a leading transition theorem, not an unsupported all-order claim.

The leading asymptotic for a_n already appears in OEIS with a 2015 attribution to Vaclav Kotesovec. It is not claimed as new. The tangent and Poupard generating functions, classical fraction operations, and structural moment consequences are also credited as prior mathematics. Worldwide publication priority for the broader extensions has not been established. These are ordinary mathematical proofs, without independent peer review or Lean formalization.

Section 14 proposes eight further research directions and a staged formalization route.

## Package contents

- `article.tex`, `article.pdf`: complete editable source and the compiled 28-page article. The TeX source requires the included `data/*.tex` fragments.
- `code/verify.py`: exact finite tests, coefficient generation, and numerical diagnostics; no network access is used.
- `data/verification.json`, `data/verification_run.txt`: recorded results and stdout from the full run.
- `data/*_table.tex`, `data/log_coefficients.tex`: reproducible fragments used by the article.
- `PROVENANCE.md`: inspected source URLs, repository snapshot, novelty and trust boundaries.
- `requirements.txt`, `Makefile`: reproducibility instructions and convenience targets.
- `BUILD_REPORT.json`: actual build, replay, and PDF validation results.
- `SHA256SUMS`: integrity ledger for the delivered files, excluding the ledger itself.

No third-party papers or font files are bundled. The fonts embedded in the PDF are ordinary typesetting resources.

## Reproduce

The recorded environment used Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, and pdfLaTeX from TeX Live 2025. Python 3.10 or later is required by the code; the recorded run itself was on 3.13.5.

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py --max-n 4096 --dps 90
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without `latexmk`, run this command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The PDF can be rebuilt without rerunning Python: all generated table fragments are included. A TeX installation with Latin Modern, AMS packages, geometry, booktabs, microtype, enumitem, xurl, hyperref, fancyhdr, and titlesec is sufficient.

The full Python command overwrites the generated data files. Work on a copy to preserve the delivered run. A shorter diagnostic that preserves the article's tables is:

```sh
python code/verify.py --max-n 512 --dps 90 --output-dir data/quick
```

`--max-n` must be at least 256; `--dps` must be at least 80 because the diagnostic thresholds are absolute high-precision thresholds. The exact finite test ranges remain unchanged in a shorter run. Lowering `--max-n` changes the large-index transition diagnostics, not the mathematical assertions.

With GNU Make, `make verify` regenerates the full recorded data and stdout, `make pdf` builds the PDF, and `make clean` removes TeX auxiliary files without removing the PDF or data.

## Verification boundary

The code checks the tangent and conjectured continued fractions through degree 48, the Poupard recurrence through row 24, the congruence through index 256, and two Hankel product formulas through order 6 at shifts 0, 1, and 3. It derives rational correction polynomials through order 8 and independently checks the first saddle correction by differentiation. Integral comparisons, sector remainder comparisons, transition values, inverse errors, gamma-model tests, and complex root residuals use high-precision floating-point arithmetic.

All recorded tests passed. Floating-point values and small root residuals are not interval enclosures, proofs of finite-index root uniqueness, or formal proof certificates. The all-index identities, asymptotic estimates, and eventual zero statements are justified by the proofs in the article. The complex-zero convergence is qualitative: a real-axis error estimate is not silently promoted to an identical complex error estimate.

The repository and OEIS were not modified, and no submission to OEIS was made.
