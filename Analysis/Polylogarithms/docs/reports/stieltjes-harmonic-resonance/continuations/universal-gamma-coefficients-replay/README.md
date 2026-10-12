# Universal Gamma Normal Forms

A research continuation for Vladimir Reshetnikov's ProveIt project, 11 October 2026.

## Main result
Every canonical coefficient of the inverse-Gamma hierarchy has a single finite polynomial beta-integral formula (Theorem 3.1 in the article). It gives the complete sign/zero classification, the nonrecursive numerator polynomials for the second-derivative sector, and every coefficient of the third and all higher sectors. The coefficient of `u1*u3^3` in `N14` is `-3185/3`.

The exact harmonic-depth and polylogarithmic constructions are proved as consequences. The scalar Gamma–height-one Stieltjes bridge is explicitly credited to the inspected repository report. No numerical independence statement, proof-assistant certification, general unequal-tail conjecture solution, or global novelty certification is claimed.

## Files
- `article.tex`: self-contained LaTeX article; no external figure or bibliography file is needed.
- `article.pdf`: PDF edition; its build status is recorded in `results/build_report.json`.
- `code/verify_exact.py`: independent rational sparse IBP and beta-formula comparison through weight 28 by default.
- `code/verify_numeric.py`: 54 non-certified, 80-digit numerical diagnostics.
- `results/exact_report.json` and `results/exact_coefficients.csv`: exact replay results, when completed.
- `results/numeric_report.json`: diagnostic residuals and completion status, when completed.
- `integration/`: source provenance, scope, proposed integration, and recovered-artifact record.
- `SHA256SUMS`: checksums of all included payload files, excluding itself.

The recorded JSON status is authoritative; the presence of a test script is not itself evidence that a run completed. Exact finite checks supplement, but do not prove, the all-order results. Floating-point residuals are not certified enclosures.

## Reproduction

```sh
python3 code/verify_exact.py --max-weight 28
python3 -m pip install -r requirements.txt
python3 code/verify_numeric.py
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
sha256sum -c SHA256SUMS
```

The last command checks the originally delivered files; rerunning a verifier changes its timing record, so the original checksum of that JSON file will then differ. Source files remain unchanged by the verifiers. The exact verifier uses only the Python standard library. The numerical verifier requires `mpmath`.

The PDF build log and build report disclose any build warnings. If no TeX compiler is available, the build script may supply a clearly labelled source-text PDF rather than pretending that mathematical typesetting succeeded. The included LaTeX is the authoritative typesetting source.

## Prior work
A matching prior completed article, when recovered, is preserved under `prior_completed_article/` for continuity. The main `article.tex` is self-contained; the recovered source is not part of its build and may retain its original project dependencies.

No changes have been pushed to the ProveIt repository. Suggested integration is documented separately.
