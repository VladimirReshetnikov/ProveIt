# Gauss–Hurwitz Pole Cancellation

**Resonant gamma-ratio sums, harmonic identities, Stieltjes jets, and polylogarithmic endpoint subtraction**

A research continuation prepared for Vladimir Reshetnikov's ProveIt repository, 10 October 2026.

## Read first

`article.pdf` is the complete 23-page article. `article.tex`, `sections/*.tex`, and `references.tex` are its editable, self-contained LaTeX sources.

The main proved statements are:

- Theorem 2.2: normally convergent gamma-ratio/Hurwitz subtraction on `Re(u) > -K`.
- Theorem 3.4: every nonpositive-integer resonance has a short digamma evaluation.
- Theorem 4.1: every resonant spectral Taylor coefficient has a finite Stieltjes/Hurwitz formula, including degenerate numerator parameters.
- Theorem 5.3: every gamma-weighted complete even harmonic-tail sum equals `2*zeta(2k+1,x)`.
- Theorems 6.1 and 7.1: an exact antiderivative telescope and all-jet polylogarithmic endpoint subtraction.

The Gauss summation and hypergeometric constant-term background are classical. The article explicitly credits Bühring's related constant-term results and makes no global originality claim for individual specializations. It does **not** prove the repository's remaining S6 or S8 conjectures, or any transcendence/independence statement.

## Reproduce

With Python 3.10 or later and a TeX installation:

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The executed environment was Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0. No network is used by the scripts; dependency installation may require it. `make verify` and `make pdf` run the same commands. `make clean` removes TeX auxiliary files but preserves the PDF.

The delivered run has **512 exact regression checks** and **64 high-precision numerical diagnostics**, with maximum scaled discrepancy approximately `1.80742922933e-43` at 65 decimal working digits. The numerical tail is an asymptotic approximation, **not an interval certificate**. Analytic proofs establish the identities; the computations independently check formulas and conventions. There is no proof-assistant formalization.

## Important conventions

1. A jet `[t^m]` is a Taylor coefficient, not a derivative; multiply by `m!` to obtain the latter.
2. Sum the displayed **bracketed differences**, not their divergent components separately.
3. Reciprocal gamma is entire. A term that is zero at resonance can have a nonzero derivative. The simplest missing term would change a first jet by exactly pi.
4. The reference shift `c` fixes the subtraction convention. Its change is evaluated explicitly in the article.
5. Hypergeometric functions with exceptional lower parameters must be regularized by their coefficient series; do not numerically multiply a pole by zero.

## Package contents

- `code/gauss_hurwitz.py`: reusable exact coefficient/jet engine and numerical evaluators.
- `code/verify_exact.py`, `code/verify_numeric.py`: independent replay entry points.
- `results/*.json`: exact tables, proof-status index, numerical values and residuals.
- `integration/README.md`: suggested repository placement and dependency order.
- `integration/gauss-hurwitz-summary.tex`: a short manuscript-facing summary fragment.
- `integration/pslq-wording.patch`: optional minimal wording correction for the inspected canonical chapter.
- `notes/SOURCE_AUDIT.md`: source provenance, inspected scope, and limits.
- `notes/PRIOR_ART.md`: classical-input and priority distinctions.
- `SHA256SUMS`: checksums of delivered files other than this checksum file.

The optional patch was prepared against an inspected source context at commit
`e0d9463bdee9685dfb1dddb819059cc738540c57`. The repository itself was not modified. Check the patch against the current branch before applying it. Earlier incoming packages were inspected only to avoid duplicating their correlation/primitive work; they are not bundled here.

Rerunning tests changes their recorded elapsed-time fields and therefore the result-file checksums. The manifest describes the delivered snapshot, not every future rerun. No font files or third-party source archives are included.
