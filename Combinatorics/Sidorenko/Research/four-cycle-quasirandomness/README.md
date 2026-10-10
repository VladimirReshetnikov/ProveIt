# Beyond the Fourth-Root Bound
## Exact Local Extremizers for Four-Cycle Quasirandomness

Research manuscript prepared with ChatGPT, October 8, 2026.

The package contains a self-contained proof of an exact local strengthening of the classical edge/four-cycle quasirandomness implication. It does not claim a resolution of a major named conjecture or an improved graph-algorithm complexity exponent.

## Main result

For a kernel `W : [0,1]^2 -> [0,1]` of mean `p`, let `D = t(C4,W)-p^4`, using homomorphism counts, and let the cut norm test indicator sets. If `E_p(D)` is the greatest cut discrepancy with cycle excess at most `D`, then for fixed `0<p<1` and sufficiently small positive `D`,

```text
E_p(D) = p Psi(t),   t = D^(1/4)/p,
Psi(t) = t/4 + t^3/4 + t^4/4 - t^5/8 - 3 t^6/4 + O(t^7).
```

The same value holds for symmetric graphons. Every extremizer is a unique two-block kernel up to relabeling, with a small degree imbalance and a small imbalance in the class masses. The article gives an exact algebraic endpoint description, not only a series.

Additional proved results are a degree-coupling inequality with optimal coefficient 3/2; the all-scale bound `cut <= D^(1/4)/4 + 2 D^(3/4)/(3 p^2)`; a near-extremizer compression estimate; and a weighted finite-realization loss at most `3 D^(1/4)/(4 n^2)`, with diagonal weights allowed. Simple graphs realize the curve in the limit; exact finite simple-graph attainment is not claimed.

## Files

- `article.pdf`, `article.tex`: article and complete LaTeX source.
- `references.bib`, `article.bbl`: editable and prebuilt bibliography.
- `code/verify_exact.py`: exact rational and symbolic checks.
- `code/endpoint.py`: high-precision stationary-branch evaluator and algebraic parametrization.
- `code/diagnostics.py`: numerical endpoint, cut, and rounding diagnostics.
- `code/build_pdf.py`: portable TeX build wrapper, including `bibtex.original` fallback.
- `results/`: actual exact/numerical run outputs, CSV values, and PDF verification summary.
- `docs/SOURCE_AUDIT.md`, `docs/PROOF_STATUS.md`: provenance, novelty boundary, and review notes.
- `SHA256SUMS`: checksums of package contents other than the manifest itself.

## Reproduce

Python 3.10 or later and a standard TeX installation are needed. The supplied computational runs used Python 3.13.5, SymPy 1.14.0, and mpmath 1.3.0. No internet access is needed after dependencies are installed.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/diagnostics.py
python code/endpoint.py --t 0.01 --sign -1 --dps 80
python code/build_pdf.py
```

On systems with Make, `make all` runs the same workflow. The build wrapper uses the included prebuilt bibliography when BibTeX is unavailable. Bibliographic changes require a working BibTeX executable.

`--sign -1` is the locally winning negative-discrepancy branch. `--sign 1` computes the positive branch for comparison. The code allows `0<t<=0.25` for numerical exploration; **0.25 is not a rigorously certified theorem radius**. Program output is a stationary branch, whose global optimality is proved only in the existential local neighborhood from the article. Numerical output beyond that neighborhood must not be labeled globally extremal without an additional certificate.

## Checks actually run

The exact verifier passed on all 512 binary 3-by-3 matrices and 120 seeded rational matrices, as well as symbolic operator identities, the implicit-function Jacobian, both signed Taylor expansions, the curvature calculation, the inverse series, and rational sharpness witnesses. The numerical diagnostics passed 48 groups at 80 decimal digits. These computations support the written proofs; they are not proof-assistant certification, interval certificates, or a substitute for universal arguments.

## Novelty and scope

The fourth-root exponent and the balanced regular obstruction are classical. The proposed research contributions are the exact local envelope, higher-order coefficients, equality classification, and related quantitative consequences. The literature search was targeted, not exhaustive. The manuscript has not undergone independent peer review, and priority has not been established. No theorem from the supplied `openai/math` repository is assumed; that repository provided methodological inspiration only. See the article and scope audit for the precise limitations.
