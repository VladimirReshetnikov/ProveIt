# Arithmetic Spectral Jets
## Stieltjes residues, Gamma reciprocity, and polylogarithmic untwisting

Research continuation prepared for Vladimir Reshetnikov's ProveIt programme, 10 October 2026.

## Read first

`article.pdf` contains the complete article and proofs. `article_singlefile.tex`
compiles without any other source file. `article.tex` is the modular master;
its section files are under `sections/` and its bibliography is `references.tex`.
All new theorem/equation labels use the prefix `asj:`.

The concrete research target is Q10 (arithmetic/nonpolynomial multiplicities)
in **Resonant Gamma Jets and Directional Zeta Identities**, inspected at
`3fdd6cc447fac0731801588723109ec3b2e21cec`.

## Main proved results

- A normally convergent finite-pole transfer theorem, all normalized Laurent
  jets, and every finite local difference above the ordinary Taylor degree.
- Complete quasi-polynomial mean/oscillation separation; a two-pole
  sum-of-divisors example; independent multiplicative Hurwitz lattices with
  every generalized-Stieltjes residue layer.
- Higher-pole Vandermonde alternants, including a six-term first-jet divisor
  identity with value `(a-b)*(b-c)*(c-a)/9`.
- Centered Gamma reciprocity, reciprocal polygamma sums, an anchored
  Hurwitz-zeta-derivative primitive, and all harmonic-number single-shift jets.
- Polylogarithmic twists and an explicit finite compensation that makes Abel
  untwisting commute with every Laurent-jet extraction.

These extend the specified repository results. Worldwide priority, arithmetic
independence, minimality of coordinate algebras, and proof-assistant verification
are not claimed. The general theorem has explicit meromorphic-continuation
hypotheses; it does not cover every conceivable arithmetic Dirichlet series.

## Build

A standard TeX Live installation with pdfLaTeX and the packages named in the
preamble suffices. No source files are fetched from the network.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Or compile `article_singlefile.tex` three times. `make pdf` uses `latexmk`.

## Replay verification

Python 3.10 or newer is recommended. Install the pinned dependencies:

```sh
python -m pip install -r requirements.txt
python verification/verify_exact.py
python verification/verify_numerical.py --full
```

During repository intake, run suites on a scratch copy, not on the delivered files,
as required by `docs/incoming/README.md`; the suites rewrite their result files.
On Windows, `py` or `uv run --no-project` can replace the `python` launcher.

The numerical script without `--full` omits the slower independent Cauchy
alternants. Results are written to `results/`; a rerun intentionally replaces
the corresponding result file. The supplied numerical result used full mode,
60 decimal working digits, and 19 equality tests; the maximum observed absolute
residual was approximately 5.9678564696e-52. A separate four-row untwisting
limit diagnostic is not counted as an equality test.

The exact program passed 191 finite polynomial/rational equality checks.
These finite checks and floating-point diagnostics have different evidentiary
roles. Neither is a replacement for the ordinary analytic proofs. Numerical
errors were not enclosed with interval arithmetic.

## Integration and audit

See `INTEGRATION.md`, `SOURCE_AUDIT.md`, and `provenance.json`.
No remote repository files were changed. The incoming directory was inventoried,
not exhaustively unpacked. The old rejected S8 vector is distinct from the
current surviving S8 conjecture. Neither that conjecture nor S6 is settled here.

`results/build_validation.json` records PDF/build checks.
