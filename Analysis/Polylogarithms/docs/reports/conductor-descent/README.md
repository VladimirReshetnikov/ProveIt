# Conductor Descent and Flat Distribution Ranks

**Stieltjes jets, cyclotomic polylogarithms, and prime-support vanishing**  
Research contribution prepared for Vladimir Reshetnikov's ProveIt programme, 9 October 2026.

Start with `article.pdf`; `article.tex` is its self-contained source, including the bibliography. The article contains complete proofs, explicit formulas, a claim ledger and further research questions. `CORRECTIONS.md` and `integration/` give proposed manuscript changes. No remote repository file was changed.

## Main results

The natural complete finite-level distribution presentation is free of rank phi(q) over a polynomial ring in independent prime weights, over a characteristic-zero character splitting field. Minimal-conductor character sums are an explicit basis. Consequently the complete endpoint-fixed matrix has rank q - phi(q), including singular and zero weight specializations. This proves the manuscript's reported pattern for a precisely defined presentation, for every denominator, rather than assuming that the unavailable historical matrices used exactly these rows.

The result extends to arbitrary spectral jets and to all Stieltjes indices n >= 0 and parameter-derivative orders k >= 1. Finite Mobius formulas provide constructive conductor descent. A separate formula includes the necessary principal pole correction at k = 0.

Character-weighted primitive-root polylogarithm traces descend through explicit exponential-polynomial factors. At order one, the principal trace has exact vanishing order omega(q) - 1. Proved examples include:

- Level 30: the sum of second order derivatives is `-2 log(2) log(3) log(5)`, with the two lower traces zero.
- Level 260, weighted by the nontrivial character modulo four: the sum of second order derivatives is `i pi log(5) log(13)`, with the two lower traces zero.

Here **order derivative** means differentiation of `Li_s(z)` with respect to `s`, evaluated at `s = 1`, not differentiation with respect to `z`.

The S4 formula displayed in the manuscript remains conjectural in this contribution. An exact 96-by-24 law-matrix certificate shows that it is not in the linear span of the specified depth-one-product double-shuffle rows modulo single-value products. This is not a disproof of the formula and not an obstruction to using a larger law vocabulary.

## Replay

Python 3.10 or newer is required; the recorded runs used the versions in the JSON certificates. Install the two explicitly pinned dependencies in a virtual environment:

```sh
python -m venv .venv
. .venv/bin/activate
python -m pip install -r requirements.txt
make exact
make numeric
make pdf
```

`make exact` runs exact rational/symbolic checks; `make numeric` runs ten 45-digit floating-point smoke tests and may take substantially longer. `make pdf` needs a TeX installation with `latexmk`, pdfLaTeX, AMS packages, Latin Modern, mathrsfs, microtype, booktabs, xurl, hyperref and fancyhdr. The PDF is supplied already compiled. No font files are distributed.

Equivalent direct commands:

```sh
python src/verify_exact.py
python src/verify_s4_obstruction.py
python src/verify_trace_coefficients.py
python src/verify_numeric.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Run the verification scripts without Python's `-O` option: assertions enforce the expected identities. Each script overwrites its corresponding JSON report. No network or proprietary computation service is used by the scripts.

## Evidence and limitations

The recorded exact run contains 295 rank cases, 29 all-divisor cases, 18 symbolic jet cases, a polynomial level-twelve normal form, and the S4 annihilating witness. Additional finite series checks verify the next two principal trace coefficients at six levels and the twisted level-260 leading coefficient. All ten numerical smoke tests passed; their largest recorded absolute residual is about 3.59e-43. These are floating-point diagnostics, not rigorous interval enclosures.

The analytic proofs do not depend on the experiments. No numerical independence theorem is claimed. The level-260 example is proved analytically and checked at the finite multiplier level, but a separate 96-term high-precision evaluation is not claimed. No result here has been independently refereed or formalized in Lean.

The distribution rank phenomenon has classical antecedents in Kubert's universal ordinary distribution and related norm-distribution theory. Character transforms, Euler factors and Hurwitz multiplication are credited in the article. The contribution is the explicit proof and constructive, replayable development for this manuscript, not an unsupported claim of worldwide priority.

## Layout

- `article.tex`, `article.pdf`: the research article.
- `src/`: exact generators, verifiers and numerical diagnostics.
- `certificates/`: exact matrices, witnesses, test reports and identity catalogue.
- `integration/`: proposed replacement theorem and editorial ledger entry.
- `CORRECTIONS.md`, `STATUS.md`, `INTEGRATION.md`: audit and integration guidance.
- `SOURCE_SNAPSHOT.json`: pinned source provenance.
- `MANIFEST.sha256`: hashes of the distributed files, excluding the manifest itself.

This package does not include third-party source papers or the original manuscript, and does not automatically commit or upload anything.
