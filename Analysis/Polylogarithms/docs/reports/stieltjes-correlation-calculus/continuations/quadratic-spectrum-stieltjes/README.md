# Quadratic-Spectrum Stieltjes Identities

Prepared for Vladimir Reshetnikov's ProveIt programme, 10 October 2026.
Repository source pin: `446dca9bd65c20e409d1d2561d4ffad408103e2a`.

## Start here

`article.pdf` is the 24-page research article. `article.tex` and `sections/`
are the modular LaTeX sources; `article_singlefile.tex` is an equivalent
standalone source. The proofs are in the article. The code contains finite
algebra regressions and numerical diagnostics, not a proof-assistant
formalization or interval certificate.

The main results are both reflected Stieltjes channels at every index,
polylogarithmic order integrals, a globally convergent finite-head harmonic
formula, an exact polynomial parity criterion for conjugate factorization,
finite complex-Hurwitz/polylogarithm identities at every negative integer,
mass primitives and a shift/mass differential equation, and a finite
first-derivative reduction for several quadratic factors.

## Build

A normal TeX Live installation with `latexmk` suffices:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex article_singlefile.tex` twice. No external
figures, font files, network services, bibliography database, or shell escape
are needed. The sources require standard packages including `amsmath`,
`amsthm`, `mathtools`, `lmodern`, `microtype`, `geometry`, `fancyhdr`, `xurl`,
and `hyperref`.

## Reproduce the checks

Python 3.10 or newer is recommended. The recorded run used mpmath 1.3.0 and
SymPy 1.14.0, pinned in `requirements.txt`.

```sh
python -m venv .venv
# Activate the environment using the command appropriate for your shell.
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py --dps 45
```

Neither script writes files unless `--output PATH` is supplied. For replay
without modifying the delivered records, use a copied working directory or
new output paths:

```sh
python code/verify_exact.py --output build/exact_replay.json
python code/verify_numeric.py --dps 45 --output build/numeric_replay.json
```

The delivered records are in `data/`. All 517 exact assertions and 82
numerical comparisons passed. The largest scaled residual in the 45-digit
numerical run was approximately `4.61771634572e-44`, with an acceptance
threshold of `1e-33`. These residuals are diagnostic, not validated error
bounds. Cutoffs are precision-dependent numerical choices. Increasing
precision is not a substitute for interval tail certification.

## Contents

- `article.pdf`, modular and standalone LaTeX sources: full statements,
  ordinary proofs, exact examples, source audit, and eight further questions.
- `code/quadratic_spectrum.py`: reusable arbitrary-precision implementations.
- `code/verify_exact.py`: exact finite coefficient checks.
- `code/verify_numeric.py`: independent analytic-representation comparisons.
- `data/exact_results.json`, `data/numeric_results.json`: actual executed records.
- `data/claim_ledger.json`: theorem-by-theorem scope and evidence.
- `provenance.json`, `SOURCE_AUDIT.md`: source pin and inspected/uninspected scope.
- `integration/manuscript_fragment.tex`: additive insertion draft.
- `integration/bibliography_entry.tex`: bibliography entry for that draft.
- `integration/editorial_update.md`: proposed correction of stale J(p/q) status.

## Integration and status

Suggested destination:
`Analysis/Polylogarithms/docs/reports/quadratic-spectrum-stieltjes/`.
The fragment is an insertion draft, not an automatic patch; its labels use
`qspec:frag:`. The complete proofs remain in the article. No remote repository
or persistent Library files were modified.

Classical Poisson, Bessel, Gamma, Hurwitz, and multiplicative-anomaly inputs
are attributed in the article. No exhaustive priority claim is made.
The existing S6 identity remains unresolved by this contribution. One frozen
S8 vector is already rejected in the inspected manuscript; this delivery
does not assert that every S8 reduction is false. The incoming ZIP catalogue
was inspected, but the six archive interiors were not read. The proposed
J(p/q) update points to an already existing formal classification; it is not
a new theorem of this contribution.
