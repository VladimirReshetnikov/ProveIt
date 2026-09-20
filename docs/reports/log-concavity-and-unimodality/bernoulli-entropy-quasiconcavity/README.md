# Two-coin counterexamples to the proposed generalized Shepp–Olkin thresholds

**Main deliverable:** `article.pdf` (17 pages) and its complete source `article.tex`.
Prepared on 20 September 2026 for Vladimir Reshetnikov.

## Mathematical result

For every finite real q > 1, both Renyi-q and Tsallis-q entropy of a sum of
independent Bernoulli variables fail even quasiconcavity as functions of the
Bernoulli parameters. Two coins with strictly interior rational parameters suffice.
The main construction is mean-preserving and uses opposite parameter slopes.

This refutes the proposed numerical thresholds 2 and 3.65986... adjoining
Conjecture 4.2 in Hillion–Johnson, arXiv:1503.01570v1. It does **not** prove
universal joint concavity throughout 0 < q < 1. The existence of an initial
interval of admissible orders below one is not settled in this package.

A compact exact witness at q=2 is:
- Endpoints: (3/20, 1/20), (1/20, 3/20).
- Midpoint: (1/10, 1/10).
- Endpoint collision probability: 54907/80000.
- Midpoint collision probability: 55088/80000.
- Tsallis midpoint deficit: 181/80000.
- Renyi midpoint deficit: log(55088/54907).

The article also proves a sharp curvature boundary, the full fixed-mean
two-coin maximizer classification, fixed-mean concavity for 0<q<=1, minimum
counterexample dimensions, and interior extensions to every n>=2.

## Review and priority

Self-contained analytic proofs are supplied. No independent referee review,
proof-assistant verification, or confirmation of bibliographic priority is claimed.
The source search located the published proposal and no earlier resolution;
that bounded search is not a guarantee that the result has never appeared.
See `STATUS.md` and `notes/sources.md` for precise scope.

## Read or rebuild

The existing PDF can be read directly. A standard LaTeX distribution with
pdfLaTeX can rebuild it using the included tables and vector figures:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

No Python libraries are needed for that rebuild. The exact arithmetic checks
use Python 3.10 or later and **only its standard library**:

```sh
python code/verify_exact.py
```

Recorded result: **PASS, 12,512 exact checks**. This includes finite exact
instances and identities, not a formal verification of the entire article.

Optional symbolic checks and plot regeneration use the dependencies pinned in
`requirements-optional.txt`:

```sh
python -m pip install -r requirements-optional.txt
python code/verify_symbolic.py
python code/make_figures.py
```

Run from any directory for the Python scripts; run LaTeX from this directory.
A Makefile provides `make pdf`, `make check`, `make symbolic`, and `make figures`.
No tool requires a network connection after dependencies have been installed.

## Contents

- `article.tex`, `article.pdf`: complete article and compiled version.
- `code/verify_exact.py`: exact arithmetic verifier, independently enumerated PMFs.
- `code/verify_symbolic.py`: symbolic differentiation and identity checks.
- `code/make_figures.py`: reproducible numerical table and two vector figures.
- `code/exploratory_hessian_probe.py`: original exploratory floating-point search;
  retained for provenance, not used to certify the theorems.
- `code/select_area.py`: original one-draw random-area selection script.
- `results/`: exact certificates, symbolic output, numerical CSV/table, exploratory
  log, environment record, and PDF quality-control record.
- `figures/`: the two prebuilt vector PDF plots included in the article.
- `notes/selection.json`: original selection record and complete list of 96 areas.
- `notes/manifest_exclusion.md`: audit of all 71 excluded manifest entries.
- `notes/sources.md`: primary-source and novelty-search audit.

## Random selection

The area list was fixed before a single OS-backed call to `secrets.randbelow(96)`.
It returned index 57 (one-based 58), **Discrete probability**. There was no redraw.
`notes/selection.json` is the preserved historical result. Re-running
`code/select_area.py` makes a fresh random draw and writes `code/selection.json`;
it cannot reproduce the original operating-system randomness. That script is
not part of the verification or article build.

## License

The newly generated article, code and data are made available under CC0 1.0.
No third-party paper, font file, or external software package is redistributed.
Bibliographic material and the manifest titles identify their respective sources.
