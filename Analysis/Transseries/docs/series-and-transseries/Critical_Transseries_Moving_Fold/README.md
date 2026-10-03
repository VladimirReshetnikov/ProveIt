# Critical Transseries at a Moving Fold

**A uniform two-sheet atlas, large-sector crossover, and resonant action splitting**  
Research continuation for the ProveIt project, 29 September 2026.

## Main result and scope

The article resolves the predecessor manuscript's Research question 11.8 for the
independent-parameter equation

    delta + log(1 + delta/w) + w*z*exp(-delta) = 0.

It proves an exact local two-sheet atlas, locates the moving critical value,
constructs all-order polynomial profiles with an explicit uniform error bound,
and derives a joint critical/large-sector limit. A second theorem treats
convergent analytic folds driven by finitely many exponential actions, including
resonance cancellations and a constructive finite positive support grid.

The original fixed-coupling map has the specialization z = exp(-w)/w, which tends
to -e as w tends to -1. The small-(w+1,z) chart is consequently NOT a claimed
analysis of that fixed-coupling specialization at its core critical point.
The article explains this distinction prominently.

The square-root preparation mechanism and singularity-analysis methods are
classical. The quantitative specialization, all-order profile construction,
specific crossover, and support construction are the contributions developed
here. Independent mathematical and priority review remain appropriate. No new
Lean formalization, peer review, or general resurgence theorem is claimed.

## Files

- `article.tex`: complete editable LaTeX manuscript, with bibliography.
- `article.pdf`: compiled article.
- `verify.py`: exact symbolic checks and 100-decimal-digit numerical diagnostics.
- `data/verification.json`: complete machine-readable results and package versions.
- `data/verification_run.txt`: the output of the full verification run,
  which prints the JSON it writes; the file is byte-identical to
  `data/verification.json`, not a separate console log.
- `data/runtime.txt`: observed elapsed runtime in the preparation environment.
- `data/profile_table.tex`, `data/crossover_table.tex`: generated article tables.
- `requirements.txt`: Python dependencies, pinned to the versions used.
- `Makefile`: convenient verification and PDF build targets.
- `PROVENANCE.md`: inspected sources, repository pin, and audit boundaries.

The delivered checksum ledger `SHA256SUMS` was verified in full on filing
(batch 45) and not kept; the delivered archive remains in the repository
history (see `docs/incoming/README.md`, batch 45 row).

The PDF can be rebuilt without running the Python code because its generated
table fragments are included. No external font files are bundled.

## Reproduce

Use Python 3.10 or later and a TeX Live installation with pdfLaTeX and latexmk.
The verified environment used Python 3.13, SymPy 1.14.0, and mpmath 1.3.0.

```sh
python -m pip install -r requirements.txt
python verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, `make verify` and `make pdf` run the corresponding commands.
The default verification run includes sector indices up to 400. Running
`python verify.py --quick` omits the n=400 diagnostics and writes its shorter
tables into `data/quick/` (since filing; see the amendments below), so it
cannot replace the tables the article inputs; the exact symbolic checks are
unchanged. The default full run is the one used for the supplied PDF and data,
and it rewrites `data/verification.json` and both table fragments in place.

The script requires no network access after dependency installation. Output
paths are relative to the script's own directory, not the caller's working
directory. It replaces only its own JSON and generated table files; it does
not update the ProveIt repository or any Library source.

## What was checked

Exact rational symbolic checks cover the critical equation through degree 8,
the normalized critical value through degree 5, five profile polynomials,
the singular amplitude through degree 4, branch-point reversion, the logarithmic
drift coefficients, and all rational domain majorants. Numerical diagnostics
cover the fold and nearby points, the first three known rational sector
functions, the large-sector crossover, and a resonant discriminant example.

All executed checks passed. These diagnostics do not certify the analytic
existence and all-order assertions: the article provides mathematical proofs
for those. The numerical roots are not interval-arithmetic enclosures.
The PDF was checked for compilation warnings, unresolved references, layout,
and embedded fonts. The supplied build has no overfull or underfull boxes.

## Editorial amendments (ProveIt, 2026-09-29)

These changes were made on filing, after the batch-45 delivery. Every change
to the article text is marked in `article.tex` by a comment beginning
`% ed. (2026-09-29)`; visible additions are headed "Editorial note (ProveIt,
2026-09-29)".

- `article.tex`:
  - an unnumbered `ednote` environment for editorial notes (no numbering
    changes);
  - an editorial note after Theorem `thm:actions` naming its countable-action
    continuation, the later package
    `Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/`, and stating that
    it is a model-specific extension that does not settle the
    higher-multiplicity question;
  - editorial notes at the research questions "Higher critical multiplicity"
    and "Actions depending on the large parameter": both remain open after
    the later sibling packages;
  - an editorial note after Proposition `prop:residual` relating its linear
    regime to the machine-checked Lean theorem
    `Fabius.exists_eq_in_residual_interval`
    (`Analysis/FabiusFunction/Lean/FabiusFunction/MeanValueBracket.lean`);
  - bibliography: the pre-split path of the `Transseries_And_Inversion`
    README (dead at the current revision; the pinned link still resolves at
    its commit) is supplemented by the current path
    `Analysis/Transseries/docs/series-and-transseries/Transseries_And_Inversion/README.md`;
    `QuadraticCoreCatalan.lean` is confirmed at its cited path, unchanged;
    the predecessor manuscript is located at its filed path
    `Support_Controlled_Reversion_One_Exponential/reversion_and_one_exponential.tex`;
  - a sentence in the reproduction appendix describing the changed quick
    mode below;
  - the title page no longer sets a hyperref page anchor, which removes a
    duplicate `page.1` destination warning.
- `article.pdf`: rebuilt from the amended source.
- `PROVENANCE.md`: an editorial note giving the current paths of the
  pre-split README and of the predecessor manuscript.
- `verify.py`: `--quick` writes into `data/quick/` instead of overwriting
  the full-run `data/verification.json` and table fragments; all outputs are
  written with LF line endings (on Windows `write_text` previously emitted
  CRLF). A full rerun on a copy reproduced `data/verification.json` and both
  tables byte for byte.
- `README.md`: `data/verification_run.txt` is described as the byte-identical
  copy of `data/verification.json` that it is; the retired checksum ledger is
  no longer listed; this section.
