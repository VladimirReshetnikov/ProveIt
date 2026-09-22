# Computable surreal numbers — merged and reconciled report

This package contains one integrated mathematical report, not a concatenation
of the three input PDFs. It preserves their distinct representations, supplies
an explicit reconciliation ledger, retains complementary proofs, and separates
mathematical existence from uniform algorithms.

## Files

- `article.pdf`: the 51-page unified report, with linked contents and bibliography.
- `article.tex`: complete editable LaTeX source; no external bibliography or graphics.
- `MERGE_NOTES.md`: a short account of the principal reconciliation decisions.
- `code/run_all.py`: runs all four verification suites and writes their logs.
- `code/original_A-verify.py`, `original_B-verify.py`, `original_C-verify_examples.py`:
  the unchanged original verification programs.
- `code/verify_reconciliation.py`: additional independent finite cross-model checks.
- `data/`: rerun logs, individual JSON results where available, and a summary.
- `data/provenance-manifest.json`: exact input archive identities, file hashes and
  line counts.
- `REVIEW_SCOPE.md`: the literature/repository checks and their limitations.

The three original manuscripts are **not** redistributed with this report. The
reconciliation ledger in the article cites them by their original TeX line
numbers and the manifest records their hashes, so every disposition is traceable
and checkable against a copy obtained elsewhere; the texts are simply not
included here.

## Input identities

| ID | Uploaded archive | Main numerical representation |
|---|---|---|
| A | `computable_surreal_numbers.zip` | Effective rational left-finite series with finite candidate covers |
| B | `computable_surreal_numbers(1).zip` | Computable bounded-denominator Puiseux series |
| C | `computable_surreal_numbers(2).zip` | Computable bounded-denominator Puiseux series |

Suffixes identify the supplied uploads. They are not assumed to identify a
chronological version history.

## Rebuild the PDF

With a standard LaTeX installation containing the packages named in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
three times so that contents and cross-references settle. The bibliography is
embedded; BibTeX/Biber is not required. The source uses Latin Modern and standard
mathematical fonts supplied by the TeX installation. No font files are distributed.

## Reproduce the finite checks

Requires **Python 3.10 or newer**, standard library only. From the package root:

```sh
python code/run_all.py
```

`python3 code/run_all.py` works where Python is named `python3`; on Windows,
`py code/run_all.py` is another option. The runner uses the same interpreter for
all subprocesses, records logs under `data/`, and exits nonzero if a suite fails.
No network access is used. Original source programs have not been modified.

Observed September 22, 2026 rerun results (the runtime and UTC timestamp are
recorded in `data/summary.json`):

| Suite | Unit reported | Result |
|---|---:|---|
| A | 4,967 exact comparisons | PASS |
| B | 18 named unit tests | PASS |
| C | 266 exact checks | PASS |
| Reconciliation | 4,366 exact cross-model checks | PASS |

These units have different meanings and are deliberately not added together.
The new suite compares dense common-grid Puiseux convolution with sparse rational
convolution, checks candidate covers with extra zeros and nonnested lists, tests
the finite-jet root transformation, checks derivative/primitive identities, and
checks finite instances of the two unbounded-denominator support examples.
The geometric-cover regression supplies valid raw names with negative zero
candidates, including a zero input. It checks both support completeness and the
output cover's `[0,B)` range; exact geometric identities alone would miss this
representation error.

## September 22 corrections

The geometric-series algorithm now explicitly intersects its candidate cover
with `[0,B)`. The topology statement distinguishes set-indexed nets in the full
surreal class from lower-universe-small indices for a universe-relative carrier.
The supplied runner and build commands use the actual shipped filenames;
`make -f code/Makefile test` and `make -C code test` both locate the package root.
The three original verification programs are unchanged.

## Mathematical and verification scope

The report presents detailed mathematical proofs and identifies the classical
results used as inputs. A finite test does **not** prove an infinite theorem,
real closedness, a computability classification, or an undecidability reduction.
Synthetic halting fixtures in the original programs do not compute the halting set.
The package does not implement arbitrary computable reals or arbitrary infinite
surreal arithmetic, and it does not include a new Lean-checked formalization.
The manuscript has not been independently refereed; no literature-wide priority
claim is made for the synthesis.

The GitHub source review is pinned to
`4896a2808ce30e01b1c86ae3ba2295a64762d246`. That historical source review made
no repository changes and ran no local Lean build. The September 22 exposition
corrections and finite-test rerun above are separate from that source review.
The report distinguishes existing mathematical infrastructure from the
effective-name algorithms proposed here.
