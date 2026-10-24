# Centered-budget Diophantine reductions: portable research release

Start with `report/report.pdf` or its complete LaTeX source `report/report.tex`.
The literal polynomial DAGs, fixed coefficient payloads and recipes, ordinary
proofs, independent reviews, and source-authentication records are included.

## Offline verification

Use Python 3.10 or later and SymPy 1.14.0 (the tested version). The environment
must already provide SymPy; verification never installs packages or uses the
network. Author component checks use the standard library. The independent
reviewers and independent resultant check use SymPy.

From any directory:

    python /path/to/release/verify.py --output /path/outside/release/verification.json

The master runs every advertised new component in ordinary and optimized
Python, including its independent review. It rebuilds the declared literal
artifacts and compares exact bytes, authenticates unchanged source archives,
replays both explicitly claimed predecessor families, and tests integrity
corruptions. All work occurs in isolated temporary copies. Delivered files
remain unchanged. `--jobs 1` reduces peak memory; the default is 3 independent
groups. `--manifest-only` checks the sealed delivery without replay.

`REPLAY_PLAN.json` is the complete executable command and deterministic-output
ledger. Inherited parity's whole release driver deliberately rejects `-O`;
the master checks that expected rejection, then runs all seven designated
parity algebraic auditors with `-O`. It does not mislabel that rejection as a
successful optimized whole-release verification.

## Contents and logical boundaries

- `guard/`: twelve unrestricted-integer variables, exact degrees 1000 and 1024.
- `eleven/`: eleven unrestricted-integer variables, centered and uncentered
  variants with exact degree and arithmetic-cost certificates.
- `finalizers/`: fifteen unrestricted-integer variables, bounded-guard
  absorption, degree 176, 125 live binary arithmetic operations.
- `positive/ten_centered/`: ten strictly positive integer variables, degree 912,
  126 live binary arithmetic operations; a translated nonnegative form is also
  retained and rebuilt.
- `alternative/`: polynomial arithmetic interfaces with explicit uncompiled
  power/binomial graph contracts. These are not ordinary-polynomial records.
- `review/`: independent proof-review records and independently implemented
  finite algebra, metric, degree, and corruption checks.
- `baseline/`: pinned comparison evidence and scoped predecessor replay.
- `provenance/`: copied predecessor interfaces used by the alternative route.

Operation counts mean live binary addition, subtraction, and multiplication;
fixed numeral leaves and register reuse are free. Variable domains are not
interchanged. Finite replay does not prove the unbounded native/compiler/Pell
or refutation-calibration theorems. Ordinary proofs and inherited mathematical
interfaces are identified separately. No new Lean/Rocq or internal-ZFC
certificate, global minimality claim, or proof of ZFC consistency is supplied.

See `DEPENDENCIES.md` for the deliberately bounded source closure. Existing
licenses, notices, source URLs, mathematical pin claims, and original source
manifests are preserved. The root `SHA256SUMS.json` seals the delivered tree.

## Rebuilding the report

With a normal LaTeX installation providing the packages used in the source:

    cd report
    pdflatex -interaction=nonstopmode -halt-on-error report.tex
    pdflatex -interaction=nonstopmode -halt-on-error report.tex

Make a working copy first: compilation creates auxiliary files and the sealed
release is intentionally immutable. PDF metadata and timed verification
receipts are not deterministic mathematical artifacts; polynomial/DAG bytes
and the listed exact certificates are.

## Rebuilding the delivery ZIP

    python make_archive.py --output /path/outside/release/ZFC_Diophantine_Budget_Interpolation_2026-10-24.zip

Entries have a fixed timestamp, path order, permissions, and compression level.
Identical delivered files and the same zlib implementation produce identical
archive bytes. The command checks the seal first and verifies ZIP CRCs after
writing.
