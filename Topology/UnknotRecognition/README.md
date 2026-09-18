# Knots: quasi-polynomial unknot recognition, six attempts and a synthesis

This repository collects six independently produced attempts to implement the
`n^O(log n)` unknot recognition algorithm announced in Marc Lackenby's
February 2021 talk, a synthesized review of them with cross-validation, and a
seventh, faster exact recognizer written on top of their ideas, nine
proposals for accelerating it, the integrated result, and a Rust port.

**Bottom line.** No archive, and not the new package either, implements a
recognizer with a proved quasi-polynomial bound. The accelerated hierarchy
operations on the last slide of the talk have no published algorithmic
specification with cost bounds (Lackenby's July 2026 preprint, Section 9,
says its steps "are not described with enough precision to be able to
estimate their running time"; the preprint is in `docs/arXiv-2607.23350v1/`). What exists is exact, exponential, mutually
consistent, and well tested. Details and the list of remaining obstacles are
in `synthesis/report.pdf`.

## Layout

| Path | Contents |
|---|---|
| `docs/` | the source material: the 109-page talk `quasipolynomial-talk.pdf`, and the arXiv source and PDF of Lackenby's July 2026 preprint *Incompressible surfaces, hierarchies and unknot recognition* (arXiv:2607.23350v1) in `docs/arXiv-2607.23350v1/` |
| `reports/` | the six original archives (`*.zip`) and their extracted contents in `01/` .. `06/` |
| `synthesis/` | the synthesized report (`report.tex`, `report.pdf`), the cross-validation scripts and data, and the table generator |
| `fast/` | `fastunknot` 0.2 (Python): polynomial and width-bounded filters plus a scanning (Bar-Natan) Khovanov backend; tests, examples, ablation |
| `proposals/` | nine independently produced proposals for accelerating `fastunknot` 0.1, extracted into `01/` .. `09/`, with a comparison of their ideas |
| `rust/` | a Rust implementation of the 0.2 pipeline, with tests, a Python cross-check and a profile; since September 2026 also the Reidemeister III search and a race of scan orders on threads (`--race N`) |

## Quick start

Everything is standard-library Python (3.10+; tested on 3.14).

```sh
# run one of the archives' test suites
cd reports/04 && python -m unittest discover -s tests -v

# run the new recognizer
cd fast && python -m fastunknot recognize examples/conway.json

# the Rust version (needs cargo)
cd rust && cargo build --release && target/release/fastunknot recognize ../fast/examples/conway.json

# rebuild the synthesized report (needs pdflatex)
cd synthesis && sh build.sh
```

## Packaging the repository as a ZIP

```sh
python make_archive.py            # writes Knots.zip at the root
python make_archive.py --all-pdf  # same, but keeps every PDF
```

The script zips every git-tracked file (itself included) at maximum
compression and leaves out `.git`, untracked files, and dot files at the root.

**By default it also leaves out the PDFs that can be rebuilt**, namely every
`foo.pdf` that has a `foo.tex` next to it. If you unpack the archive and a
PDF is missing, open the `.tex` file of the same name in the same directory,
or rebuild it with `pdflatex` (twice):

| Missing PDF | Source in the archive | Rebuild |
|---|---|---|
| `synthesis/report.pdf` | `synthesis/report.tex` | `cd synthesis && sh build.sh` |
| `reports/01/docs/report.pdf` | `reports/01/docs/report.tex` | `pdflatex report.tex` (twice) |
| `reports/02/docs/implementation_report.pdf` | `reports/02/docs/implementation_report.tex` | likewise |
| `reports/03/docs/implementation_report.pdf` | `reports/03/docs/implementation_report.tex` | likewise |
| `reports/04/docs/report.pdf` | `reports/04/docs/report.tex` | likewise |
| `reports/05/docs/report.pdf` | `reports/05/docs/report.tex` | likewise |
| `reports/06/docs/technical-report.pdf` | `reports/06/docs/technical-report.tex` | likewise |
| `docs/arXiv-2607.23350v1/algorithm-incompressible-250726.pdf` | `docs/arXiv-2607.23350v1/algorithm-incompressible-250726.tex` (with its `.bbl` and figure PDFs) | `pdflatex algorithm-incompressible-250726.tex` (twice) |

The report PDFs inside `proposals/01` .. `09` are omitted by the same rule
(each has its `.tex` beside it).

PDFs without a same-name source are always included: the talk
`docs/quasipolynomial-talk.pdf` and the preprint's figure PDFs in
`docs/arXiv-2607.23350v1/`.

## Test status (last observed 18 September 2026)

All unit-test suites are green on CPython 3.14.4 and rustc 1.96.1 / Windows 11:

| Suite | Tests | Result | Wall time |
|---|---|---|---|
| `reports/01` | 40 | OK | ~4 s |
| `reports/02` | 64 | OK | ~2 s |
| `reports/03` | 49 | OK | ~4 s |
| `reports/04` | 62 | OK | ~3 s |
| `reports/05` | 58 | OK | ~1 s |
| `reports/06` | 45 | OK | ~4 s |
| `fast` (0.2 plus the later scanner and pipeline work) | 40 | OK | ~12 s |
| `rust` (`cargo test --release`) | 4 | OK | ~25 s including the build |
| `rust/cross_check.py 200` (Rust against Python) | 200 closures | 0 problems | ~1 min |

The six archive suites were last run at commit 72b15eb and have not changed
since. The test suites shipped inside `proposals/01` .. `09` were not run.

The experiments (cross-validation, benchmarks, ablation, profile) have a more
nuanced status; see `synthesis/README.md`, `fast/README.md` and
`rust/README.md` before rerunning any of them. Everything reported in
`synthesis/report.pdf` comes from completed runs; several experiments are
long-running because old configurations run into their time caps on purpose.

## Status of the quasi-polynomial target

Open. Section 5 of the synthesized report lists what a proof-carrying
implementation would still need: an encoded layered handle structure with
bit-size bounds, bounded hierarchical multi-surfaces, compressed cutting with
provenance, constructive Cheeger-region and weak-reduction routines, the
logarithmic depth bound, and the end-to-end cost accounting.
