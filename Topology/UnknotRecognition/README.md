# Knots: quasi-polynomial unknot recognition, six attempts and a synthesis

This repository collects six independently produced attempts to implement the
`n^O(log n)` unknot recognition algorithm announced in Marc Lackenby's
February 2021 talk, a synthesized review of them with cross-validation, and a
seventh, faster exact recognizer written on top of their ideas.

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
| `fast/` | `fastunknot`: Alexander-polynomial filter plus a scanning (Bar-Natan) Khovanov backend; tests, examples, benchmark |

## Quick start

Everything is standard-library Python (3.10+; tested on 3.14).

```sh
# run one of the archives' test suites
cd reports/04 && python -m unittest discover -s tests -v

# run the new recognizer
cd fast && python -m fastunknot recognize examples/conway.json

# rebuild the synthesized report (needs pdflatex)
cd synthesis && sh build.sh
```

## Test status (last observed 18 September 2026, commit 72b15eb)

All unit-test suites are green on CPython 3.14.4 / Windows 11:

| Suite | Tests | Result | Wall time |
|---|---|---|---|
| `reports/01` | 40 | OK | ~4 s |
| `reports/02` | 64 | OK | ~2 s |
| `reports/03` | 49 | OK | ~4 s |
| `reports/04` | 62 | OK | ~3 s |
| `reports/05` | 58 | OK | ~1 s |
| `reports/06` | 45 | OK | ~4 s |
| `fast` | 19 | OK | ~2 s |

The experiments (cross-validation scripts, benchmark) have a more nuanced
status; see `synthesis/README.md` and `fast/README.md` before rerunning any
of them. In short: everything reported in `synthesis/report.pdf` comes from
completed runs, but two experiments are long-running (hours) and one
benchmark input hits a 600 s cap.

## Status of the quasi-polynomial target

Open. Section 5 of the synthesized report lists what a proof-carrying
implementation would still need: an encoded layered handle structure with
bit-size bounds, bounded hierarchical multi-surfaces, compressed cutting with
provenance, constructive Cheeger-region and weak-reduction routines, the
logarithmic depth bound, and the end-to-end cost accounting.
