# Exact Quotient Kernels for Unknot Recognition

Research continuation dated 8 October 2026, against ProveIt commit
`58ee11a97d5fd7f21647c57eefaf3ecc007931d6`.

The report develops three exact local improvements and their integration:
sharp Fine–Wilf mergers in native interval orbit counting, coefficient-span
and forest reductions of scalar commutants, and a shared cyclic-overlap
index with bounded adaptive search. It also implements native topology
queries for binary normal coordinates and repairs an inherited subprocess
input deadlock. **It does not establish a general quasi-polynomial unknot
recognizer.** The article identifies the remaining representation, search,
cutting and total-work obligations explicitly.

## Read and build

`article.pdf` is the complete report. Its main TeX source is `article.tex`,
which includes `overlap.tex`, `experiments.tex`, `integration_and_research.tex`,
`research_agenda.tex`, `validation_summary.tex` and `references.tex`.
Generated tables are under `tables/`; vector figures and their PNG previews
are under `figures/`.

The supplied tables and figure PDFs make the document build independent of
running any experiment:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

A standard TeX Live installation with pdfLaTeX, latexmk, Latin Modern, AMS
packages, microtype, hyperref, listings and the ordinary table packages is
sufficient. The measured Python environment is recorded in
`research_environment.json`; `requirements-research.txt` lists optional
research dependencies. The new orbit and normal-topology production modules
do not depend on Regina or Matplotlib.

## Reproduce experiments

Apply the complete overlay to the pinned repository. It is an incremental
research package, not a standalone replacement for the inherited `fast/`
tree. From `Topology/UnknotRecognition/fast`:

```bash
python3 -B interval_research/benchmark.py --output interval_research/results.json
python3 -B normal_orbit_research/benchmark.py --output normal_orbit_research/results.json
python3 -B benchmark_coefficient_span.py --output coefficient_research/results.json
python3 -B cyclic_overlap_research/benchmark.py --output cyclic_overlap_research/results.json
python3 -B cyclic_overlap_research/make_summary.py
```

Use other output filenames to preserve the supplied raw samples. The cyclic
benchmark reads the pinned Git object to record the historical implementation's
digest. It therefore requires a repository that contains that commit.

From this article directory:

```bash
python3 -B render_results.py
python3 -B audit_sources.py
```

The former rebuilds tables and figures from the archived JSON; the latter
checks recorded source digests, portable paths and required dependencies.
The final source audit matches all 26 recorded digests. Its notes distinguish
before/after source freezes from the normal experiment's end-of-run hashes,
and explicit arm-order arrays from order reconstructed using the recorded
seed. It does not rerun benchmarks or tests.

## Validation

From `fast/`, with the pinned sibling reference directories present:

```bash
PYTHONPATH=. python3 -B -m unittest discover -s tests -v
```

The required inherited references are `reports/24/reference`,
`reports/26/detshadow` and `reports/28/src/closure_reset`. In a sparse checkout,
add these paths before running the full suite. Optional Regina 7.4 was
available for the independent checks reported here.

The faithful baseline ran 768 methods: 767 passed and the delayed-input
subprocess regression failed. The final maintained implementation passed
all **807 methods**, with no skips, errors or failures. The `validation/`
directory contains both full logs, source hashes, the unchanged baseline
archive manifest, and the diagnosis of the inherited subprocess failure.
Earlier incomplete staging runs are superseded by these full runs.

## Interpretation of results

The whole Gordian query improves with adaptive search while preserving its
complete certificate. Shared-index-only search regresses there and is
retained as a negative control. Constructed coefficient families show large
equation and timing reductions; the measured raw knot scans do not show a
consistent overall benefit, so `direct` remains their default. The normal
kernel computes topology of a supplied triangulation and vector; it does
not search for the vector or certify correspondence to the input knot.

See `PROVENANCE.md` for inherited source attribution and the distinction
between classical ingredients, new code, measured findings and proposed
research. The article includes twelve concrete research questions and
conditions under which a complete quasi-polynomial bound would follow.
