# Compiled orbit transfers and selective normal-disc witnesses

A proof-backed local continuation of ProveIt's unknot-recognition work.

**Main article:** `article/report.pdf` (editable source: `article/report.tex`).

**Pinned upstream revision:** `b365341b1939c69a26b31bb5d05a097d4572692c`.
The exact inspected modules and their Git blob identifiers appear in
`PROVENANCE.json`. No repository commit or production-dispatch change was made.

## Result

Compile a complete, source-bound AHT interval-orbit trace into a value-independent
nonnegative integer linear DAG. Use a few scalar weights to select an emission;
transpose once to recover one component's counts in the source intervals. Prefix
sums then recover interval-owned coordinates without transporting a full dense
coordinate payload. For normal surfaces this changes the extraction interface
from a full `7t`-coordinate census to three decision weights plus one transpose.

The article proves correctness, a polynomial circuit-size bound, small coefficient
bit lengths, the normal-disc application, and a dense-profile family with a
quadratic full-output cost versus `O(D log(D+2))` selective arithmetic.

This is not a general quasi-polynomial recognition proof. A supplied normal vector,
a validated geometric source, and global search/hierarchy bounds are different
obligations. A negative result for one vector is not a knottedness certificate.

## Execution status

- **Executed:** 24 passing test methods; a separate 10,000-system literal-graph
  audit (5,000 traces under each merger convention); huge binary-integer tests;
  matched local-query benchmarks with dense, sparse, and A/A controls.
- **Not executed:** the proposed native `fastunknot` adapter, the maintained
  repository suite, a Regina corpus, native positive disc certificates, or
  end-to-end knot-recognition timings.

The integration adapter has been source-reviewed against the pinned interfaces
and checked for Python syntax. It must pass `integration/audit_native.py` and the
maintained suite before promotion. Standalone graph tests are not native geometry
validation.

## Reproduce

Python 3.10 or newer; the completed runs used Python 3.13.5. No third-party Python
dependencies are required for the standalone package.

```sh
PYTHONPATH=src python -m unittest discover -s tests -v
python experiments/audit.py
python experiments/benchmark.py --rounds 7
python experiments/make_tables.py
cd article && sh build.sh
```

The PDF build uses `pdflatex` and standard packages (amsmath, amsthm, TikZ,
booktabs, listings, geometry, microtype, hyperref). A checked-in bibliography makes
BibTeX unnecessary; `references.bib` is supplied for integration elsewhere.

`python experiments/check_delivery.py` verifies the shipped SHA-256 manifest and
that the recorded experiment source hashes match the delivered kernel. Running
experiments again overwrites their result files, so check the original manifest
before rerunning or keep an untouched archive copy.

## Reading order

The article's Sections 3–5 give the compiler and extraction proofs. Sections 6–7
state the normal-disc and independent terminal contracts. Section 8 proves the
explicit asymptotic separation; Section 9 gives the audit and all measurements.
Section 10 isolates the conditional global complexity target, and Section 11
contains seven concrete research directions.

## Performance interpretation

On the supplied dense-profile family at `D=1024`, the recorded medians were
529.922 ms (dense eager), 142.426 ms (sparse eager), and 41.131 ms (selective).
The median paired sparse/selective ratio was 3.471.

Cold selective compilation loses to sparse eager transport on most other
fixtures. These are generic interval-query experiments with the same supplied
trace. Trace discovery, native geometry, and final disc-certificate verification
are excluded in **all** arms. The results are not whole-knot speedups and do not
justify a blanket default switch. Full raw observations are retained, including
regressions and the identical-code timing control.

## Integration

See `integration/REVIEW.md`. Suggested use is an opt-in research path beside the
maintained package. The bridge first preserves the cheap three-weight negative
path, then compiles only when a disc exists, and independently checks a newly
extracted disc vector. It deliberately keeps the existing full-coordinate census
available as a baseline.

The positive terminal certificate proves an admissible disc `y <= x` in the
validated manifold. It does **not** independently prove component membership in
`x`, and does not supply knot-diagram provenance. These are explicit semantic
boundaries, not optional checking shortcuts.

## Package contents

`src/orbit_transfer/` contains the tested kernel, checked-trace adaptation, and
research-only controls. `tests/` and `experiments/` contain deterministic drivers.
`results/` retains raw CSV/JSON, source-bound logs, and document checks.
`integration/` contains the pending native bridge and audit runner. `article/`
contains all TeX sources, the PDF, and build script.

New code and documentation use MIT-0, matching the inspected upstream license.
The checker and reference scheduler are attributed adaptations, not byte-identical
native snapshots. No third-party paper PDFs or font files are redistributed.
