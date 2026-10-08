# Certified disk-frontier reduction for exact unknot recognition

A research continuation for `ProveIt/Topology/UnknotRecognition`, dated 7 October 2026.
The paper is **`article/certified_disk_frontiers.pdf`** (with complete LaTeX source).

## What is added

A common-disk hypothesis is now checked from the actual processed diagram's rotation
system. The certificate uses boundary walks of a ribbon neighborhood; it does not
enumerate smoothing states. A polynomial ear-insertion construction supplies certified
orders for biconnected plane crossing graphs. Existing good orders should be checked
before choosing a different, potentially wider order.

On certified stages, a finite homological-perturbation kernel computes a minimal
complex **including nonzero maps between adjacent surviving degrees**. The guarded
adapter fits the newly inspected `FastScan.eliminate(update_budget=...)` API and keeps
completed sparse progress. Incompatible disk geometry declines the new path; it is
never interpreted as a knot verdict.

An explicit descending-grid generator supplies unknot diagrams with `n=m^2` crossings
and frontier at least `m/3` in **every** crossing order. This rules out a universally
polylogarithmic raw-width proof strategy even on unknots. It is not a running-time
lower bound for recognition, simplification, or certificate-based rejection/acceptance.

## Relationship to the existing work

The current maintained `synthesis/radical.tex` already discusses scalar survivor
prediction, degree-gap shortcuts, canonical multiplicities, sharp radical nilpotence,
and finite transfer. This article credits that work. Its main continuation is the
**constructive geometry bridge**, the guarded full-transfer implementation, and the
explicit width obstruction and validation artifacts. It does not claim a new general
perturbation lemma or a first-in-the-literature algebraic minimality theorem.

There is **no proved general quasi-polynomial recognizer in this package**. The paper
proves a bound `poly(n,1+R) * 2^O(B)` for a certified explicit scan, where `B` is the full
boundary half-width and `R` the maximum explicit minimal object count. No universal
small-parameter extraction theorem is supplied. Pivot order alone cannot lower those
minimal multiplicities. Existing sharing and saturation methods can bypass some
explicit-object obstructions and are not replaced here.

## Run the checked artifacts

Python 3.10+ and its standard library are sufficient; the recorded run used CPython
3.13.5. Run these commands from the unpacked root (the scripts set local import paths).

```sh
python -m unittest discover -s tests -v
python experiments/geometry_validation.py
python experiments/verify_certificates.py
python experiments/grid_family.py
python experiments/benchmark.py --repeats 7
python experiments/make_tables.py
```

A validated demonstration recognizer is available, without the production prefilters:

```sh
python experiments/run_diagram.py --strands 2 --word=1
python experiments/run_diagram.py --strands 3 --word=1,-2,1,-2 --mode adaptive
python experiments/run_diagram.py --strands 2 --word=1,-1 --homology
```

The first two examples return `UNKNOT` and `KNOTTED`. The third returns link homology
without a knot verdict. `--json` accepts `{"pd": [[...], ...]}` or an object with
`strands` and `word`. Empty PDs, nonplanar rotation systems, and non-knot inputs at the
recognition entry point are rejected rather than guessed. A resource limit returns
`UNKNOWN_RESOURCE_LIMIT` and a nonzero exit code, never a knot verdict.

To rebuild the article (requires `pdflatex` and ordinary LaTeX packages):

```sh
cd article
sh build.sh
```

The modular article inputs are generated from the recorded final results. The release
also provides a single-file LaTeX export. Re-running timings changes the generated
tables only after `experiments/make_tables.py` is run; this is intentional.

## What the recorded evidence establishes

See `results/verification_summary.json` for the exact machine-readable counts. The
final suite has **52 passing test methods**, including 100 seeded independent-cube
braid comparisons and 320 intermediate profile comparisons. Separate geometric
validation accepts 71 of 80 candidates, checks **14,658 complete smoothing states**,
and performs another 71 cube comparisons. Seven full typed chain-homotopy certificates
are exported and replay-verified. Grid geometry and descending traversals are checked
through 64 crossings; independent cube ranks for that family are computed only through
9 crossings.

The final paired timings show up to **5.87x** improvement on dense synthetic two-term
blocks with nonzero survivor maps. Sparse diagonal blocks regress by **8.79x**. All
synthetic cases additionally agree under independent binary regular-representation
homology checks. These matrices are not asserted to be actual knot-prefix complexes.

The seven complete fixed-order diagram scanner benchmarks do **not** establish a
recognition speedup. Eager block reduction is slower on every case. The adaptive
control completes ordinary cancellation before its budget expires on every case,
so it makes **zero full block calls**. Its timing differences are not evidence for
a benefit from the new kernel. Raw trials, all controls, environment data, and the
exact generated inputs are in `results/benchmarks.json` and `benchmarks.csv`.

## Integration boundary

Keep the current production default unchanged. Consult `integration/INTEGRATION.md`.
The intended seam is after the existing adaptive pause and after any successful
cheap residue/degree-gap shortcut. Only attempt full transfer after a geometric
certificate has been checked. Decline must resume the same partially reduced complex.
The demonstration's own allowance policy is an experimental control, not a proved
competitive scheduler.

`reference_upstream/` is an attributed **source-derived fixture**, not a full checkout
and not a byte-identical copy. The original production suite, CLI pipeline, Rust port,
and races were not run here. Source-equivalence checking against the pinned Git blobs
is a separate integration task; `integration/check_upstream_ast.py` supplies that
check but was not executed in this runtime. See `PROVENANCE.md` for exact scope.

The supplied adapter handles the ordinary interned-list `FastScan` state. It does
not maintain component-owner arrays, saturated weights, or other scanner-specific
metadata. Do not drop it into those subclasses without a separate adapter and tests.

The code is an exact-arithmetic research prototype with executable certificates,
not a formally verified implementation or a hardened untrusted-certificate service.
The paper distinguishes proved mathematics, tested implementation behavior,
conditional bounds, and unperformed integrations. Further research questions appear
in the further-research section of the paper.

## Layout

- `article/`: maintained TeX, generated table inputs, build script, PDF, standalone export.
- `src/`: geometry certificates, orders, finite transfer, guarded scanner, validated driver,
  and descending-grid generator.
- `tests/`: algebraic, geometry, certificate, scanner, and failure-path tests.
- `experiments/`: independent cube oracle, benchmarks, exhaustive checks, certificate
  generation/verification, and demonstration CLI.
- `results/`: raw trials, summaries, exact input/certificate JSON, and test logs.
- `reference_upstream/`: explicitly scoped, source-derived baseline fixture.
- `integration/`: production handoff requirements and pinned-source audit utility.

All additions are offered under MIT-0; the source-derived fixture preserves its
upstream MIT-0 attribution. No third-party paper PDFs or font files are redistributed.
