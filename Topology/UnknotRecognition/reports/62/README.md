# Sparse Certified Component Incidence

An additive research contribution for `VladimirReshetnikov/ProveIt`, beneath
`Topology/UnknotRecognition`, based on commit
`274909dd8724e411ece14e47ac4addea717aeca6`.

The article is `article/sparse_incidence.pdf`; its self-contained LaTeX source is
`article/sparse_incidence.tex`. It contains complete proofs, implementation
contracts, paired measurements, a gluing obstruction, and nine further research
questions. This package does **not** implement a general quasi-polynomial unknot
recognizer or establish a whole-knot timing improvement.

## Mathematical contribution

For a nonnegative signature histogram with `r` port labels and `s` positive
entries, recover every entry with at most `r*s` logical subset queries. Each query
is an unweighted coned interval-orbit count, and all counts share one work budget.
No prior sparsity bound is required. An independent checker establishes atom
masses using forward sums and dominating zero sets, then proves completeness by
conservation of total mass. It does not rerun sparse recovery.

Classical weighted Agol–Hass–Thurston theory implies polynomially many signatures
for **explicit interval-union ports**. The article derives a conservative explicit
support bound from its cycle and breakpoint estimates. Therefore the unweighted
sparse reduction is polynomial in the full binary interval input, without a
logarithmic restriction on the number of ports. This is not the first polynomial
weighted-orbit algorithm: it replaces the repository's dense Boolean-array
interface while reusing its unchanged unweighted kernel and independent checker.

The signed extension returns signature-resolved parity-consistent and
parity-inconsistent counts. Calling them orientability counts requires separately
established geometric provenance for the parity labels. A four-point example
proves that incidence, even augmented by per-port point multiplicities, cannot
alone determine arbitrary future gluing.

## Reproduce the focused results

Use Python 3.11 or newer; the recorded execution uses CPython 3.13.5. The code uses
only the standard library. Run from the extracted package root:

```sh
python experiments/run_tests.py
python experiments/benchmark.py --rounds 7 --scale-rounds 3
python experiments/make_tables.py
python experiments/make_examples.py
sh article/build.sh
```

PDF rebuilding requires a TeX installation with the standard packages named in
the source. On systems without a POSIX shell, run `pdflatex` on
`article/sparse_incidence.tex` three times from the `article` directory.
The `.tex` embeds its numerical table rows and bibliography; the separate table
fragments are optional generated artifacts.

The test runner verifies four exact upstream Git blob hashes before running the
36 new test methods. Cases include all 6,654 coefficient-0/1/2 histograms for up
to three labels, 1,000 literal interval systems, 300 dense comparisons, 300 literal
parity graphs, proof mutations, shared budgets, and 128 labels on a universe of
size `2**16000`. The full upstream repository suite was **not** run here.

## Measurements and limits

The final benchmark dataset contains eight paired workloads with seven measured
rounds and one warmup, plus three sparse-only scale workloads with three measured
rounds and one warmup. Arm ordering is shuffled. A duplicate sparse arm is an A/A
control. The certified arm includes production **and** independent replay; JSON
serialization is not timed. All final timed calls completed.

Three disjoint 12-port workloads reduce orbit calls from 4,096 to 79; only 23
coned traces are retained. Coincident and nested ports improve chiefly by avoiding
dense arrays, not by reducing orbit queries. Full-support controls at three and
four ports are about 25–26% slower. The largest identical-arm control discrepancy
is about 5%, so small timing percentages should not be overinterpreted.

These are supplied interval-relation workloads, not native knot diagrams or
triangulations. The exact baseline is the unchanged maintained dense routine.
An earlier harness-limited 64-port disjoint attempt produced only a partial log;
it is retained separately, excluded from the final dataset, and supplies no
completed timing ratio. The final disjoint scale case uses 32 ports.

## Integration without overwriting maintained code

The `overlay/` tree adds six modules and one test file. It changes no existing
recognizer dispatch, dense API, Rust source, or orbit scheduler. The `reference/`
copies are **not** overlay files: they exist only to reproduce this delivery.
The empty reference `__init__.py` is a local package shim, not an upstream copy.

A conservative cross-platform installer is provided:

```sh
python experiments/integrate.py --repo /path/to/ProveIt
python experiments/integrate.py --repo /path/to/ProveIt --apply
```

The first command is a dry run. Both commands require the four target dependency
files to match the pinned hashes. Existing identical overlay files are left
alone; existing different files cause refusal rather than overwrite. The
installer does not modify Git metadata, commit, push, or change documentation.
After installation, run the focused suite and then the full repository suite:

```sh
cd /path/to/ProveIt/Topology/UnknotRecognition/fast
python -m unittest discover -s tests -p test_sparse_incidence.py -v
python -m unittest discover -s tests -v
```

## API example

```python
from fastunknot.sparse_incidence import analyze_sparse_port_incidence
from fastunknot.sparse_incidence_verify import (
    verify_sparse_port_incidence_certificate,
)

size = 10
pairings = []
ports = [[(0, 3)], [(2, 5)]]  # Half-open port intervals.
result = analyze_sparse_port_incidence(
    size, pairings, ports,
    max_cycles=10000,
    max_orbit_queries=1000,
    record_certificate=True,
)
if result["status"] == "COMPLETE":
    assert result["histogram"] == [[0, 5], [1, 2], [2, 2], [3, 1]]
    assert verify_sparse_port_incidence_certificate(
        size, pairings, ports, result["certificate"]
    )
else:
    # No histogram, orbit_count, or certificate is published on exhaustion.
    print(result["reason"], result["stats"])
```

A missing mask means count zero; a present mask `0` is the unmarked component
count. Pairings are native objects or inclusive `[a,b,c,d,sign]` rows, in an
explicit list or tuple. Integers reject Boolean values. A signed row adds parity
as a sixth entry; signed outputs are `[mask,consistent,inconsistent]`.

`max_cycles` and `max_orbit_queries` cover the entire unsigned run and, in the
signed wrapper, both the base and cover. Signed `max_terms` limits each histogram
separately. Ordinary callback exceptions propagate; the implementation's reserved
schema/limit exception classes are internal control signals. A cycle cap does
not bound normalization, residual scans, memory, or serialization. Use a
cooperative `check` callback and external process/I/O limits as appropriate.

## Contents and evidence

`article/` contains the PDF, TeX, generated table fragments, and build script.
`overlay/` contains only integration additions. `reference/` contains exact native
dependencies. `experiments/` contains reproducible runners, an endpoint-sweep
benchmark reference, and the conservative installer. `examples/` contains actual
unsigned/signed certificates and the gluing obstruction. `results/` contains raw
samples, source hashes, test results, build evidence, and the separately labelled
incomplete earlier benchmark log. `RESEARCH_STATUS.md` records what is proved,
inherited, measured, and still missing. `SOURCE_MANIFEST.json` and `SHA256SUMS.txt`
record provenance and file integrity.

The implementation and written contribution use MIT-0. The dependency snapshots
retain their upstream text and are distributed under the repository's declared
MIT-0 terms. No third-party paper PDFs or font files are redistributed.
