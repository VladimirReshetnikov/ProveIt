# Integral tension kernels for compressed unknot certificates

Research contribution for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

**This package does not claim a general quasi-polynomial unknot recognizer.** It
contains a proved, implemented local optimization kernel and a bounded-phase
complexity theorem. It does not change the maintained recognizer or its defaults.

## Main results

A fixed multiplier `a` defines a commuting family of integral shears
`x -> a^(-z[-x]) x a^(z[x])`. On cyclically reduced relators, all non-`a`
letters survive. Total cyclic length is a compressed weighted L1 tension
objective. An exact capacity-bit-scaling circulation algorithm solves its
integer minimum, and a separate primal-dual verifier proves optimality without
running an optimizer. Balanced graphs and forests of parallel-edge bundles
have faster exact solutions.

The direct output constructor needs no generic compressed-word equality or
free-reduction calls. It increases the number of repetition-grammar rules by
at most a constant factor. Consequently, `q` strictly shortening shear phases,
including certificate generation and independent replay, have cost
`poly(initial encoded size) * 2^O(q)`. For presentations of polynomial encoded
size in a crossing parameter `n`, `q = O(log(n)^2)` gives `n^O(log n)`.
The phase bound and a sufficiently general terminal decision procedure are
NOT proved for arbitrary knot diagrams.

See **article.pdf** and **article.tex** for complete proofs, scope, experiments,
an automorphically minimal infinite-cyclic obstruction family, and further
research questions. No claim of priority over all existing literature is made.

## Reproduce

Python 3.10+ and the standard library suffice; the executed environment was
CPython 3.13.5 on Linux. From this directory:

```sh
python -B -m unittest discover -s tests -v
python -B experiments/audit.py
python -B experiments/benchmark.py
python -B experiments/make_tables.py
python -B -m shear_kernel verify certificates/star_Z_500.json
python -B -m shear_kernel demo --bits 500 --branches 6 --output demo.json
sh build.sh
```

The PDF build needs `pdflatex` and its standard mathematics/typography packages.
The benchmark overwrites its result JSON; retain the supplied measurements
before rerunning on another machine. `make_tables.py` regenerates the table
fragments, stage aggregates, and marked numerical passages in `article.tex`;
run it before rebuilding the PDF after a new benchmark.

## Recorded evidence

The delivered test log records 51 passing tests. The deterministic audit
checks 1,200 circulation instances, 360 stages from 180 connected braid
closures, 1,012 individual relator images, and three serialized large abstract
presentation traces. Tests include an additional 120 forest/circulation
comparisons, independent decorated-word replay, small exhaustive potential
searches, and malformed certificate checks.

Joint optimization gives a strictly shorter one-step result on 21 of the
180 **raw** braid presentations, but on **none** of their 180 post-singleton-
elimination presentations. The latter matters because the maintained producer
already performs singleton elimination first. The small-stage timing corpus
also shows overhead. These data do not establish a production speedup.

Synthetic multi-run infinite-cyclic presentations do exhibit fewer phases and
faster same-terminal descent than the mathematical selected-direction/eager-
line baseline. The baseline is independently implemented in the same harness;
it is not a timing of the current production scheduler. See raw samples and
precise contracts in `results/benchmark.json` and the article.

## Integration status and trust boundary

**No upstream checkout test, maintained test-suite run, or end-to-end recognizer
benchmark was executed.** Repository source was inspected through the GitHub
connector at the pinned commit recorded in `integration/STATUS.json`.
The source-pinned gateway `integration/check_upstream.py` is supplied for a
maintainer to run; its execution status is explicitly NOT EXECUTED.

`shear_kernel/adapter.py` offers two different routes. Legacy replay decomposes
a shear into existing Whitehead/Whitehead-power moves and lets the host rebuild
its own exact cyclic representatives. The direct constructor is reserved for
an explicitly new atomic-shear protocol: its roots can be cyclic rotations of
legacy replay roots, so mixing them with positional legacy relator moves is
unsafe. The linear rule-growth theorem applies to the retained repetition
representation, not to the unexecuted legacy gateway.

All public presentation results are abstract group results. A knot verdict
requires independently validated classical one-component diagram provenance
and the full presentation, not a quotient or an arbitrary supplied group.
A stalled or resource-limited probe is inconclusive. The supplied `Budget`
charges circulation work, not a whole-service deadline or memory allocation.
Untrusted-input service hardening remains a host responsibility.

The SHA256 source field binds a canonical serialized DAG for standalone
certificates; it is not used as a word-equality oracle. During multi-phase
independent replay, later source hashes are advisory because the verifier uses
a different equivalent DAG. Every objective, dual witness, and next image is
recomputed from the actual replayed words.

## Suggested repository destination

Add this directory, for example, at:

`Topology/UnknotRecognition/research/integral_shears_20261008/`

Do not replace maintained production modules automatically. Read
`integration/INTEGRATION.md` before considering a pipeline change. The package
contains no redistributed third-party paper PDFs or upstream implementation
files. `SHA256SUMS` covers the delivered files other than itself.
