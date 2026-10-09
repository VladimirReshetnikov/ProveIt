# Compiled component profiles and event-driven port quotients

An additive mathematical research package for **ProveIt / UnknotRecognition**.
The article, complete proofs, new reference code, executed tests, raw experiments,
and a native integration gate are included.

**Main result:** on `m` fixed source atoms, at most `2*m - 1` full-port coning
steps can change the component partition, and the bound is sharp. A compressed
program with binary repetitions can therefore be processed by its actual changes,
without expanding its instruction sequence.

## What this package establishes

A source-atom profile records the number of points of each component in each
fixed atom. Multiplicities remain binary. Capacity-aware scalar packing obtains
the entire joint profile census from one weighted orbit histogram. The table
then supports new atom-constant additive observations and exact full-port
quotients, without new orbit searches or point expansion.

The quotient engine activates each type population once and scans each support
edge at most once in a monotone phase. A grammar with `g` nodes supports first
count-threshold search in at most `g + 1` state trials. All effective event indices
can be recovered in `O((h + 1)*g)` trials, where `h <= 2*m - 1`. Binary arithmetic
and output bit lengths are charged; these are not constant-time claims for
arbitrarily large integers.

The paper proves an exact observational-equivalence theorem and a four-point
counterexample showing why the cache cannot answer arbitrary pointwise
attachment queries. Coning **all points** of a port is not the same operation
as gluing points by a specified bijection.

## What is not established

This package does **not** prove general quasi-polynomial unknot recognition.
It does not find useful normal vectors, certify diagram-to-exterior provenance,
control source refinements across an entire hierarchy, or model arbitrary
cutting/gluing operations. Additive charges remain charges on old source points;
they are not automatically invariants of a newly constructed manifold.

The baseline was inspected at commit
`1fab6d945be52857cce48b6459075e6194622001`. The newer native sparse-incidence and
weighted-component modules are prior work, not results claimed new here.

**Native execution status: NOT_RUN.** A runnable native checkout was unavailable.
The adapter matches the inspected API, but it must pass the supplied gate in the
target checkout before integration. The core tests use explicit, separately
named literal finite oracles. There are no whole-knot or native-AHT speedup
measurements in this delivery. No repository files were changed remotely.

## Executed evidence

The deterministic suite passes **25 test methods**. Its internal checks include
9,338 exhaustive finite coning cases, 500 random packing sources under both
codecs, 7,000 sequential cone comparisons on 700 sources, 400 random grammars,
16 sharp-height families, huge binary populations and indices, malformed inputs,
source-relative certificate mutations, and producer-disabled independent replay.

For a five-node delayed repetitive program, the measured `b=4096` case used
**2 state trials** for direct threshold descent versus **8,194 evaluations** for
prefix bisection. The retained batched medians are approximately 0.0105 ms and
49.98 ms. These are controlled **algebra-kernel** measurements on an intentionally
repetitive family, with initial source compilation excluded. They are not
benchmarks of the maintained recognizer. Raw samples, a noisy initial unbatched
run, identical controls, exact operation counts, and source hashes are retained.

## Reproduce

From this directory, using Python 3.10 or newer (executed here with 3.13.5):

```sh
python -m unittest discover -s tests -v
python experiments/audit.py
python experiments/benchmark.py
python experiments/make_tables.py
python examples/demo.py
sh paper/build.sh
```

Core execution needs only the Python standard library. Building the paper needs
`pdflatex` and the standard packages named in `paper/main.tex`. The bibliography
is included as `references.tex`, so BibTeX is not required; `references.bib` is
also supplied for integration. Repeated LaTeX passes resolve cross-references.

## Native gate

Run this against an actual target checkout:

```sh
python integration/native_gate.py \
  --fast-root /path/to/ProveIt/Topology/UnknotRecognition/fast
```

The gate uses the actual maintained weighted producer and independent verifier.
It is designed to test 200 random interval systems under both packing modes,
direct-vector versus packed equality, source-bound replay, source mutation
rejection, and a binary `2**1024` parallel-population system. These are gate
requirements, not completed native test counts. A missing dependency fails the
gate rather than selecting a literal fallback. A successful future run writes
`results/native_gate.json`; the historical delivery status is kept separately.
Run the maintained suite and paired native compilation/reuse benchmarks next.

## Layout and integration

`paper/main.pdf` is the article; `paper/main.tex` includes the section files.
`compiled_ports/` contains the additive package, `tests/` the finite checks,
`experiments/` the reproducible drivers, `results/` the evidence, and `integration/`
the source audit and native gate. `examples/` includes the counterexample and an
exact delayed-program history.

Suggested additive location:
`Topology/UnknotRecognition/research/compiled_port_quotients/`.
No maintained dispatcher should be changed until source-bound integration tests
pass and a real consumer's full-port semantics are proved. No upstream code is
vendored. New reference source is released under MIT-0; upstream dependencies
retain their own terms.
