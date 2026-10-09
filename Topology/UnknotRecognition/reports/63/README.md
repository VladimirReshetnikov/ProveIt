# Power-conjugacy saturation for unknot recognition

Research continuation for `ProveIt/Topology/UnknotRecognition`, 8 October 2026.

**Read `docs/article.pdf` first.** This package develops a source-checkable local
presentation operation, proves its exact graph-level scope, implements independent
certificate replay, and supplies reproducible experiments. It does **not** prove
unrestricted quasi-polynomial unknot recognition. It does not modify the maintained
recognizer or establish a native production speedup.

## Main results

Verified relations `x_s^a = u x_t^b u^-1` define a graph with signed binary exponent
labels. In a classical knot group, an inconsistent cycle of **absolute** exponent
ratios forces its entire connected component to be trivial. A signed inconsistency
is also decisive when every conjugator on that cycle is proved trivial. The graph
criterion is sharp after the fixed conjugator words and source-generation constraints
are forgotten: all surviving vertices can simultaneously be nontrivial in one trefoil
group. The article proves all parts and attributes the underlying knot-group
balancedness lemma to Himeno–Motegi–Teragaito.

For the specified exhaustive exposed-donor interface on literal presentations,
complete deletion-only saturation has a conservative `O(N^5 log^2(N+2))` bit bound.
Binary power blocks provide an independently checked unconditional rule: for
`<x,y | x^(a_i)=y^(b_i)>`, the group is trivial exactly when the gcd of its two-by-two
exponent minors is one. The sufficient direction applies inside any larger group.
The paper gives a short source-minor certificate and a compressed family with no
initial primitive-forest move.

## Reproduce

Python 3.10 or later; standard library only. The recorded runtime was Python 3.13.5
on Linux. Run from this directory:

```sh
python verify_manifest.py
python code/run_tests.py --output /tmp/power-tests.json
python code/audit_braids.py --output /tmp/power-audit.json
python code/benchmark.py --output /tmp/power-benchmark.json
python code/benchmark_sieve.py --output /tmp/power-sieve.json
sh build.sh
```

`build.sh` requires `pdflatex` and the packages in `docs/article.tex`; it regenerates
tables from the retained JSON and compiles the article three times. No network access
is needed. Benchmarks use shuffled paired A/A/B/B arms and record all samples,
warm-ups, machine metadata, and source hashes checked before and after each run. New timing samples are
machine-dependent and should not silently replace the shipped observations. The
historical timing records are deliberately separate; see `data/historical/README.md`.

## Source-bound examples

```sh
python code/cli.py examples/circle.json --proof /tmp/circle-proof.json
python code/cli.py examples/circle.json --verify /tmp/circle-proof.json
python code/cli.py examples/figure_eight.json --cube
```

The braid frontend checks that the closure has one component, reconstructs its full
Artin presentation, applies an explicit difference basis, and independently replays
every positive proof. Its literal source construction is capped and has no claimed
polynomial diagram-input bound. The optional `--cube` fallback is a **small exponential
reference oracle**, not the maintained fast scanner. Without a successful positive
certificate, the probe returns `INCONCLUSIVE` or `RESOURCE_LIMIT`, never `KNOTTED`.
An arbitrary presentation or unauthenticated graph is not a knot input.

## Validation and measured scope

The retained run passes 24 test methods. The separate braid audit checks 3,227 inputs
against independently implemented reduced Khovanov homology over F2: 1,943 inputs
are unknots, 1,428 receive positive certificates, and 515 unknots are missed; all
1,284 nontrivial inputs remain without a false positive. These are presentations,
not 3,227 distinct knot types. An ablation finds **no extra coverage** over pure-power
deletion on this small corpus. A concrete missed three-braid has a simple equality
substitution that the native forest method can exploit.

The modular sieve is exact because every successful witness is replayed over the
integers and every undetected component receives rational fallback. Some exponent
and cycle-length families alias modulo 65,537; those negative timing controls are
retained. Large binary capacity tests include 128 independent pairs and 16,384-bit
exponent parameters. These are supplied presentation families, not hard knot diagrams.
The article separates kernel timing, standalone source timing, and unmeasured native
integration. No native test suite or native corpus benchmark was run for this package.

## Layout

- `docs/`: article, LaTeX source, generated tables, bibliography metadata.
- `code/`: exact graph producer, independent graph/source checkers, literal donor
  discovery, deletion closure, power-minor certificates, small homology oracle,
  tests/audit/benchmark entry points, and CLI.
- `tests/`, `data/`, `examples/`: reproducible validation and all retained observations.
- `integration/`: pinned source audit, proposed native contract, and claim ledger.
- `MANIFEST.sha256`, `verify_manifest.py`: integrity check for delivered files.

Suggested nonconflicting destination:
`Topology/UnknotRecognition/research/power_conjugacy_20261008/`.
No numbered report slot is assumed and no remote repository files were changed.

The new article and code are supplied under MIT-0, consistent with the repository's
stated licensing. Third-party papers are cited, not redistributed. No Lean
formalization or independent peer-review validation is claimed.
