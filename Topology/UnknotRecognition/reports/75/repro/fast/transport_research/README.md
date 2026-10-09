# Coherent cocycle transport: reproduction and integration

The production modules transport an integral cocycle through a checked
formal Pachner region, then select its coherent normal fibre. The fibre's
topology can change. Every positive source-diagram result uses the general
native disc-component certificate and the independent source consumer.

## Package layout and input requirements

Run the commands below from the research package's top-level directory,
which contains `fast/`, `synthesis/`, and `reproduce/`.

Required files outside the `fast/` snapshot are:

- `synthesis/data/coherent-obstruction-certificate.json`: the maintained
  eight-tetrahedron obstruction and its preceding construction record.
- `reproduce/cocycle-source-cases.json`: a compact extraction of the source
  diagrams from the prior `cocycle-reuse-audit.json` record. Its required
  shape is `{"source_cases": [{"source": {"name": ..., "pd": ...,
  "expected": ...}}, ...]}`. Preserve all 84 source entries; the command's
  sixteen-crossing cutoff selects the measured 82.

The complete 9.2 MB prior audit is unnecessary. The driver retains that
audit's filename as its project default for backward compatibility; the
explicit `--corpus` argument below selects the compact packaged fixture.
There are no executed Git commands, network downloads, or absolute
workspace/baseline paths in these drivers. The baseline commit string is
provenance metadata only.

The transport-specific commands do not use files under `reports/`.
Some unrelated tests in the full repository snapshot do require those
historical reference modules. Preserve the package's supplied `reports/`
dependencies when running its complete regression suite.

The measured interpreter was Python 3.12.14. The production project declares
Python 3.10 or later. These research drivers import directly from `fast/`,
so set `PYTHONPATH=fast` even if `fastunknot` has also been installed. The
project's package-discovery configuration does not install research modules.

Regina 7.4.1 is required only for the independent Regina arm of `local`
mode. The other transport modes use the native implementation and standard
library. Pytest runs the supplied tests; the maintained measurement
environment used pytest 9.1.1.

## Exact commands

Targeted tests, including the existing move and source-consumer regressions:

```bash
PYTHONPATH=fast python -m pytest -q \
  fast/tests/test_cocycle_transport.py \
  fast/tests/test_cocycle_transport_splitting.py \
  fast/tests/test_cocycle_transport_callbacks.py \
  fast/tests/test_pachner32.py \
  fast/tests/test_coherent_obstruction.py \
  fast/tests/test_normal_transport.py
```

Scalar identities, 120 mixed native/Regina moves, and the explicit genus-two
escape:

```bash
PYTHONPATH=fast python -m transport_research.audit local \
  --steps 30 \
  --output reproduce/generated/cocycle-transport-local.json
```

To run that audit without Regina, add `--no-regina`. This still performs
native transport and certificate replay, but deliberately omits the
independent Regina comparisons.

The 82-diagram, three-arm native audit:

```bash
PYTHONPATH=fast python -m transport_research.audit corpus \
  --corpus reproduce/cocycle-source-cases.json \
  --max-crossings 16 \
  --output reproduce/generated/cocycle-transport-corpus.json
```

Controlled, identical-output candidate-scoring comparison:

```bash
PYTHONPATH=fast python -m transport_research.audit benchmark \
  --sizes 16 32 64 128 256 --rounds 5 \
  --output reproduce/generated/cocycle-transport-benchmark.json
```

The explicit connectivity-splitting counterexample:

```bash
PYTHONPATH=fast python -m transport_research.splitting \
  --output reproduce/generated/cocycle-transport-splitting.json
```

Every driver creates its output directory when needed. Generated timing
values depend on the interpreter and machine; compare structural outputs,
certificate acceptance, and the shape of the performance trend. Run the
benchmark without concurrent heavy computation. Its five trials alternate
the two arm orders.

## Recorded results and their interpretation

The scalar audit checks all 3,125 tuples in `{-2,-1,0,1,2}^5`. The main unit
tests also cover 20,000-bit scaling, identical guard counts across scale,
strict proof mutations, input immutability, and cancellation.

A final callback-only correction followed the original local and corpus
measurements. It shields callback exceptions from malformed-input catches
and restores their original exception objects. Its dedicated regression
injects `NormalOrbitError`, `ValueError`, `CocycleLimit`, and `RuntimeError`
at every callback position in the direct checker, producer, candidate
enumerator, and descent. No mathematical formula or candidate policy changed.

The exact four source files referenced by the original local/corpus
`source_sha256` fields are retained, with their original relative names, in
`measured_sources_before_callback_fix.zip`. Those measured hashes were not
relabelled as hashes of the corrected sources. The final candidate benchmark
was rerun after the correction; its source hashes refer to the corrected
files. New reruns of local/corpus audits naturally record the corrected
source hashes. The earlier benchmark is separately retained as
`synthesis/data/cocycle-transport-benchmark-pre-callback.json`.

The mixed geometric audit has 63 upward and 57 downward moves. All 120
agree with Regina's replacement up to triangulation isomorphism and with
its coherent Euler count. The observed nonzero Euler changes are one each
of `-4`, `+4`, `-2`, and `+2`; the other 116 changes are zero.

The corpus compares first-site/re-extracted-gauge, first-site/transport,
and score-selected/transport. All 246 runs complete. Each arm makes 144
collapses and finds 15 supplied-vector compressing-disc positives. Both
transport arms' 15 positives pass the complete independent source consumer:
there are **30 positive source replay runs**. The retained file has **32
distinct positive bundles across the three arms**, which includes research
bundles from the re-extracted-gauge reference. Those reference bundles have
schema `diagram-regauge-research-v1` and are not accepted by the new transport
consumer. The `diagram-transport-disc-v1` bundles are its source-bound proofs.

The corpus shows no coverage gain. First-site and scored transport have
identical final Euler and piece counts on every input. Re-extracting the
gauge changes the final piece count on twelve inputs. The aggregate totals
are 16,170 pieces for re-extracted gauges and 16,297 for either transport arm.

The corpus times are **not** a matched end-to-end speed comparison: positive
transport runs include an additional full source replay, and construction
of the initial canonical exterior and seed is shared outside the timed arms.
The controlled benchmark, by contrast, compares identical candidate-score
outputs on one-vertex triangulations. Its reported speedups apply only to
scoring all candidate moves, not to complete unknot recognition.

The splitting example independently certifies a 24-piece disc becoming
an 11-piece disc plus two four-piece spheres under a 3--2 move. Euler
characteristic rises from 1 to 5, while total piece count falls from 24 to 19.
It supplies a concrete reason to retain the general component verifier.

## Integration contracts

`transport_cocycle(before, heights, after, move_certificate)` takes an
already specified legal replacement. Its `certificate` contains the move,
the five normalized formal heights, output heights and coordinates, and
the two exact global cell-count changes. `verify_cocycle_transport` imports
no transport, cocycle-seed, or Pachner-move producer.

`cocycle_collapse_candidates` scores all currently legal degree-three sites.
`descend_cocycle` performs a deterministic downward epoch and returns steps
of the form `{"triangulation": after, "transport": proof}`. These steps feed
`normal_transport_verify.verify_transport_disk_certificate` directly.
The optional root-level wrapper is
`normal_transport.transport_seed_decide`.

No default recognition schedule is changed. A failed restricted search is
inconclusive. The larger quasi-polynomial objective still needs a complete,
bounded discovery argument and its geometric hierarchy interfaces.

The unimplemented vertex-link-peeled scoring lemma is developed separately
in `PEELED_EULER.md`. It is an exact data-structure lemma, not an observed
recognition improvement.
