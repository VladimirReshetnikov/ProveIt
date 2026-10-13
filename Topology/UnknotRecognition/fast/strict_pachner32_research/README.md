# Optional strict Pachner 3→2 preprocessing

This package compares the same bounded whole-diagram crushing recognizer with
`reduce_pachner32=False` (`baseline`) and `True` (`pachner32`). The optional
policy greedily accepts independently verified, strictly shrinking 3→2 moves
after vertex reduction and boundary peeling, before preparing Euler algebra.
The baseline remains the public default. These finite controls do not establish
general quasi-polynomial recognition, monotonicity of the resolving-set
parameter, or a universal performance improvement.

`common.py` fixes all inputs, both complete option maps, the nine shared budgets,
and the benchmark protocol. Each whole call uses the transversal conflict policy
and polynomial LP backend, 256 tree nodes, and 10,000 pivots, anchors, candidate
hitting subsets, ellipsoid iterations and feasibility calls. All strict topology
reductions share `max_crushes` when that cap is supplied. The experimental maps
leave it unlimited: strict tetrahedron descent bounds their number. The only
option difference between arms is the new Boolean flag.

The audit retains eight complete *returned calls*: circle, trefoil, figure eight,
and the visible two-trefoil sum, each under both arms. A returned INCONCLUSIVE
result is recorded with its authenticated partial chain, all counters and exact
budget controls. It is not a complete recognition verdict. The raw driver runs
on the whole diagram; this experiment does not exercise the separate visible
factor wrapper. No arbitrary wall cutoff discards difficult calls. Interrupted
files preserve `passed=False` and incomplete coverage.

The benchmark was declared before its results. It uses circle, trefoil and
figure eight: one warmup per arm, three alternating-order pairs, and one
baseline/baseline pair per diagram, 30 calls altogether. Every timer includes a
fresh whole recognition, independent conclusive or partial proof replay,
canonical result serialization and SHA256. Module initialization and prepared
input PDs remain outside. Warmups retain full results; every timed serialization
must match the corresponding complete audited result exactly. Recognition speed
ratios are computed only for a common conclusive verdict. Baseline A/A ratios
are retained as a noise control; no statistical population claim follows.

Run from `Topology/UnknotRecognition/fast`, after all native and research sources
are frozen:

```sh
PYTHONPATH=. python -m strict_pachner32_research.audit \
  --output ../synthesis/data/strict-pachner32-audit.json
PYTHONPATH=. python -m strict_pachner32_research.check_evidence \
  --audit ../synthesis/data/strict-pachner32-audit.json
PYTHONPATH=. python -m strict_pachner32_research.benchmark \
  --audit ../synthesis/data/strict-pachner32-audit.json \
  --output ../synthesis/data/strict-pachner32-benchmark.json
PYTHONPATH=. python -m strict_pachner32_research.check_evidence \
  --audit ../synthesis/data/strict-pachner32-audit.json \
  --benchmark ../synthesis/data/strict-pachner32-benchmark.json
```

Store generated outputs outside this package. Its pin map includes every native
Python module and every package file, including the independent checker and
archived inputs. It excludes caches and never hashes its own output artifacts.
The audit and benchmark require unchanged source pins at completion. The checker
does no discovery: it replays saved certificates, binds input PDs and exact
configurations, validates coverage and charged counters, and recomputes sample
hashes, order and ratios.

## Separate historical archive and fresh replay

`data/generation/manifest.json` identifies immutable copies of the exploratory
scripts and results that motivated this implementation. JSON inputs use
deterministic gzip; the manifest preserves both original uncompressed SHA256
and stored-byte SHA256. Embedded native source pins are **historical generation
or historical replay pins**, never claims about the current native source.
Generation scripts preserve their original scratch paths. The commands above
are the portable current replay route.

Fresh `archival_replay` coverage is separate from the eight new diagram calls:

- Three authenticated historical initial diagram chains and nine supplied
  legacy Pachner packets: trefoil 10→9→8, figure eight 13→12, two-trefoil sum
  23→22→21→20→19→18→17. The endpoint scan excludes precisely the strict candidate
  class; it does not certify minimal triangulations.
- Three saved full-root negative Euler proofs on the 8-, 12-, and
  17-tetrahedron successors. Their complete branch trees split only within
  sets of sizes 1, 1 and 3, respectively, giving upper bounds on the resolving
  parameter for those exact labelled sources. No lower bounds at the new
  sources were searched or retained.
- A three-tetrahedron all-region control, including two formal boundary
  selfattachment pairs, replayed with the new source-bound verifier.

The archived Regina checks corroborate the same nine moves by exact
combinatorial isomorphisms and the tiny selfattachment example. They are
historical oracle outputs; a fresh native replay does not rerun Regina. The
independent native relative-boundary checks supply the current certificate
validation. The old `DESIGN.md` opening describes the initial scan, before the
separately archived capped Euler queries were run.

The previously published 23-tetrahedron two-trefoil source has a separately
proved lower bound of five from its retained root-ray conflicts. This package
binds that exact source and verifies the six moves and the endpoint upper bound
of three; it does not repeat the previous 35-ray STANDARD-rank audit. This is a
finite strict improvement after simplification, not a family theorem or an
invariance claim for the resolving parameter.
