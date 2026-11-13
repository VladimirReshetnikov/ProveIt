# P65 endpoint replay after the P72 source refactor

After origin commit `e1b79c42eb` changed `P72Exact.lean` and
`P72Power.lean`, the historical captured-provider replay no longer matched
the current source hashes. On 2026-11-04, an isolated overlay replayed the
visible affected import closure without using cached outputs:

1. `P72Exact`, `P72Power`, `P72Facts`, `P65Facts`;
2. `P72ConvArith`, `P72Converse`, `P65Converse`, `IPRAPositive65`.

All eight Lean invocations exited 0. The endpoint log reports
`positiveBridge`, `native_equivalence`, `standard_equivalence`, and
`reference_equivalence` with axioms `[propext, Classical.choice, Quot.sound]`;
no `sorryAx`, compiler errors, or warnings appeared in the eight logs. The
endpoint object is byte-identical to the earlier captured endpoint object;
this is observed equality of outputs, not evidence that recompilation was
unnecessary. Four of the eight rebuilt objects differ from their predecessors.

The inputs and their limits remain important: this is a replay against the
existing captured-provider overlays, **not** a clean rebuild of the full
current source tree or an audit of all transitive package, dynamic-library,
or source/object ancestry. The closure follows only imports visible in the
two recorded manifests; dependencies hidden behind their captured objects
remain inherited. The compiled declarations concern the Lean graph and
selected consistency formalization; connecting these to an external PDF
rendering remains separate. This check does not establish the 88/89 reverse
implication or any additional equation reduction.

## Reproduction and recorded diagnostics

`prepare.py` verifies source hashes across all 92 recorded modules (allowing
exactly the two post-merge hashes), their old object hashes, and the 86
recorded direct provider bindings. It computes the 4+4 import closure,
creates a symlink overlay without changing the original providers, and
unlinks all eight selected output links. It refuses to overwrite the output
directory. `run.py` refuses existing selected output objects, compiles all
eight sequentially with `-M6000 -j1`, a 300-second per-module timeout, and
records command, elapsed time, output hashes and exit status. `audit.py`
rechecks the output files and endpoint axiom reports, and verifies the 92 old
provider objects and 86 direct bindings still have their recorded hashes.
The audit refuses Python's optimized mode. These checks do not authenticate
the transitive ancestry of the captured objects.

The recorded workspace and `/tmp` paths are machine-specific; the overlay
and compiled objects are not committed. In that captured environment, with
the Lean slot available and `/tmp/p65-post-merge-replay` absent:

```sh
python3 Computability/DiophantineConsistency/research/p65-post-merge-replay/prepare.py
python3 -u Computability/DiophantineConsistency/research/p65-post-merge-replay/run.py
python3 Computability/DiophantineConsistency/research/p65-post-merge-replay/audit.py
```

`plan.json`, `results.json`, `logs/`, and `audit-result.json` preserve the
observed plan and diagnostics; their absolute paths describe the captured
run. No cached replay is represented as an additional compilation.
