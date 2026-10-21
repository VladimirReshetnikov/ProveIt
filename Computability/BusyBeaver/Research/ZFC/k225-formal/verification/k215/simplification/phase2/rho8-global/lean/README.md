# Lean: 629-node direct dominated-rho8 proof

The [canonical proof](../../../../../../../../../Lean/BusyBeaver/ZFC/DomRho8.lean) now uses 629 named proof nodes and 939 input
terms, down from the earlier 674-node checkpoint. It is 128,177 bytes, 7,240 fewer
than that checkpoint and 81.4% below the original 689,857-byte module. The shared
plan additionally supplies 735 instructions to the Rocq interpreter. These are
proof-size results; the shared replay plan adds data and code, so no net repository
byte saving or optimum is claimed.

The [generator](../../../../../../generate_domrho8_lean.py) replays the [shared original-node plan](../../../../../../rho8plan/README.md)
for the exact immutable Source149 certificate. The global selection may use a
later original theorem schema, but the replay emits a verified acyclic order;
every Lean proof references only an earlier emitted theorem. The direct emitter
still checks each retained step, substitution and native zero-alias conversion.
The optimizer, solver and plan have no role in the theorem's assumptions.
`DomImp`, `le_l`, `le_r`, `sub`, and the arbitrary-Nat `rho8_all` statement are unchanged.

The exact source plus [five typed API clients](API.lean) passed in 8.281 seconds,
with zero warnings and two reports containing only `propext` and `Quot.sound`.
The [invocation record](actual/result.json), [log](actual/compiler.log) and
[checked source](actual/WithAudit.lean) retain that isolated check. The final
endpoint dependency-closure check is recorded separately by the phase2 build.

From the repository root, regeneration uses only Python's standard library:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/generate_domrho8_lean.py \
  Computability/BusyBeaver/Research/ZFC/k225-formal/lean217/dominated_rho8_full_certificate.json \
  /tmp/DomRho8.lean
```

For that exact input, the default reads the maintained `rho8plan/plan.json` and
`replay.py`; neither SciPy nor a search is needed. `--plan PATH` selects an explicit
plan, checked by the same replay implementation. `--no-plan` retains the previous
greedy schema-pruning route. Other certificate inputs keep that generic route by
default. Copied-input [reproduction controls](reproduction/result.json) checked
all four modes: default and explicit plans and the generic 629-node certificate
reproduce the final source exactly; `--no-plan` reproduces the 674-node source.

The [generator delta](generator.diff), [earlier generator](history/generator.674.py)
and [compressed earlier proof](history/DomRho8.674.lean.gz) preserve the accepted
checkpoint. The earlier generic-interpreter timeouts remain in the phase1 packet;
none is an accepted proof. See [summary.json](summary.json) for exact pins.

The [independent hook review](hook-peer.json) confirms that plan selection is
limited to the documented modes and the proof-emitter suffix is unchanged.
The reviewer did not rerun the generator or compiler.
