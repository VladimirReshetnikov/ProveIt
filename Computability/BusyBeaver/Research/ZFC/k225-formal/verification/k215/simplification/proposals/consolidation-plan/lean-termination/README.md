# Clock-free termination transport for the existing K215 proof

This is a checked, optional refactor against ProveIt commit
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`. It changes the proof of
`KSim.halts_iff`, preserving its exact theorem statement and every machine,
decoder, invariant, source program, and calculus definition.

## What was checked

Lean 4.32.0 checked the standalone generic library, exact KZip/RegisterPath
adapters, two counterexamples to weakening the hypotheses, and the actual
patched KSim module. The replay built all 13 original runtime modules, then
reused their 12 unchanged dependency objects to build the patched KSim.
`evidence/replay.json` records every source hash, exit code, complete compiler
output, and observed duration. The full K215 endpoint was not rebuilt in this
sub-experiment. These checks do not by themselves establish a new ZFC
calibration theorem.

The generic theorems `Halts.suffix_induction`, `reflects`, and `halts_iff`
report **no axioms**. Both the original and patched `KSim.halts_iff` report
the same existing Lean assumptions:

```
[propext, Classical.choice, Quot.sound]
```

The original and patched `KSim.sim_step` have that same list. There are no
`sorry`, `admit`, or added axiom declarations in the supplied proof sources.

## The mathematical interface

Let `f : A → Option A` and `g : B → Option B` be deterministic partial
transition functions, and let `R : A → B → Prop`. Write `a →* a'` for a
finite run, `a →+ a'` for a nonempty finite run, and `Halts f a` for reaching
a state where `f` returns `none`. Require:

1. If `R a b` and `f a = some a'`, there is a `b'` such that `b →+ b'` and
   `R a' b'`.
2. If `R a b` and `f a = none`, then `Halts g b`.

Then `R a b` implies `Halts f a ↔ Halts g b`. The first condition alone
reflects termination from the target to the source. The second supplies
preservation from the source to the target; source terminals may take a
finite target drain before halting.

The relation need not be functional or injective, and it need not describe
interior target configurations. There is no fixed bound on macro lengths,
no global sequence of chosen macros, and no reverse simulation obligation.

The reusable induction rule says: to prove `P a` for a terminating state,
prove it for stopped states and prove it at `a` from `f a = some b` and
`∀ c, b →* c → P c`. Its proof strengthens ordinary finite-run induction
to all reachable suffixes. Determinism aligns the first successor in two
runs. This removes the arithmetic comparison and subtraction of halting
times from the client argument.

## Exact safety boundaries

Strict progress is essential. `ProgressCounterexamples.zero_step_simulation`
checks an infinite one-state source loop and an immediately halted target
that satisfy the weakened zero-or-more-step condition. The claimed
equivalence is false. `missing_terminal_drain` checks the converse failure:
a stopped source and an infinite target satisfy all transition obligations
vacuously, but preservation fails without the second premise.

Target determinism is essential to this interface. For a nondeterministic
target, a related infinite loop could coexist with a separate branch to a
halt. A forward existential simulation could select the loop while the
target still has a halting execution.

`RegisterPath.step = none` can denote decoder-fuel exhaustion as well as a
literal halt instruction. Consequently the adapter retains the explicit
premise `step p c = none → AtHalt p c`. In the actual KSim replacement,
the existing `sim_stop hcov` supplies it. It is not silently assumed.

For an absorbing, totalized target semantics, a positive number of steps
may occur after a halted state. Such a semantics cannot be inserted into
this partial-function interface without an adapter that removes outgoing
steps at halt. The existing `RuntimePerm252` and `PositiveBlockBisimulation`
proofs treat this case explicitly; their hypotheses must remain when those
clients are refactored.

The arithmetic-model theorem in `ArithmeticPositiveSimulation254` is not
an immediate client. It proves a statement inside arbitrary arithmetic
models using Sigma-1 definability and induction. Replacing that with
external Lean induction would lose its intended strength.

## What gets shorter, and what does not

| Measure | Original | Proposed |
| --- | ---: | ---: |
| Entire KSim source, raw lines | 354 | 326 |
| `KSim.halts_iff`, declaration plus proof, raw lines | 35 | 6 |
| New generic termination library, raw lines | 0 | 144 |
| New exact K-family adapters, raw lines | 0 | 72 |
| KSim plus new production modules, raw lines | 354 | 542 |

The KSim client shrinks by 28 lines overall. **This isolated refactor adds
188 maintained source lines overall.** The counterexamples and replay
script are excluded from that production-source comparison. It should be
adopted for shared proof structure only if enough additional clients use
the interface, or if avoiding ad hoc clock arithmetic is worth the initial
library cost. No total size or build-speed saving is claimed.

`TerminationTransportK.halts_of_reach` is also a checked direct replacement
for the handwritten clock-subtraction proof of `KEndpoint.halts_of_reach`.
That optional KEndpoint edit is not part of `KSim.patch`, and the KEndpoint
closure was not rebuilt here. Other proposed clients require explicit
semantics adapters; no automatic line saving is attributed to them.

## Provenance and priority

Positive forward simulation is already present in ProveIt and was already
proposed as a KSim extraction in `simplification/proposals/proof-core`.
The reachable-suffix induction idea was proposed in
`simplification/proposals/further-interface/report.tex`. This contribution
implements that idea, connects it to the exact current partial-machine
interfaces, and checks a current KSim replacement. It does not claim a new
general simulation theorem.

This is a secondary architecture improvement. It should not displace a
refactor that removes an entire redundant semantic construction or large
duplicated certificate from the live endpoint.

## Replay and incorporation

Run:

```
python3 replay.py --repo /path/to/ProveIt --lean /path/to/lean-4.32.0/bin/lean --out /tmp/k215-transport-replay
```

The output directory must not already exist. The script verifies the
SHA-256 of every original module against `source-hashes.json` before
building. It makes no network requests and does not modify the repository.

For incorporation, add `TerminationTransport.lean` and
`TerminationTransportK.lean` from `lean/BusyBeaver/ZFC/` to the corresponding
repository directory, then apply `KSim.patch`. The full patched KSim is
also supplied for inspection. `ProgressCounterexamples.lean` is an optional
audit module. Rebuild the final endpoint and print its assumptions before
merging, since that complete integration gate is outside this experiment.
