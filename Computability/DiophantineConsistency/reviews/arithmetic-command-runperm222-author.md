# C222 word iteration and draining: root author receipt

26 October 2026. Root authored the191-line main and39-line checks by
adapting the completely read generic PR/draining proof structure of
CommandRun254. Only the actual new CommandTickPerm222 and cached Foundation
PRF are imported. No old254 tick/run semantic theorem is used. This is an
author receipt; independent review is recorded separately when available.

The fixed PR graph iterates at every internal IΣ1 time from every initial
evaluator state. It supplies a Δ1 companion, unique output, zero/successor
laws and a semigroup law. Halted and successfully completed evaluators
remain absorbing at every internal time, with their scalar codes distinct.

The draining induction keeps the initial word and working state fixed.
Its definable predicate says either the current evaluator is stopped or
remaining(current)+time≤word. The only changing evaluator is the actual
represented run at that time; no unbounded universal induction hypothesis
over arbitrary working states is used. The strict tick decrease therefore
proves halt or completion by time=word for every internal word, including
nonstandard inputs. An empty word returns w+1 rather than halt0.

Terminal/evaluation graphs are total and unique. A literal closed arithmetic
sentence states evaluator totality; arithmetic completeness and weakening
give actual IΣ1 and PA proof-existence theorems. These are totality theorems,
not the desired consistency equivalence or an HA derivation of the plain
checker relation.

The complete new source/checks and adapted driver were read before running.
Both new leaves passed their first compiler invocations in8.163s and1.797s.
The main log is empty; twenty-one reports contain only propext,
Classical.choice and Quot.sound. No failed preparation or Lean run occurred.
Pinned Lean4.32.0 used `-M6000 -j1 -DElab.async=false`, actual source paths
and fresh nonsymlink outputs in
`/tmp/arithmetic-command-runperm222-root-author-gf9iylxf/lib`. The512MiB
reserve was enforced.

The preflight and postchecks authenticated117 cached current-source
modules, including95 Foundation modules,402 cached artifacts,38 explicit
external boundaries and564 pin observations. The tick provider was the
frozen author primary; its later independent peer rebuild has identical
bytes and was reauthenticated separately. No dependency or Foundation
source was compiled, and no shared output was overwritten.

Main source SHA:
`3721f3d6804d95ce3ec6779ffea567ce364d05bb16764224965eb26b174fc9ff`.
Checks: `89575c318c80c59ca28b2cae58d6e6acbdb72a92017cc503be5ab6dd5ebed2a2`.
Main object: `7f82947894f227b0d17c533a21297ad31c8000bc79b234cf4514ce07a687e01c`.
Checks object: `be8f881baa703cf783678b112591d850f6310ae43e333f56d909d1a2115dfd69`.
The [frozen summary](arithmetic-command-runperm222-replay.json) has SHA
`3d11b3ec1e09ff45d36f5a2c48f83ef0a46e6e2cd826372459b99fe03d519826`;
the [nine-file manifest](arithmetic-command-runperm222-replay/FILES.json)
has SHA `e7c2b13ec79edfe2730dcaed11d7112f7112350d165ba88ee3805850c9b4162a`.

Execution composition, scheduler fairness, compiled proof blocks, proof
invariants, exact215 simulation and the final HA equation equivalence
remain separate obligations. No maintained equation artifact changed.
