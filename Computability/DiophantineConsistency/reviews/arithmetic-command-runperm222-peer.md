# Independent review of C222 command-word iteration and draining

26 October 2026. **PASS; no source correction requested.** The reviewer,
`circuit_reduction`, did not author this main/check pair. The reviewer authored
the parser/command-step prerequisites and independently reviewed the separate
root-authored tick packet. Those roles do not make this a second independent
derivation of every prerequisite.

The review read all 191 main and 39 check lines, the complete author receipt,
driver, input/run records and nine-file manifest, the complete current
Foundation PRF source, and the complete literal TickPerm222 source. The
selected import graph was independently traversed from source headers. It
contains no CommandTick254 or CommandRun254 module. The historical generic
proof structure does not supply an imported old-validator execution theorem.

The PR blueprint has one fixed parameter, the complete initial evaluator;
its successor actually calls the new tick. The two argument positions of
`runDef` are time and initial evaluator. The derived graph and its delta
companion bind this exact PR result, including zero and successor equations.
The stopped-state and semigroup proofs use definable induction on an internal
model element, not external induction over standard natural times.

In `drain_bound`, word and working state remain fixed. The induction predicate
is the disjunction of stopped status and
`remaining(run time (liveValue word w)) + time ≤ word`. The actual tick
strict-decrease lemma gives the successor inequality; no induction hypothesis
universally quantifies over arbitrary changing working states. At time equal
to the word code, order cancellation forces remaining zero in the surviving
case. This covers empty and nonstandard word codes under the stated IΣ1 model
hypotheses. No size bound on the changing working state is inferred.

The terminal evaluator preserves the distinction between halt zero and
positive completed configurations. The evaluation result is zero exactly
when the terminal configuration is zero; an empty word instead returns
`w+1`. Totality/uniqueness use the exact represented graphs. The final closed
IΣ1 proof-existence theorem uses the actual arithmetic completeness theorem;
weakening supplies the PA counterpart. These are classical arithmetic
totality proofs. They are not an HA derivation of a plain checker equivalence.

Fresh independent replay used a new private overlay
`/tmp/command-runperm222-independent-u581k8i6/lib`, pinned Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`, actual source paths and new nonsymlink outputs.
Both first compiler runs passed in 8.205 and 1.863 seconds. The main log is
empty; all 21 axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. Both fresh objects are byte-identical to the author's objects.
No preparation or compiler failures occurred in this independent replay.

The authenticated closure contains 117 current-source cached modules,
including 95 Foundation modules, 402 cached artifacts and 38 explicit
external boundaries. All 590 distinct pre/post pin observations matched.
The source-header traversal verifies exact closure coverage, explicit package
boundaries, and that no reused client imports either fresh leaf. Compiler,
toolchain, package manifest, source files, primary/available companion objects,
author snapshots/logs/timings and the full author bundle are pinned. This
reuses the previously authenticated dependency objects; it does not freshly
replay Foundation or external packages. The 512 MiB reserve was enforced.

Exact source pins:

- Main: `3721f3d6804d95ce3ec6779ffea567ce364d05bb16764224965eb26b174fc9ff`.
- Checks: `89575c318c80c59ca28b2cae58d6e6acbdb72a92017cc503be5ab6dd5ebed2a2`.
- Main object: `7f82947894f227b0d17c533a21297ad31c8000bc79b234cf4514ce07a687e01c`.
- Checks object: `be8f881baa703cf783678b112591d850f6310ae43e333f56d909d1a2115dfd69`.
- Author summary: `3d11b3ec1e09ff45d36f5a2c48f83ef0a46e6e2cd826372459b99fe03d519826`.
- [Independent summary](arithmetic-command-runperm222-peer-replay.json):
  `a01463b5be6fd3f4ad21f8e3aa0879638f2a9b33ce4cd7d8c926e5ded13e12ef`.
- [Twelve-file replay manifest](arithmetic-command-runperm222-peer-replay/FILES.json):
  `42585ea602f88599d8f054e11e2ae3a4ab0435c7c73b136018f13dbb08f43745`.
- Result: `6c35a907fbb2583ad861543b7cc7c6d3fb39d0c218ffd138ff992f34cce2bdea`.
- Inputs: `0ef186f08602db5e1a9655475e9ce46877972d1afebe3800cb078203f125e5bb`.
- Independent driver: `f23c682c3ed924225a9cb7a38f20611cc7faf645b4199bc4217174c366f0f910`.

Scope remains the exact internal PR iterator, drain bound and represented
total evaluator. Execution composition, scheduler fairness, compiled proof
blocks, proof invariants, exact215 simulation, checker normalization and the
desired HA equation equivalence remain separate obligations. No frozen
source, shared documentation, dependency output or equation artifact changed.
