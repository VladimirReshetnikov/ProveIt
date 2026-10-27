# Uniform unrestricted rho8 circuit: independent review and replay

26 October 2026. Reviewer: `circuit_reduction`. Author: ROOT. Verdict: PASS,
with no source correction requested. I did not author the reviewed circuit,
its checks, the generic dominated-implication derivation, or the imported
Circuit/Rule/Leaf implementations. I previously supplied source-only
challenges of Leaf and Rule.

## Source and mathematical review

The complete new 111-line main and 33-line checks, complete author driver and
receipt, cache plan, and the relevant imported sources were read before the
independent replay. The earlier [source-only review](arithmetic-command-rho8-circuitperm222-source-review.md)
records the full read scope and detailed mathematical challenge. Its SHA256 is
`cb2cc3b6a9a7b0e3ff069550e6b9c8745f86f87d6f39734cb6d2ad8641569dbc`.
That historical note retains its no-compiler claim; this receipt records the
subsequent authorized compiler replay.

The source witness remains outside the model, instances, and input
quantifiers. `Contract` still covers every initial top and saved stack.
`Restricted.mp` takes its major first, while the actual circuit and
`mp_contract` correctly take the minor first. The actual MP suffix, including
its cleanup counter and saved-stack treatment, matches the imported Rule
definition. The two symbolic dominance constructors give exactly the real
numeric guard needed by direct leaf8. Applying the existing finite generic
derivation removes the outer dominance assumption without inventing an
unrestricted physical leaf. The final conversion to the actual
`ArithmeticTemplates254.rho8` is definitional and was accepted by the fresh
compiler.

This is an externally finite circuit existential, uniform over models in
each fixed universe parameter. Its existing graph interface is literal
five-slot Sigma1 syntax. It is not internal recursion on proof/circuit codes,
a represented proof-history compiler, a success-only contract, source-proof
interpretation, exact215 calibration, or a new HA endpoint.

## Exact source and fresh objects

Both source paths are under `Lean/DiophantineConsistency/`, relative to this
project directory.

| File | Source SHA256 | Fresh object SHA256 |
| --- | --- | --- |
| `ArithmeticCommandRho8CircuitPerm222.lean` | `580010fadd590c1cbbf67ef14615ebbcc468a8ee2e7edf55900a1f78af5a7c30` | `ed2baf3f73a4823870ee89378a083f79758cfebfba5ffb95f0233be2f52e707f` |
| `ArithmeticCommandRho8CircuitPerm222Checks.lean` | `2a46b5f47f2a7adf46be29ffcb8e7eebd0c3153231f05b1352d7fc53f06c8c3a` | `309be98d11ce52dc17245fbe13a0c52920b1fcbf2332d9a1e1a388157adebec5` |

The private overlay is
`/tmp/command-rho8-circuitperm222-independent-xskuw6l8/lib`.
Both new objects are regular, previously absent, nonsymlink outputs, and are
byte-identical to the author's corresponding objects. No shared object or
accepted source was overwritten.

## Authentication and execution scope

The frozen author summary
`arithmetic-command-rho8-circuitperm222-replay.json` has SHA256
`c5638a2feefa39717e881101060ea5e32b264b457aeda497e841db9db878742f`.
I authenticated its nine-member bundle, driver, input/result records, source
snapshots, logs, timings, and object hashes. Independently parsing current
source import headers recovered exactly 126 cached custom modules, including
95 Foundation modules, 411 recorded compiled artifacts, and 38 explicit
external package/toolchain boundaries. All cached modules are reachable;
none imports either fresh leaf. There were no import-metadata normalizations.
External module lookup was checked against the explicit ordered search paths.

All 697 unique inherited and explicit path/hash pins matched before and after
each fresh invocation. They include source bytes, recorded companions and
provider evidence, exact Lean/toolchain/package pins, and the author's frozen
evidence. These are authenticated cache reuses, not fresh recompilations of
the Foundation or other prerequisite closure. No dependency build occurred.

The independently adapted driver was fully read before execution. Both
invocations used pinned Lean4.32, `-M6000 -j1 -DElab.async=false`,
`LEAN_NUM_THREADS=1`, no `LEAN_SRC_PATH`, private outputs, and a checked
512MiB free-space reserve before each invocation. The main passed in 1.951s
and the checks in 1.576s. Maximum resident sizes from the two individual time
records were 1,826,612KiB and 1,811,244KiB. The main log is empty; neither
invocation reported a warning or error.

All five reports (`below_eval`, `eval_mpCircuit`, `uniform_restricted`,
`unrestricted_expr`, `exists_rho8_circuit`) contain only `propext`,
`Classical.choice`, and `Quot.sound`. There was one independent attempt,
which passed immediately. No failed compile or preflight correction is
omitted. The extra suggested checks in the source-only note were not added
or represented as executed checks.

## Durable evidence

[Independent summary](arithmetic-command-rho8-circuitperm222-peer-replay.json):
`9cdad5cc4d86c08a171fdfff5b74bbd85e87d0b665037ca23e3f6c5ed2fc22d2`.

[Complete 15-file manifest](arithmetic-command-rho8-circuitperm222-peer-replay/FILES.json):
`228480ac6bc2112e865c4705f179fed79fd56e65216ae16c2a62c48c021e1db9`.

The bundle retains the full independent driver and input pins, copied author
evidence, exact fresh source snapshots, commands, logs, individual timing
records, object comparisons, axiom reports, and terminal result. No Git,
proof-source, or shared-document changes were made as part of this review.
