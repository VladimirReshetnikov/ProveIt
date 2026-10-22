# Exact residual coverage for the maintained K215 source

Base: `VladimirReshetnikov/ProveIt` commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.

**Checked with Lean 4.32.0: all 4,751 leaves and 6,176 guarded outcomes.**
All 51 pinned component modules passed in the isolated overlay during this
task, across resumed compiler invocations. This is not a fresh complete
ZFC-endpoint build. See `evidence/validation-receipt.json` and the named
axiom audits in `evidence/accepted-logs/BusyBeaver.ZFC.KResidualSites215.log`.

## What this adds

The repository already proves that the complete consumed word reaches an exact
primitive port, uniformly over every gap and register list. Its prior
`proof-contracts` proposal already makes the register simulator consume semantic
edge contracts, and composes a shared prefix with a positive suffix. Its concrete
example discharges only word `000`, with two decrement outcomes.

This component connects those existing pieces to all literal source leaves.
`KResidualRouting215.followRoles` deterministically follows the full prefix in the
certified role graph. `followRoles_of_path` proves that it returns the role in
every `RolePath` proof. `checkLeafSuffix_of_routed` identifies the computed
primitive port with every accepted `RoutedEntry` for the consumed word.

Thus `checkedLeafSuffixes_of_allSites` converts the finite equation

```lean
allSites (checkLeafSuffix tm215) [] KSource215.t215 = true
```

into the prior proposal's universal `CheckedLeafSuffixes`. It leaves no new
port-compatibility hypothesis to the endpoint caller. The nine original batch names
retain the maintained 105-subtree partition. Six larger batches each import two
six-block halves to bound compiler memory; no equation changes in that split. Both decrement branches remain;
no leaves, branch outcomes, register values or gap values are sampled or dropped.

The finite checker preserves the complete word at the port. The original
`KHomeReady.exec` begins with progress flag `false`, so every nonhalting residual
supplies `Reach1`. Prefix duration may be zero. No physical-state-only merging,
first-window-restoration assumption, or first-dispatch stopping rule is added.

## Exact statements

`checked_leaf_suffixes` discharges every residual premise for the literal source.
`counts` computes 4,751 leaves and 6,176 guarded outcomes directly from the
maintained source tree. `covered` supplies closed semantic coverage, specializing the existing
register-engine theorem to the literal table.

`source_halts_iff` proves

```lean
RegisterPath.Halts KSource215.p215 c ↔ KZip.Halts tm215 T
```

for every related pair `KSim.Rel KSource215.p215 c T`. The existing register
engine theorem and literal terminal rows discharge the other premises. It reuses the prior generic simulator and
introduces no new source-run or target-run induction.

This is a runtime-component result. It does not freshly rebuild the complete
ZFC endpoint. To integrate, expose a semantic-coverage version of the generic
`KEndpoint` composition and retain the old Boolean wrapper, or directly compose
this source/table equivalence with the existing dense-table, boot,
source-calculus and ZFC bridges. Semantic coverage does not itself assert that
the old whole-site fuel-limited evaluator returned `true`.

## Reproduce

Use Lean 4.32.0, a local checkout containing the pinned sources, and a fresh
output directory outside that checkout:

```sh
python3 build.py --repo /path/to/ProveIt --lean /path/to/lean \
  --out /path/to/new-residual-build
```

The script validates every input against `source-pins.json`, assembles an
isolated source tree, compiles 51 modules serially, with one Lean worker and a 3 GiB process limit, sets `maxRecDepth=65536` and `maxHeartbeats=8000000`, rejects unexpected named
axioms, and records source/log/object hashes. It makes no network requests and
changes no repository files. On Linux/WSL, a file lock serializes compiler calls.

The package contains 24 new residual modules. The 27 prerequisite sources
are read from the checkout: current maintained modules except `KSim`,
`KSimPrefix`, and `KDecoderSuffix215`, which are the existing
`proof-contracts/lean/src` proposal's versions. Their exact origins and hashes
are recorded. No precompiled project objects are distributed or required.

## Costs and remaining work

This stage makes a previously conditional runtime interface complete. It is not
an immediate source-size reduction: the semantic interface and routing adapter
add code, and the partition itself is intentionally unchanged. It removes
repeated decoder execution from each certificate. The earlier
`sharing-interfaces` numerical replay reports 220,471 avoided symbolic steps out
of 926,351; that is not a physical TM-step count or a measured build-time gain.
Fresh logs record component compile times only, excluding lock waiting.

The next source-size reduction is to replace repeated residual checks by
parametric primitive/return lemmas over accepted full `RolePath` prefixes, with
any marker/carry invariants proved from the source-role graph. The 97 short leaf
contexts reported in earlier work cannot be treated as universal contracts
without those continuation hypotheses.

## Attribution

The universal decoder prefix, source binding, symbolic executor, Home return,
register engine, source partition, and semantic simulator/positive-suffix
interfaces are prior repository work. Original module headers retain attribution
to the repository, Elliot Glazer's K230 development and Jeff Ketchersid's m254
development. The new files implement the deterministic role selector, its formal
attachment to `RoutedEntry`, full residual certificate instantiation and the
resulting all-leaf theorem. No new Turing machine is claimed.
