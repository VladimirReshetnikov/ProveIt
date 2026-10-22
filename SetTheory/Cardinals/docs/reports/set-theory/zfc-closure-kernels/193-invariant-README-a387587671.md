# Checked Lean proof simplifications at `57541fe0cfe3`

These proposals were developed against ProveIt commit
`57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`, using Lean 4.32.0. They do not
change any machine table, machine state count, dense-to-sparse relation, or
statement of `KDenseBridge.blank_iff` or `KSim.halts_iff`.

## Recommended small patch: keep the information needed by both directions

Apply `minimal.patch`. The complete proposed module and a separate typed
audit client are in `minimal/BusyBeaver/ZFC/`.

| Measured source | Baseline | Proposed | Reduction |
| --- | ---: | ---: | ---: |
| Entire `KDenseBridge.lean`, lines | 193 | 170 | 23 |
| Entire `KDenseBridge.lean`, UTF-8 bytes | 8,127 | 7,323 | 804 |
| `blank_iff` declaration plus proof, lines | 52 | 29 | 23 |
| `blank_iff` declaration plus proof, UTF-8 bytes | 2,230 | 1,426 | 804 |

There are no new imports or production utility modules in this patch. The
whole-file reduction includes the explanatory comments in the new proof.
The audit client is a separate verification artifact and is not needed by
the production proof. The theorem signature is byte-for-byte unchanged.

### Mathematical change

Write `d_t = D.run t` and `z_0 = zc (ex 0) [] []`. The original forward proof
already maintained a useful disjunction: either the sparse machine had
halted, or the runs were synchronized at time `t`. Its stopped branch
discarded the evidence that the dense machine had halted. The reverse
direction therefore constructed another synchronized-run induction.

Keep both pieces of information in the stopped branch:

```text
I(t) := (BlankHalts D AND Halts M z_0)
        OR exists z, run M t z_0 = some z AND Rel (D.run t) z.
```

The base case is the existing blank-tape relation. In the inductive step,
if the dense configuration has halted, the synchronized branch supplies a
dense halting witness and `rel_halt` supplies the sparse one. If the dense
configuration is still running, the existing `rel_step` advances both
configurations and preserves the relation.

For a dense halting witness at time `t`, `I(t)` immediately yields sparse
halting. For a sparse halting witness at time `k`, inspect `I(k+1)`. Its
stopped branch immediately yields dense halting. Its synchronized branch
would assert a successful sparse run of length `k+1`, contradicting the
known stop at `k`. This deletes the entire second induction. No inverse
state map or injectivity argument is introduced.

This is a concrete simplification of the reviewed source, not a claim of
priority for the general invariant-strengthening technique.

### Verification

The baseline module, proposed module, and the identical typed audit client
were compiled separately against the original `Core.lean` and `KZip.lean`.
The baseline and proposed audit outputs are byte-for-byte identical. They
check `Commutes`, `Rel`, `rel_step`, `rel_halt`, `run_succ`, the exact public
`blank_iff` type, and a nonhalting client. Both public endpoint facts report
exactly `[propext, Quot.sound]`; there is no `sorryAx`. The final proposed
module compiles without warnings.

The change is proved against the actual repository definitions, not against
a simplified model. A full `KEndpoint215` rebuild was not performed in this
experiment. The preserved public type and direct-dependency compilation are
the verified scope.

## Optional shared infrastructure: finite terminal drains

`terminal-drain.patch` is a separate, larger consolidation proposal. It
contains an alternative implementation of `KDenseBridge.blank_iff`; do not
apply both patches to that file. It also replaces the local proof of
`KSim.halts_iff`, with its exact public signature preserved.

The key generic contract for partial transition functions `f` and `g` and
a relation `R` has two obligations:

1. A source step from related states is implemented by a **positive** finite
   target run ending at related states.
2. If the source stops at a related state, the target has a finite halting
   run. It need not already be terminal at that instant.

This implies equivalence of halting. The second obligation is weaker than
immediate terminal agreement and therefore fits the K-family interpreter's
finite epilogue after a source halt leaf. Reflection uses only the first
obligation. The proof consumes the positive target prefix from a target
halting witness, leaving a strictly shorter witness.

This proposal adapts the repository's existing checked
`k215-transport/formal/PositiveStutter.lean` prototype. The finite-drain idea
also appears in its uncompiled `further-simplifications/terminal_contract`
packet. The new contribution here is checked adaptation plus integration
with the actual current `KDenseBridge` and `KSim` definitions. It should not
be represented as a new discovery of positive simulation.

`RegisterPartial.halts_iff` keeps an essential premise: every stuck source
configuration must be a literal halt leaf. Its application in `KSim` uses
the existing `sim_stop hcov` theorem. A failed decoder does not become a
valid source halt merely because `step` returns `none`.

`TerminalDrainExamples.lean` checks three boundary cases:

- A stopped source can correspond to a target that still needs two steps
  to halt; immediate terminal agreement is false, finite draining works.
- Zero target steps can falsely match a looping source with an already
  stopped target. Positivity cannot be removed from reflection.
- A malformed source decoder is stuck but never reaches a literal halt
  leaf. The source coverage premise cannot be removed.

### Honest cost accounting

The alternative reduces the two existing client modules from 549 to 502
lines, and from 24,273 to 22,446 bytes. The three new production utility and
adapter modules add 219 lines and 8,543 bytes. Thus these two clients alone
produce a **net increase of 172 lines and 6,716 bytes**. Audit/example files
are excluded from those production counts. This is checked shared
infrastructure, not yet a net source-compression result. The small invariant
patch above is the immediate source-saving recommendation.

All three generic modules, actual `KDenseBridge` and `KSim` integrations,
and boundary examples compile. The generic theorem and dense bridge use
`[propext, Quot.sound]`; the KSim result retains the usual
`[propext, Classical.choice, Quot.sound]` set. No full endpoint or heavy site
certificate rebuild is claimed.

## Reproduce

The script compiles a fresh, isolated import closure using only the original
project modules needed by these targets and the distributed Lean runtime.
It checks original dependency hashes, records every source/object/log hash,
and stops on compiler errors, proposed-module warnings, or `sorryAx`. It records
inherited warnings in unchanged dependencies; the baseline `KZip.lean` has an
unused `simp` argument warning under this compiler. It does not use Lake,
network access, or previously cached project objects, and does not edit the
repository. Pass absolute paths or ordinary local paths:

```bash
python3 build.py --repo /path/to/ProveIt --lean /path/to/lean-4.32.0/bin/lean \
  --variant minimal --out /tmp/k215-minimal-check

python3 build.py --repo /path/to/ProveIt --lean /path/to/lean-4.32.0/bin/lean \
  --variant terminal-drain --out /tmp/k215-terminal-check
```

Use a checkout of the pinned commit, or a checkout retaining exactly the
recorded dependency source bytes. The JSON receipts and logs describe the
local checks actually completed; their exact paths are incidental. The
published sources and script are the reusable deliverables. Binary compiler
objects are intentionally not included.
