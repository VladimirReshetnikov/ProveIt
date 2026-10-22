# Independent review of the K215 residual site proof

This review concerns the sources under `lean_work/src/BusyBeaver/ZFC` and the
pinned ProveIt baseline `57541fe0cfe3af62b4cb58747d8d1d7c16b338d5`.
`residual_review.json` records the current source/object/log status. The
reviewer does not rerun the expensive site compilations. It independently
checks the mathematical interface, literal program expansion, partition
preservation, and the hashes of the implementing agent's compiler artifacts.

## Conclusion

No logical defect was found in the residual-prefix composition or semantic
simulation adapter. The result retains the complete consumed path, exact
physical table, both decrement guards, full tape parameters, positive physical
progress, and both directions of the original simulation. Complete finite
coverage is established only when the nine batch proofs, the root facade, and
the explicit audit client all compile successfully with matching source
hashes. See the adjacent JSON for that execution status rather than inferring
it from the existence of source files.

**Final execution review: passed.** All 34 project modules and the explicit
audit client have successful current receipts. The independent review checked
every source, `.olean` object, and log against those receipts; no stale or
missing binding remains. All nine finite batches, their final composition,
and the audit tying 4,751 leaves and 6,176 guards to the literal tree passed.
All four expected audit reports are present, and the complete named axiom
union is exactly `propext`, `Classical.choice`, and `Quot.sound`. These are
the fresh runtime checks, not a fresh whole-endpoint build.

## Exact contract chain

For a decoded source path `P`, let the source walk consume `d` bits, producing
`Q = consume P d`. The maintained `walk_prefix` theorem establishes a single
source-determined decomposition `Q = pre ++ [bit]` and entry state `q`. For
every gap parameter `n` and register list `vs`, the real sparse K215 table
reaches the exact configuration

```lean
conc n vs (leafPort pre bit q)
```

from `conc n vs (start Q)`. The entire prefix is retained as
`pre.reverse ++ [true]` to the left of the head. The right side contains the
primitive-read bit, `n + (D0 - (pre.length + 1))` blanks, the header marker, and
the whole register representation. This is a complete concrete tape
configuration, not merely agreement of control states or a local window.

`KResidual215.Prefix` expresses that concrete reachability uniformly in `n`
and `vs`. Its proof uses the maintained theorem exactly at `consume P d`,
including implicit zero padding of the source path. It never substitutes an
unconsumed suffix or forgets the original register payload.

The finite `followRoles` function walks certified *role indices* along every
bit of `pre`. It rejects absent roles and premature primitive exits. The
theorem `followRoles_of_path` follows the inductive certified role path, and
`portState_of_entry` identifies its computed final physical state with the
state supplied by `RoutedEntry`. This is significant because different roles
can share a physical state; physical state alone would be an insufficient
decoder identity. `residualTest` also rejects the empty instruction word.

At that exact port, `runFrom` uses the existing certified executor with
progress initialized to **false**. `runFrom_sound` therefore returns
`Reach1`, not merely reflexive reachability. The prefix is allowed to have zero
steps, but composing it with the positive suffix still gives `Reach1` for
every nonhalting source edge. This is precisely the progress required by the
reverse simulation's induction on the number of physical steps.

`checkFrom` keeps the complete old `Q` in every target. It retains the path
length bound, the register index bound, all overflow/gap arithmetic, and all
exact register effects from `KSim.checkEdge`. In particular:

- Increment reaches the successor path and increments the correct physical
  register.
- Decrement has both the zero guard and the nonzero guard. The zero branch
  breaks one level without decrementing; the positive branch decrements and
  proceeds to the successor path.
- Break and continue use the same `breakPath`, `stripPath`, `continuePath`,
  and overflow expressions as before.
- Halting composes prefix reachability with `haltFrom_sound`, retaining the
  explicit premise that state 230 has no outgoing transition.
- A `.node` edge is false, and a failed tree branch is false in `allSites`.
  Neither can be silently treated as an intended source halt.

The soundness theorem `checkFrom_contract` is abstract in the table. Its K215
application uses `KTableCore.tm215`. Computational batches may evaluate the
fast lookup table, but `allSites_of_fast` transports them along the proved
functional equality `KBoot215.fast215`; it does not substitute another
transition system.

## The semantic simulator

The proposed `KSim` is the existing semantic-coverage refactor, with current
SHA-256
`d5b5f502c3ea0529d9c2aaf26a33d13d65e9f91a6da2cb4b3c774a9c2ac5dcd7`.
Its prior-art origin should be credited separately from the new residual
checker.

`SemanticCovered` requires every actual source walk to reach a leaf with an
`EdgeContract`. That contract retains all premises formerly extracted from a
successful Boolean check. The simulator's concrete `Rel` is unchanged. Its
forward simulation uses the positive realization; its reverse direction
strictly decreases the remaining physical run length. The original public
Boolean `sim_step`, `sim_stop`, `sim_halt`, and `halts_iff` declarations remain
available as compatibility wrappers. In particular, the old `sim_stop` still
does not require `BoxLemmas`.

`covered_of_residual` supplies semantic coverage through the exact original
literal tree and `t215_eq`. It uses `allSites_walk_total` and `allSites_walk`,
which recover the actual consumed word. There is no undisclosed
`PrimitiveContracts` premise and no coverage predicate assumed globally.
`BoxLemmas tm215`, terminal-state behavior, and the original concrete
representation relation remain ordinary explicit premises of the generic
simulation theorem.

The resulting theorem is

```lean
RegisterPath.Halts KSource215.p215 c ↔ KZip.Halts tm215 T
```

for every pair related by the existing `KSim.Rel`. This is a complete runtime
simulation statement once the site proofs compile. It is not, by itself, a
fresh compilation of the full `BlankHalts machine215 ↔ ZFC-refutation`
endpoint. Boot, dense relabeling, source-to-enumerator equivalence, and logical
calibration still compose through their existing interfaces.

## Independent finite census and exact coverage

The audit script parses the literal `p215Nodes` definition as data, beginning
at its stated root 178, with 179 nodes. It expands the finite tree and finds:

| Operation | Leaves | Guarded outcomes |
|---|---:|---:|
| Increment | 1,900 | 1,900 |
| Conditional decrement | 1,425 | 2,850 |
| Continue | 1,327 | 1,327 |
| Break | 98 | 98 |
| Halt | 1 | 1 |
| **Total** | **4,751** | **6,176** |

The expanded words, operations, and arguments agree entry-for-entry with
`candidate-k215/sites215.json`. All 105 original subtree-block theorem targets
are preserved exactly except for changing `KSim.checkEdge` to
`KResidual215.residualTest`. The entire root-join proof is preserved under the
same substitution, and all 105 block proofs use `decide +kernel`. Thus the
proposal does not prune any leaves or drop either decrement outcome. The
implementing agent's `concrete_counts` theorem additionally ties the leaf and
guard counts directly to `KSource215.t215` inside Lean.

The source-only census establishes intended coverage. Successful current
kernel compilation of all the batches and root facade is what establishes
that every one of those residual checks actually succeeds. The adjacent JSON
checks source, `.olean`, and log SHA-256 values against the corresponding
receipts. Failed early drafts remain separate from the accepted sources.

The independent import traversal finds a focused closure of 34 project
modules plus one explicit audit client, rooted at `KResidualAudit`; its only
external import root is `Init`. All 22 unchanged providers match the maintained
source bytes exactly. The replacement `KSim` matches the archived
semantic-coverage proposal exactly. The hash checks range over this complete
focused closure, including providers, rather than just the nine site batches.
This count describes the runtime experiment and must not be confused with the
179-module production endpoint closure.

The same source/receipt audit can be rerun on the portable runtime packet:

```sh
python3 audit_residual.py --repo /path/to/pinned/ProveIt \
  --packet /path/to/residual_sites --output /tmp/residual-packet-review.json \
  --require-complete
```

Packet mode verifies saved source/log bindings and coverage but explicitly
does **not** inspect compiled object bytes or invoke Lean. Its status is
`PASS_SAVED_SOURCE_LOG_BINDINGS_NO_OBJECT_REPLAY`; the corresponding actual
packet inspection is saved in `residual_packet_review.json`. The stronger
original-workspace check uses `--work` instead of `--packet`, requires the
current objects, and is recorded in `residual_review.json`. The supplied
runtime `replay.py` is the separate fresh proof-compilation entry point.

## Savings and limitations

This runtime refactor makes a repeated decoder prefix into a reusable semantic
proof. It does **not** reduce the number of guarded residual executions:
all 6,176 remain. Family-level primitive suffix proofs would be a further
improvement. It also does not yet reduce total proof-source mass. The nine
batches grow from 55,794 to 57,285 bytes because the replacement qualified
names and provenance comments are longer; the generic semantic interface and
the residual soundness module add source as well.

Counting `KSim`, the nine site batches, and their facade on both sides, plus
the new `KResidual215` module on the candidate side, gives 86,896 to 103,551
bytes and 1,321 to 1,651 lines: an increase of 16,655 bytes and 330 lines.
These totals include every changed production source in that runtime group;
they exclude unchanged imported providers and the explicit audit client.
They are not a comparison of complete endpoint closures.

Measure completed compiler time separately from lock waiting, and compare
against a same-toolchain, same-environment baseline before claiming a speedup.
A historical phase-nine time is useful context but is not a controlled
benchmark for this new run. Report any implementation timeout or rejected
batch rather than inferring all-site success from the generic soundness
theorem.

Integration should keep the original endpoint statement and separately check
its standard-axiom profile. Adding a new semantic theorem with explicit
runtime hypotheses does not itself discharge the full machine endpoint, and
a fresh module's axiom list is not a substitute for the endpoint's list.

## Source review of the separate endpoint proposal

The separate `integration/endpoint-UNCHECKED.patch` adds
`KEndpointSemantic.lean` and changes the machine-specific endpoint to use
`KResidualSites215.covered tm215_box`. The new generic composition has the
same dense relabeling, terminal-state, boot reachability, representation, and
source-to-`C222` hypotheses as the maintained composition. It replaces the
Boolean coverage plus register-box inputs by `SemanticCovered`; the concrete
call discharges the necessary register-box hypothesis while establishing
that semantic coverage.

Its first equivalence rewrites dense blank halting to sparse blank halting,
rewrites the source calibration, and applies the new two-way simulation.
The remaining boot equivalence uses exactly the original deterministic
`KEndpoint.halts_of_reach` and `Halts.of_reach`. Its logical calibration then
reuses the maintained `C222`/ZF refutation equivalence and the maintained
ZF/ZFC refutation equivalence. Neither direction of the theorem is weakened.
The proposed types of both `blank_halts_iff_zfc_refutation` and
`nonhalting_iff_zfc_consistency` are textually equal to the maintained types
up to whitespace; the independent script checks this fact and records the
proposal hashes.

No mathematical or interface defect was found in this source review. The
adapter and the full endpoint have **not been compiled in this focused
experiment**. The patch is appropriately labeled `UNCHECKED`; the checked
runtime receipts do not turn it into an endpoint build. The next integration
gate is to compile these endpoint modules in the complete dependency closure
and recheck both endpoint axiom profiles.
