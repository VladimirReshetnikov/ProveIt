# Exact 244/245 halting equivalence in Lean

The literal compensated244 machine now has a checked halting equivalence
with Routing245. [Compensated244Simulation](../../Lean/BusyBeaver/ZFC/Compensated244Simulation.lean)
proves `start_halts_iff` for every head and finite-support tape at shared
old start95, and `blank_halts_iff` / `blank_nonhalts_iff` for the actual
state-zero, head-zero, empty-tape runs. The equivalences are oriented
Routing245 to Compensated244. No clock bound or interpreter-frame premise
remains in these statements.

The relation equates the full configurations after embedding the244 control
state, preserves the [original-machine local invariant](compensated244_foundations.md),
and excludes old92 at comparison endpoints. The embedding already omits
old122. All482 ordinary rows advance both machines one step. The seven
exceptional contexts use independently checked finite blocks:

| Entry and local bits | Old/new steps | Endpoint |
| --- | --- | --- |
| 104/read1, next0 | 2/4 | old25, head+2 |
| 104/read1, next1 | 2/2 | old66, head+2 |
| 106/read1, next0 | 2/4 | old25, head+2 |
| 106/read1, next1 | 2/2 | old66, head+2 |
| 167/read1, left1 | 2/2 | old24, head−2 |
| 81/read1, left0 | 2/2 | old107, head−2 |
| 81/read1, left11 | 6/4 | old2, head−2 |

[Compensated244Blocks](../../Lean/BusyBeaver/ZFC/Compensated244Blocks.lean)
checks both the paired identities and seven explicit new endpoints. The last
case erases the current cell and its left neighbor in the same order on both
machines; the other cases leave the tape unchanged. All endpoints retain exact
`Core` tape-list equality, including arbitrary exterior finite support and
arbitrary list representations. These are not finite test fixtures.
The submitted ordinary proof's arbitrary-function-tape claim is broader than
this formal tape type; blank tape is included in the formal result.

The local blocks pass14 named probes and14 typed callers in1.370/0.478seconds
for source/audit. The global composition passes4/4 in0.805/0.439seconds.
Both have zero warnings and only `propext` and `Quot.sound` in their axiom
reports. The exact [blocks record](results/compensated244-blocks-verification.json)
is `71b8b0096ead121f787f0f489cd5cc8988b7311ca52f3a602e3235f1a2c09b41`;
the [global record](results/compensated244-simulation-verification.json) is
`c5155b3f1e58812b2e91f8a7e66294fc0650adb3c170ff07923968d9e55783c7`.
Sources and audits are published unchanged from those runs.

The block guard selects three existing project providers. The global guard
joins three actual parent records into exactly seven project providers and
checks the exact import closure. Each source/audit pair runs serially with
`-j1 -M4096` and default proof limits under one120-second budget. Fresh objects
are captured before the audit; all input, object and first-provider identities
are checked afterwards. No dependency build, download or compiler-version
query is performed. Independent source and actual-evidence reviews, prior
unexecuted drafts and the exact guard-default changes are preserved under
[compensated244-formal](compensated244-formal/).

To reproduce against the exact existing providers, use new external directories:

```sh
python3 -B check_compensated244_blocks.py --prepare-only --output /tmp/c244-blocks-prepared
python3 -B check_compensated244_blocks.py --output /tmp/c244-blocks-actual
python3 -B check_compensated244_simulation.py --output /tmp/c244-simulation-actual
```

Historical cache paths and the pinned toolchain are required, as described in
the [foundation instructions](compensated244_foundations.md). Preparation
does not invoke Lean. The maintained guards change only path defaults.

The [final wrapper](compensated244_binary.md) composing this equivalence with
the closed [BinaryRouting245](routing245_binary.md) ZF/ZFC calibration now
passes its separate six-probe/six-caller check. These simulation theorems do not assert unconditional nonhalting
or an internal proof in PA. Attribution and the exact submitted table are
recorded on the [candidate page](candidate-compensated244/README.md).
