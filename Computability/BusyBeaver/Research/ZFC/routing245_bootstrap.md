# Exact routing245 blank startup

Lean now proves that the literal 245-state machine, started in state 0 with
head 0 on the all-zero tape, reaches its complete dispatch frame after
**407,915 transitions**. The proof retains the entire infinite tape and its
zero exterior. It also proves that the machine is active at every earlier
time in this prefix.

The final checkpoint in
[BootRouting245Chunk009](../../Lean/BusyBeaver/ZFC/BootRouting245Chunk009.lean)
satisfies

```lean
ZipRep (machineRouting245.run 407915) checkpoint407915
```

The checked
[BootstrapFrameRouting245](../../Lean/BusyBeaver/ZFC/BootstrapFrameRouting245.lean)
then identifies that exact checkpoint with the runtime representation:

```lean
Routing245Simulation.DispatchFrame64 dispatchRouting245
  (machineRouting245.run 407915) LogicalSeed246.initial 181 spares
```

Here `spares = List.replicate 167 1`. The state is 88, the head is at −5,
the marker is at −6 and the register header is at 176. The physical primary
registers are `[0,0,0,3,0,0,3,0,0]`, corresponding to the previously calibrated
logical seed `[3,0,0,0,3,0,0,0,0]`. The frame proof establishes the logical
zero tail and the nonempty spare suffix required by the runtime theorem.
All 351 one-cells are retained. The finite zipper stores a left list of
one true bit followed by nine false bits and a right list of 707 bits;
unlisted cells are zero.

Ten startup modules check 34 successive blocks. The first checks 1,024
steps, a single 16,384-step continuation measures the cost, and subsequent
modules contain at most four blocks of at most 16,384 steps each. Each
literal block equality is proved by `decide +kernel`; the generic zipper
soundness theorem composes it into the actual blank run. The checked fast
table is equal to the canonical machine, whose table hash is
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.
Generated checkpoint data supply the proposed literals; they are not proof
premises. No startup proof from the 246-state machine is reused.

The startup modules pass **72 named theorem probes and 102 typed callers**.
The frame adapter adds **8 probes and 9 callers**, for **80 / 111** total,
with zero warnings. Observed axiom reports contain only `propext` and
`Quot.sound`, or no axioms. The eleven source checks took 233.884 seconds
in total and their audits 4.766 seconds; the longest source check took
37.347 seconds. Every source/audit pair shares 120 seconds, one thread and
4,096 MiB, with default proof limits. The final startup module selects
13 existing project providers; the frame adapter selects 123. Init and
Omega are the explicit toolchain boundary. No dependency rebuild or
compiler-version query occurred.

The first attempt to generate the final 43 steps rejected an expected
left list containing ten trailing false bits. The actual finite zipper
has nine; both describe the same infinite tape. The corrected generator
changes only this expected padding, and the later Lean proof checks the
literal checkpoint and its exact equality with the runtime target. The
stopped coordinator, diagnostic, original templates and successor edits
are preserved. Earlier successful blocks were not rerun.

The [final startup record](results/routing245-bootstrap-verification.json)
and [frame record](results/routing245-bootstrap-frame-verification.json)
contain the actual compiler results. The
[publication manifest](results/routing245-bootstrap-publication.json) and
[history](routing245-bootstrap/history.json) preserve sources, audits,
generators, guards, preparations, logs and reviews. Scratch paths and object
hashes identify the actual runs; compiled caches are excluded from publication.

This discharges the initial-frame premise of the
[conditional runtime theorem](routing245_execution.md). Complete decoder
coverage and its composition into the closed binary consistency endpoint
remain separate. The internal PA equivalence also remains open. Attribution
follows the [candidate notice](candidate-routing245/README.md): Mira-Cult,
Jeff Ketchersid, Andrew James Wade, and the subsequent ProveIt reductions
and formalization.
