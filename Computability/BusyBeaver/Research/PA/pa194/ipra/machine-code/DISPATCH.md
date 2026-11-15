# Source dispatch after scheduler fetch and Cantor decode

The independently replayed source suffix adds ten Lean modules to the sixteen-module fetch/decode suffix described in `SCHEDULER-DECODE.md`:

* `PA194Transfer42Loop.lean`, `PA194Transfer42Invariant.lean`, `PA194Transfer42Model.lean`, `PA194Transfer42Complete.lean` prove the actual site 42→45 source segment: it takes `3·initial reg7+1` source steps, adds reg7 to reg8, clears reg7, and preserves all other logical registers and the independent file tail. The model-length iteration assumes PRA + IΣ₁.
* `PA194Transfer45Loop.lean`, `PA194Transfer45Invariant.lean`, `PA194Transfer45Model.lean`, `PA194Transfer45Complete.lean` analogously prove site 45→48: it takes `3·initial reg6+1` source steps, adds reg6 to reg3, clears reg6, and preserves other registers and tail. The model-length iteration assumes PRA + IΣ₁.
* `PA194DispatchTransfers.lean`, `transferToDispatch`, composes these exact model-valued durations and both final register updates.
* `PA194DispatchTag.lean` kernel-checks the pinned site-48/49 source instructions and proves three PRA-model dispatches: reg3=0 goes to site 3661 in one step, reg3=1 to site 3554 in two steps, and reg3=c+2 to site 50 in two steps with reg3=c. Other register/file content is carried exactly as in those theorems.

The staged replay of all 26 source-suffix modules completed with exit 0, no `sorryAx`. It uses the common source-built 270-module controller/scheduler closure, and retains six documented prebuilt graph objects and general prebuilt project/package/Lake foundations. Exact provenance, graph hashes, and the preserved first failed audit are in `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md`. Log `/tmp/pa194-dispatch-replay.log`; output `/dev/shm/pa194-dispatch-replay`. `check-dispatch.sh` pins the ten new sources and invokes the nested earlier checkers; only its final `PASS: model-length source dispatch transfers` line certifies all 26 modules. Run from the repository root with a fresh final path:

```sh
Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-dispatch.sh "$PWD" /dev/shm/pa194-scheduler-controller Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code /dev/shm/pa194-fetch-coherent-full-v2 /tmp/pa194-fetch-coherent-full-v2.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-dispatch-replay
```

Two further source modules, `PA194SchedulerDispatch.lean` and `PA194SchedulerBranches.lean`, check in scratch and compose the actual site-25 fetch/decode with the site-48 transfer and the three dispatch tags, under scheduler-field matching and initial zero regs 3/6/7. Their independent and repository suffix replays both passed; see `SCHEDULER-BRANCHES.md`. These results are model-level under PRA + IΣ₁. They are a scheduler-iteration prefix, not native iPRA proofs, a complete scheduler-step correspondence, a global source/physical simulation, or a consistency direction.
