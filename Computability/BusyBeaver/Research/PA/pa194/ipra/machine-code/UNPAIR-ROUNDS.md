# PA194 source-controller decoder rounds

The five source files `PA194UnpairRound.lean`, `PA194UnpairDrainLoop.lean`, `PA194UnpairDrainInvariant.lean`, `PA194UnpairDrainModel.lean`, and `PA194UnpairDrainComplete.lean` describe the **actual pinned PA194 source controller**, with literal instructions at sites 34–41 checked against the generated source tree. The tail and all unrelated logical registers are arbitrary.

* `positiveRound`: if reg8 = w+1 and reg6 = a+1, sites 34→35→36→37→41→34 consume exactly 5 controller steps. Reg8 and reg6 each decrement, reg7 increments, and the two sums reg8+reg7 and reg6+reg7 are preserved. This uses PRA model assumptions.
* `drainLoop` and `drainExit`: site 38 consumes one reg7 item in 3 steps, incrementing reg6, or exits to site 34 in 2 steps when reg7 is zero. `runDrain` extends that loop to arbitrary model-valued lengths j ≤ initial reg7 by an explicitly Σ₁-definable induction invariant; it additionally assumes IΣ₁.
* `zeroXRound`: if reg8 = w+1 and reg6 = 0, the actual run returns to site 34 after 3 + (3·(old reg7+1) + 2) steps. It leaves reg8=w, reg6=old reg7+1, reg7=0, all other registers and the tail unchanged. This uses PRA + IΣ₁ model assumptions.

These are model-theoretic Lean theorems, not native iPRA theorems. They do not cover the reg8=0 exit, prove termination of the whole decoder, identify its output with the scheduler's unpair operation, establish full scheduler/controller synchronization, or prove any consistency implication. The original scratch Lean checks used mixed PA194 overlays and hence are preliminary from a source-closure provenance standpoint.

The intended independent replay uses the completed, isolated 270-module fetch source rebuild documented in `SCHEDULER-FETCH-MODEL.md`; after that audit has completed successfully, run from the repository root:

```sh
/dev/shm/pa194-scheduler-controller/check-unpair-after-fetch.sh "$PWD" /dev/shm/pa194-scheduler-controller /dev/shm/pa194-fetch-coherent-full-v2 /tmp/pa194-fetch-coherent-full-v2.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-unpair-coherent-replay
```

The script requires a fresh output, verifies the completed fetch log, 270 source hashes and object presence, the five new source hashes, and the six curated graph object hashes and namespace symlinks. It compiles these five modules in order against the common source-built machine output and checks the axiom reports for `sorryAx`. It inherits the baseline's limits: the six graph objects and the general project/package/Lake foundations are prebuilt, and source and output checksums do not independently establish their provenance or recheck the kernel of compiled baseline objects. The 270-module closure rebuild and this suffix replay both completed with exit status 0; their logs and output remain available for inspection.

The prerequisite v2 270-module fetch rebuild completed with exit status 0; the unpair suffix replay subsequently completed with exit status 0, with log `/tmp/pa194-unpair-coherent-replay.log` and output `/dev/shm/pa194-unpair-coherent-replay`.

The repository-source suffix replay also passed against that independently
built baseline, with the same retained graph and foundation limitations.
