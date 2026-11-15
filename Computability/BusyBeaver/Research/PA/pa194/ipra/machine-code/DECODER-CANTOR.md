# PA194 decoder invariant and site-42 exit

These two source modules extend the five previously checked sources in `/dev/shm/pa194-scheduler-controller/UNPAIR-ROUNDS.md`:

* `PA194UnpairExit.lean`, SHA-256 `f0147c08af606feaea7c3da8b5142039dbae85dd44cc88a4ea47b80acb13dfbd`, proves `exitTo42`: in any PRA model the actual source-controller instruction at site 34 takes one step to site 42 when register 8 is zero, leaving all registers and the arbitrary file tail unchanged.
* `PA194UnpairCantor.lean`, SHA-256 `fe146ccc98edf4c035a6c500ab4543de4e4667c576cb0317d4dd26cce325e103`, uses the machine Cantor pairing `triangle(x+y)+y` and the exact controller round theorems. `positiveRoundInvariant` preserves `cantor(reg6,reg7)+reg8=seed` through the 5-step positive-reg6 round in PRA models. `zeroRoundInvariant` preserves it through the variable-time zero-reg6 round in PRA + IΣ₁ models. `exitIdentifies` proves in PRA models that, when reg8 is zero, the actual scheduler's `fixedFirst` and `fixedSecond` codes applied to the invariant seed return reg6 and reg7, and the controller exits to site 42.

These are model-theoretic Lean theorems; in particular the conditional site-42 identification neither proves that a model-length sequence of actual decoder rounds reaches the exit nor proves a native iPRA statement, global scheduler/controller simulation, or a consistency implication.

The independent staged replay completed with exit 0. It rebuilt all five decoder-round prerequisites and these two modules into a fresh output against the common source-built 270-module fetch/controller/scheduler closure. The graph namespace's six objects and the general project/package/Lake foundations remain prebuilt; see `/dev/shm/pa194-scheduler-controller/SCHEDULER-FETCH-MODEL.md` and `UNPAIR-ROUNDS.md` for exact source provenance, SHA-256 pins and the preserved first failed build. The checker validates final axiom reports and source hashes; no `sorryAx` occurs. Log: `/tmp/pa194-unpair-cantor-replay.log`; output: `/dev/shm/pa194-unpair-cantor-replay`.

From the repository root, with a fresh output path:

```sh
/dev/shm/pa194-unpair-diagonal/check-unpair-cantor.sh "$PWD" /dev/shm/pa194-scheduler-controller /dev/shm/pa194-unpair-diagonal /dev/shm/pa194-fetch-coherent-full-v2 /tmp/pa194-fetch-coherent-full-v2.log /tmp/current14-standard-fresh-build-20261104/lib /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib /dev/shm/pa194-unpair-cantor-replay
```

`check-unpair-cantor.sh` calls the prerequisite `check-unpair-after-fetch.sh` from `/dev/shm/pa194-scheduler-controller`, then checks these two new modules. Its final PASS line refers to the full seven-module suffix, rather than the earlier PASS for only the decoder rounds.

The repository-source replay also passed using this directory for both source
arguments against the independently rebuilt fetch baseline. The graph and
general foundations remain prebuilt.
