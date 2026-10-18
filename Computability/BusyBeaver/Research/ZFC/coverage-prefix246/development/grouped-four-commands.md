The four-cut/128-guard candidate is frozen at manifest SHA `9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09`. Its102 units cover the unchanged233 cuts and232 joins. The3 existing representative records are listed in `representatives-reuse.json` (SHA `2d3c42c2a354379ceb11bdefe28f6838df6ff5175f639e2c5152c84248dda64a`); their source and audit bytes agree with this grouped plan. The static review rehashed all65 current inputs in each existing record, the source snapshots and fresh objects. No guard/runner/compiler was invoked during preparation.

For root review and a single initial measurement, the first new unit is `SitesPrefix246Batch001`: cuts1–4,30 leaves,42 guard cases,4 probes/4 typed callers. The runner skips the3 existing representatives and will check only this unit because `--max-units 1` is explicit. It preserves the per-unit120-second source/audit bound and default Lean proof limits. Total runner wall bound is180 seconds with an additional3-second termination grace only if needed.

Root-only preparation (creates readiness metadata, invokes no guard/compiler/version):

```sh
python3 -B /tmp/zfc-prefix246-lean/coverage/run_pipeline.py \
  --repo /home/codex/.codex/worktrees/ec20/Proofs \
  --manifest /tmp/zfc-prefix246-lean/coverage/guards-four/pipeline-manifest.json \
  --manifest-sha 9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09 \
  --reuse-list /tmp/zfc-prefix246-lean/coverage/representatives-reuse.json \
  --max-units 1 --wall-seconds 180 \
  --output /tmp/zfc-prefix246-lean/coverage/grouped-four-prepared \
  --prepare-only
```

Root-only first grouped proof measurement, with a new output:

```sh
python3 -B /tmp/zfc-prefix246-lean/coverage/run_pipeline.py \
  --repo /home/codex/.codex/worktrees/ec20/Proofs \
  --manifest /tmp/zfc-prefix246-lean/coverage/guards-four/pipeline-manifest.json \
  --manifest-sha 9ee21ec2c106e88f01b1613588dc65b0cdd1f12e04abcd13abc8fbaabb151b09 \
  --reuse-list /tmp/zfc-prefix246-lean/coverage/representatives-reuse.json \
  --max-units 1 --wall-seconds 180 \
  --output /tmp/zfc-prefix246-lean/coverage/grouped-four-first
```

After a successful single-unit measurement, retain that record and use a fresh continuation output with the3 representatives and new successful unit included in the reuse list. The selected number of new units and overall wall bound remain explicit root choices. A bound failure must preserve its record and trigger smaller grouping; it must not trigger raised proof limits. The final source and audit already include all3 endpoint probes and typed callers. No complete coverage claim follows until the final unit and every predecessor pass.
