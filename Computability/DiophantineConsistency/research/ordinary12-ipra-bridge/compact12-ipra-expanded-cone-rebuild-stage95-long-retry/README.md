# Expanded compact/iPRA rebuild: stage 95 longer retry

The initial stage95 attempt timed out at 180 seconds without producing an
object. Historical author and root timing receipts for the same named source
show successful runs around 7:48–7:55, so this separate retry retained Lean's
`-M3000 -j1 -DElab.async=false` settings and allowed 600 seconds for this
stage. The prior failed runner, source snapshot, receipt and unchanged direct
guards were revalidated; no prior evidence was overwritten.

Before compilation the runner also checked all prior runner hashes, both
baselines, the quarantined rejected objects, all 425 source pins, selected
original and merged provider files, earlier outputs/log hashes, the three
exact-warning baselines, and earlier direct dependency and companion guards.
The exact runner is `run.py`, SHA-256
`946b1cb9afdb6e53f9530459f4be7561e078340a198eab21ee1dcd16a1152711`.

Lean compiled `BusyBeaver.ZFC.ArithmeticDagControlPerm222` in 501.213 seconds,
exit 0, without warnings or `sorryAx`. The source snapshot, dependencies,
companion guards, log, object hash and receipt are in
`observations/batch-019/stage-0095/`. The object SHA-256 is
`5fdec3e97edcf15b4c262efb3c35780475a5a0447ed5586d4c9ff80c0a2554c2`.
The wrapper rechecked full selected overlay, source hashes, prior and current
outputs, warning baselines and direct guards, and exited 0 with
`completed: 95, total: 425`. Earlier receipts and the baselines remain in
the prior sibling packets.

At the coordinator's direction, the equal-length nine-variable
peer ran in a separate output root while this stage was live. The companion
`observe_run.py` sampled Lean process IDs and available memory every five
seconds during this wrapper. Its 104 samples include 18 with two Lean
processes, none with more than two, and a minimum sampled MemAvailable of
17,286,824 KiB; maximum sampled RSS for this stage's Lean child was 2,901,924
KiB. The concurrent peer modules and timestamps are recorded in
`observations/execution-monitor/monitor.json`; sampled monitoring cannot rule
out shorter overlaps or memory dips between samples. The selected overlay and
direct shared-input guards were unchanged at the recorded checks. The
monitor's SHA-256 is
`484fe9910465b0f6a44fddfd733a0ac917ed5c55fa4951378b5d36bd3d9f2e12`;
`observe_run.py` SHA-256 is
`35b0b9481dd8f4e8fd8f590ce883b1cf94a15986e27d97bc8d186a8139fe81a9`.

This is an exploratory author prefix, not an iPRA endpoint, a complete
coherent build or an independent replay. Source/object import-shape agreement
does not authenticate the historical origin of inherited objects. Package,
dynamic and broader provider ancestry remain unverified; 330 rebuild stages
and the compact model-to-iPRA join remain open. File/resource guards are
point-in-time.
