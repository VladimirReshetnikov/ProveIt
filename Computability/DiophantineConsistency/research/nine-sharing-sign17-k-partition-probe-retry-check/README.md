# Generic three-block finite partition: associativity retry

This checked one-stage retry retains the failed probe's statement and
all provider/resource guards, changing only the third branch's simplifier to
normalize nested offsets by reverse associativity and numeral reduction. It
pins the failed outer receipt and independent audit. The proposed theorem is
generic; no candidate, global rank, K or file claim follows. Author no-Lean
preflight exited 0.

Runner SHA-256:
`7f60e86bac83cf43c7740da50c5e950cad2ac369d4fc8e3231db0504f6a38b9b`;
manifest SHA-256:
`a0cc5f2f079ac94caf57d39965f94493b25c3759356eaa0ec32824c4e89cf588`;
source SHA-256:
`964acff05a2c13c5d77d2e6ecbe4286c52ddbcfbdfceae9da01f2ec9de882ad8`.
The run used the established independent-review and exclusive-slot workflow.

The [independent prelaunch audit](../../reviews/nine-sharing-sign17-k-partition-probe-retry-prelaunch-independent/README.md) passed.

Attempt 01 passed with observed outer exit 0; see [`attempt01`](attempt01/README.md). The [independent terminal audit](../../reviews/nine-sharing-sign17-k-partition-probe-retry-terminal-independent/README.md) passed; the packet is frozen.
