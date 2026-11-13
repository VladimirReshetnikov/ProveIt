# Independent sign24 scoped interpreter-limit retry prelaunch review

Checker session 43950 exited 0. It verifies byte-identical source, manifest,
provider survey and union against the prior failed bridge attempt, and
reconstructs the guard: only the fresh output path, state scope label and
Lean interpreter limit `-M2800` → `-M3600` differ. The 4 GiB sampled RSS
cap, 10 GiB host floor, 120-second timeout, 5 GB disk precheck, one-thread
setting and provider guards remain unchanged.

The checker inspects three previous sign24 bridge memory-exception logs and
sampled RSS receipts, reruns the independently audited successful sign25
`-M3600` endpoint receipt, and runs the no-Lean preflight. These observations
justify a targeted test but do not diagnose the exact cause or guarantee
success. Sampling and ancestry limitations remain; no new Lean theorem is
claimed. The retry requires the exclusive slot and its resource checks.
