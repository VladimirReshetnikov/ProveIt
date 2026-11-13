# Expanded compact/iPRA rebuild: stages 286–300

All fifteen modules, from `StagedSuccessor` through `LFinalRepl`, compiled
with exit code 0 and no warnings. Each stage retains its source snapshot,
dependency guard receipts, log, timing and object hash. The wrapper rechecked
all previous receipts, 425 current source pins, corrected cone and baseline,
selected overlay and exact-warning exceptions before and after the batch. It
reported 300/425 complete and unchanged selected overlay. Runner SHA-256:
`f9423dedf276c701995c5b2290f6acbe560ac0a13a7ad6145b36005388ada6b2`.

Five-second monitoring sampled at most two Lean children and minimum
MemAvailable 17,591,668 KiB; per-stage starts also checked available memory
and process limits. These are sampled and point-in-time observations, so
brief processes or overlaps can be missed. The monitor SHA-256 is
`7b11280172462b03b798249c6c171a3251c5663d251f0e8fd9deb9ac898c31fd`.

This author prefix is not an iPRA endpoint, independent replay, or complete
provider audit. Package, dynamic and historical object ancestry remain open,
as do 125 stages and the compact model-to-iPRA join. A source/provider mismatch
encountered at stage 276 required a local checked proof correction.
