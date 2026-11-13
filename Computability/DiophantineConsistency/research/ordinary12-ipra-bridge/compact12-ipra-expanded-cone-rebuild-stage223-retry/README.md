# Expanded compact/iPRA rebuild: stopped at stage 224

This separately captured run raised the rejected setup's batch limit from five
to 15 while retaining the per-stage checks. Stage 223, `KQ1ZF`, compiled
cleanly in 0.373 seconds with unchanged direct guards. At stage 224,
`KLowerQHyp`, Lean exited 0 in 0.789 seconds but emitted two unused-section
variable warnings, so the runner rejected the result and stopped. It emitted
no later stage receipts. Source and direct dependency guards remained
unchanged. The rejected object hash is
`e4012864d6877d2c0591c859c51d87fedf8f44578e6b3552cc9d063531b82671`.

The file uses `tsing_tagged hs hirr ht` and `tsing_members hs hirr ht` later
in the same source, so omitting the warned variables would change existing
call interfaces. The exact original log and source snapshot are retained for
a separately guarded warning-baseline retry. The runner SHA-256 is
`d4f61bd012fd1f1229000def41fdd84a94c701c01270d07a12c7dc919e485a02`;
the stage 224 source SHA-256 is
`342485cb6294e12d0c52cc747758d447221670ce7dfda096b2f242d7a2974e62`.

The five-second monitor saw no Lean child and recorded minimum sampled
MemAvailable of 18,653,840 KiB; short compilations or overlaps can be missed
between samples. The author prefix through stage 223 is not an iPRA endpoint,
independent replay, or full provider audit.
