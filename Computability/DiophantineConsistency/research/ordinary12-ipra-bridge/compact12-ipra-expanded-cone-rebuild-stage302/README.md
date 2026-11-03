# Expanded compact/iPRA rebuild: stopped at stage 306

Stages 302–305 compiled cleanly. Stage 306, `ZFCinPA.LFvBound`, exited 0 in
17.059 seconds but emitted one unused `hw` binder warning, with no `error:` or
`sorryAx`. The runner rejected its object and stopped; no later stage ran. The
warned lemma is called positionally later in the same source. Source and
direct dependency guards stayed unchanged. The rejected object SHA-256 is
`021f78a695755002890c3f881601fc9197e50147cdc73776738f675d7fafc964`.

Runner SHA-256 is
`425b92e4046f6f5e3b66a6a3c8272278000ec130f8c1dc08bd523e01ec27ce2e`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,380,444 KiB; brief children and overlap can be missed. The prefix
through stage 305 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
