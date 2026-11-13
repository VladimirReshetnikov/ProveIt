# Expanded compact/iPRA rebuild: stopped at stage 368

Stage 368, `ZFCinPA.R2Main`, exited 0 in 11.311 seconds but emitted two
unused section-variable warnings, with no `error:` or `sorryAx`. The runner
rejected the object and stopped; no later stage ran. Both warned lemmas are
used repeatedly in the same source. Source and direct dependency guards stayed
unchanged. The rejected object SHA-256 is
`97dfa715e4a845e79cd15684ec300d9fd1a60f49a0f2283fbcbb8bb4ef6731e9`.

Runner SHA-256 is
`5e31b52f3a2a8e2f1343e73a21556581f112f5f8633c74014fbe0cac73f78853`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,331,112 KiB; brief children and overlap can be missed. The prefix
through stage 367 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
