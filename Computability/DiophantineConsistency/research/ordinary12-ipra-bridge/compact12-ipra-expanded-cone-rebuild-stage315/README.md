# Expanded compact/iPRA rebuild: stopped at stage 316

Stage 315 compiled cleanly. Stage 316, `ZFCinPA.LReplBase`, exited 0 in
16.181 seconds but emitted eight linter warnings: one deprecated `push_neg`,
three broad simp discrimination-tree keys and four unused simp arguments.
The log has no `error:` or `sorryAx`. The runner rejected the object and
stopped; no later stage ran. Source and direct dependency guards stayed
unchanged. The rejected object SHA-256 is
`46cf01d55ba0724905e6b3eeb075a4ee72f34679920617fc48afbdb112a3e880`.

Runner SHA-256 is
`51248a1ac3774525cc64bc60d084d715e90e566ddafde171518166d45fa7c31b`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,427,108 KiB; brief children and overlap can be missed. The prefix
through stage 315 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
