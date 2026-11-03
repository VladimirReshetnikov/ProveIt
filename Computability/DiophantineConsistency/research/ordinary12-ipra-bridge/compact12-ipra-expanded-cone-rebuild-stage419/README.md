# Expanded compact/iPRA rebuild: stage 419 failed

Stage 419, `ZFCinPA.QSchema`, exited 1 in 3.940 seconds because the selected
pre-existing `InternalInterpretation` object does not contain the newer
`consistent_of_falsum_transfer` helper used at line 187. No object or later
stage was produced. Source and direct dependency guards stayed unchanged. The
failure is the same source/provider mismatch documented at stages 276 and 317;
it is not a warning exception. The exact failed source, receipt and compiler
log are retained for a separately reviewed and re-pinned correction.

Runner SHA-256 is
`de5980b32d7e943a2594d3cc3fcb44133365e0f6c3ea6e6fdb0ac0d59f7d70ab`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,559,252 KiB; brief children and overlap can be missed. The prefix
through stage 418 is not an iPRA endpoint, independent replay, or full provider
audit. Current-source/provider ancestry remains a documented limitation.
