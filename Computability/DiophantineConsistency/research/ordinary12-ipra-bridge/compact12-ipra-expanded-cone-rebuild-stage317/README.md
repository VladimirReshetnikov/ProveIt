# Expanded compact/iPRA rebuild: stage 317 failed

Stage 317, `ZFCinPA.LSchema`, exited 1 in 3.036 seconds because the selected
pre-existing `InternalInterpretation` object does not contain the newer
`consistent_of_falsum_transfer` helper used at source lines 63 and 78. No
object or later stage was produced. Source and direct dependency guards stayed
unchanged. The failure is the same source/provider mismatch documented at
stage 276; it is not a warning exception. The exact failed source, receipt and
compiler log are retained for a separately reviewed and re-pinned correction.

Runner SHA-256 is
`9550d97a188c857117f9159dce5eb46972dce0b589305bf2b2c5dd45c1f67311`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,550,096 KiB; brief children and overlap can be missed. The prefix
through stage 316 is not an iPRA endpoint, independent replay, or full provider
audit. Current-source/provider ancestry remains a documented limitation.
