# Expanded compact/iPRA rebuild: stopped at stage 320

Stages 318–319 compiled cleanly. Stage 320, `ZFCinPA.SeedTemplate222`, exited
0 in 5.474 seconds but emitted one unused simp argument warning, with no
`error:` or `sorryAx`. The runner rejected the object and stopped; no later
stage ran. Source and direct dependency guards stayed unchanged. The rejected
object SHA-256 is
`ec75f59276edce16ed1ef9180ca9e5cf67f10bcdedcf96431c72e4d81ab4f8ff`.

Runner SHA-256 is
`899d875102d002c91d0386822e159944e1ef7995b0c996c59ea6c3137bcd5e3c`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,443,652 KiB; brief children and overlap can be missed. The prefix
through stage 319 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
