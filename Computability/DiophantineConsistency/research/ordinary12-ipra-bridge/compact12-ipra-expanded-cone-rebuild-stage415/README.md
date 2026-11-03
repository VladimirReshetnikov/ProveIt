# Expanded compact/iPRA rebuild: stopped at stage 418

Stages 415–417 compiled cleanly. Stage 418, `ZFCinPA.QSchemaSem`, exited 0
in 8.885 seconds but emitted four unused section-variable warnings and two
unused simp argument warnings, with no `error:` or `sorryAx`. The runner
rejected the object and stopped; no later stage ran. One warned lemma is used
later in the same source. Source and direct dependency guards stayed unchanged.
The rejected object SHA-256 is
`0ecb5fef2a0fc52138b9c21e02170118d091995d17b417bcb0af19fe61464145`.

Runner SHA-256 is
`cf4ba9fdfa75d852b12cc0c749a54888c156fc30b00ea9df405e6234b317ad3b`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,432,212 KiB; brief children and overlap can be missed. The prefix
through stage 417 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
