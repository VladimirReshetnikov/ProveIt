# Expanded compact/iPRA rebuild: stopped at stage 275

Stages 273–274 compiled cleanly. Stage 275, `ZFCinPA.NativeSchemaSem`, exited 0
in 8.795 seconds but emitted four unused section-variable warnings and two
unused simp argument warnings, with no `error:` or `sorryAx`. The runner
rejected its object and stopped; no later stage ran. A warned lemma is used
later in the same source. Source and direct dependency guards were unchanged.
The rejected object SHA-256 is
`3a096eb8f79bd3983c0cae8397705572058b2c2bfe70068db7e4da94e59c360a`.

Runner SHA-256 is
`417b6614486f367c2116b37d36199bb4d7dcad42d59a921fcd7f927a4c00d591`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,421,184 KiB; brief children and overlap can be missed. The prefix
through stage 274 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
