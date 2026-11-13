# Expanded compact/iPRA rebuild: stopped at stage 310

Stages 308–309 compiled cleanly. Stage 310, `ZFCinPA.LGlue1`, exited 0 in
12.911 seconds but emitted three linter warnings: an unused and unreachable
`(exfalso; omega)` tactic and an unused `done` tactic. There is no `error:` or
`sorryAx`. The runner rejected the object and stopped; no later stage ran.
Source and direct dependency guards stayed unchanged. The rejected object
SHA-256 is `7a8d49aa7939dc3c3bbdb282c7bd1c858841b48a7b94268657b958559636df2e`.

Runner SHA-256 is
`f593c2933363f230bd5ec416e95f98009c79dd9f4e01e09747f91f7d7ae2ba99`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,396,256 KiB; brief children and overlap can be missed. The prefix
through stage 309 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
