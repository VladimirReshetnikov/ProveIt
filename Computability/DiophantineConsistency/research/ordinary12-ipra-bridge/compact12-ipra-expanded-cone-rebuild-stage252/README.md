# Expanded compact/iPRA rebuild: stopped at stage 263

Stages 252–262 compiled with exit code 0 and no warnings; their individual
source, guard, log, timing and object receipts are retained. Stage 263,
`ZFCinPA.ConstructibleInterpretation`, exited 0 after 20.058 seconds but
emitted an `unnecessarySimpa` warning and an unused section-instance warning.
The runner rejected its object and stopped without running later stages. Its
source and direct dependency guards were unchanged. The rejected object
SHA-256 is `7b24b2a930ba755a9d9e9ff2c98200042cb409e801c64eeb07903ad7ae83864d`.
The warned lemma is used in this source and in `LSchema.lean`; a separately
guarded retry can preserve its interface while pinning the exact warning log.

Runner SHA-256 is
`0c05d702c9f34b0b940517485f257496da92583a8e92d3f1729bedcd94584848`.
Five-second monitoring sampled at most two Lean children and minimum available
memory 18,262,192 KiB; brief children and overlap can be missed. The author
prefix through stage 262 is not an iPRA endpoint, independent replay, or full
provider audit. The rejected object requires quarantine before replacement.
