# Expanded compact/iPRA rebuild: stopped at stage 272

Stage 271, `ZFCinPA.NTemplate`, compiled cleanly. Stage 272,
`ZFCinPA.NativeInterp`, exited 0 in 5.542 seconds but emitted three unused
section-variable warnings and one unused simp argument warning, with no
`error:` or `sorryAx`. The runner rejected the object and stopped; no later
stage ran. The warned theorems are used in later declarations in the same
source. Source and direct dependency guards were unchanged. The rejected
object SHA-256 is
`1217722f6af7a78773dc27059348be28a0e25d31aee7327a15e3c218011ca909`.

Runner SHA-256 is
`c0d248780c823f6b432681311c79118a92b6933b3f36a4a75a6cde608546ef40`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,507,388 KiB; brief children and overlap can be missed. The prefix
through stage 271 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
