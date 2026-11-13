# Expanded compact/iPRA rebuild: stopped at stage 414

Stages 402–413 compiled cleanly; stage 408 took 142.020 seconds under its
180-second wall bound. Stage 414, `ZFCinPA.QInterp`, exited 0 in 5.821 seconds
but emitted three unused section-variable warnings and one unused simp
argument warning, with no `error:` or `sorryAx`. The runner rejected the
object and stopped; no later stage ran. The warned theorems are used later in
the same source. Source and direct dependency guards stayed unchanged. The
rejected object SHA-256 is
`373896711055c838dc22a84440b934dcb0938b44a87f4eca4ec9e7321856844d`.

Runner SHA-256 is
`fdb589599633e8240b7202e43af5f46e6cb4a45239623017525f06142278332c`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,255,572 KiB; brief children and overlap can be missed. The prefix
through stage 413 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
