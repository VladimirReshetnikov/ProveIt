# Expanded compact/iPRA rebuild: stopped at stage 270

Stage 269, `ZFCinPA.Translation`, compiled cleanly. Stage 270,
`ZFCinPA.NativeTheory`, exited 0 in 2.806 seconds but emitted one unused
section-instance warning for `sat_of_models_toSet`. The runner rejected its
object and stopped; no later stage ran. Source and direct dependency guards
were unchanged. The rejected object SHA-256 is
`f72e7e6f13676cc4675e402cd479124cfe70a222cabc1d041cf6b38be79242bb`.
The theorem is used by later declarations in the same source, so a separate
exact-warning retry can preserve its existing interface.

Runner SHA-256 is
`f8cc928655fa5ae5e6b503d7fc731b2dd7f0cfac9d7ca68c8f61b2c4247dcae7`.
Five-second monitoring sampled at most one Lean child and minimum available
memory 18,496,468 KiB; brief children and overlap can be missed. The prefix
through stage 269 is not an iPRA endpoint, independent replay, or full provider
audit. The rejected object requires quarantine before replacement.
