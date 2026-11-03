# Expanded compact/iPRA rebuild: stage 84 exact-warning retry

The earlier stage 84 was rejected because Lean emitted three unused-variable
warnings for explicit `witness : V` binders in `KQ1Model.member_left_congr`,
`member_right_congr` and `modelSetoid`. These explicitly named arguments are
threaded through other theorem and quotient-domain definitions; changing or
removing them would alter the named interface. This retry keeps the source and
theorem statements unchanged and accepts **only** the exact source-pinned
three-warning full log as a documented exception to the otherwise fatal
warning policy. The original rejected run and receipt remain unchanged.

The separate `verify_warning.py` requires source SHA-256
`284f5c1a9ac828bd2b773fbfe365ec1d5b2471f7f6088e2b0f82abfc0fbfcd2a`,
the recorded rejected log SHA-256
`00e83762778f03721393d83d3f971232944f39bab225ff080181cbac6c4d4f0a`,
and the complete expected log after normalizing only the three source paths.
It requires exactly three warnings and no `error:` or `sorryAx`; the three
named metatheory axiom-report lines are included in the exact comparison.
`check_mutations.py` rejected extra-warning, missing-warning, wrong-variable
and changed-axiom-report mutations. The verifier is separately executed; this
is not a claim of an independent theorem or dependency audit.

The retry revalidated all prior runner hashes and guards, including both
previous warning baselines, the selected overlay, 425 source pins and direct
guards from the rejected stage84. It moved only the exact rejected stage84
object to a separate quarantine and compiled `KQ1Model` again. Lean exited 0
in 0.634 seconds, emitted the same three warnings, and the verifier accepted
exactly that log. The retry object SHA-256
`e52477f9a7fc2b6aae82a387281beb829246270cf7b3fbf6d3bdadb052077729`
matched the rejected object's bytes; quarantine and receipts preserve both
outcomes. The wrapper rechecked baseline, source, output and direct dependency
guards and exited 0 with `completed: 84, total: 425`. Stages 82–83 had
compiled in the earlier stopped batch and were revalidated by this wrapper.

Exact source snapshots, log, verifier output, dependency guards, quarantine
receipt and terminal receipt are in `observations/`. The runner SHA-256 is
`afe5cce022d23567a573b83570e08a4b6c64dac664b77f50bbd7f0cea9b18843`;
the verifier SHA-256 is
`c525d03a80ea7b8b66a82a090f6ca9020bf89507722d9b2d5f861b7de2bffe02`;
the normalized full-log SHA-256 is
`ce41a6fcc3c0116286d878add6ddb33c1f9d39970c3d4285d71e77dcf08b9ddb`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source-to-object origin, package, dynamic and broader
transitive ancestry remain open, as do 341 rebuild stages and the compact
model-to-iPRA join. File and resource checks are point-in-time.
