# Existing decimal seed-lines theorem in the K context

This guard proposes recompiling the byte-identical existing `research/current14-seed-lines-binding/SeedLines.lean` as `Sign17SeedLines` against the recent independently audited symbolic-K-byte provider context. It retains the twelve explicit in-Lean digit lines and `decimal_lines_eq_seed` statement, without changing their content. The original historical proof's DecimalMachine215 object and the current provider object have the same SHA-256 but different captured realpaths. This replay checks the recent direct object route; it does not establish full transitive source/object ancestry, interpret PDF/TeX or identify external files.

No-Lean preflight passed (exit 0). The K provider, DecimalMachine215 overlay/hash and Init routes, identical source and inherited one-thread/child/resource guards are pinned. Runner SHA-256 `3c48b052c70e502c3e075dcb1aa32f0af0b4d111221491259df1bbd6443b3da5`; manifest `192598a7ca2d0b22f35a8ad1d0d97679deb903d667e3cefe3ce1a5256c0b7028`; existing source `36bd157407732377d364186378980650c48c89b6dfee63d5688234791e7ff8d3`; DecimalMachine215 object `9a28850ecd82e97bbc7361ec39820edc4abe8473a62f08079a1da34fdd462687`. Independent prelaunch and exclusive allocation are required.

Independent prelaunch passed at `reviews/nine-sharing-sign17-seed-lines-replay-prelaunch-independent/`.

Attempt 01 completed with observed outer session 99576, exit 0; stage and postflight passed. See `attempt01/`. Independent terminal audit is pending.

The [independent terminal audit](../../reviews/nine-sharing-sign17-seed-lines-replay-terminal-independent/README.md) passed; the attempt is frozen.
