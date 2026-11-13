# Expanded compact/iPRA rebuild: stage 197 exact-warning retry

The earlier stage197 was rejected because Lean warned that the explicit
`witness : V` binder in `KQ1Basic.interpreted_pair` was not referenced. The
same source calls `interpreted_pair` positionally from `quotient_pair`, and
removing or renaming the binder changes its named interface. This retry keeps
the source and theorem statement unchanged and accepts **only** the exact
source-pinned warning as a documented exception to the otherwise fatal warning
policy. The earlier rejected run and receipt remain unchanged.

The separate `verify_warning.py` requires source SHA-256
`c6dcf8a8babed8e7544bc091a53070c923f67c97c2f3e8439783c243c8293ca8`,
the recorded rejected log SHA-256
`d36f414ca417b1858033e79a6d1c1f529c2c5f43ca3de9593125f94e5162b0d0`,
and the full expected warning after normalizing only the source path. It
requires exactly one warning and no `error:` or `sorryAx`; the retry log must
match the normalized rejected log byte-for-byte. `check_mutations.py` rejected
extra-warning, missing-warning and wrong-variable mutations. The verifier is
separately executed; this is not an independent theorem or dependency audit.

The retry revalidated all earlier runner hashes and guards, including the
three previous warning baselines, full selected overlay and 425 source pins,
and direct guards from the rejected stage197. It moved only the exact rejected
stage197 object to separate quarantine and compiled `KQ1Basic` again. Lean
exited 0 in 0.621 seconds and emitted the same warning; the verifier accepted
precisely that warning and no other warning or error. The retry object SHA-256
`fd61d67e686d620b818bb53cca8d9e2eb2fa49c6cd70731bfdffea92c078c171`
matched the rejected object's bytes; quarantine and receipts preserve both
outcomes. The wrapper rechecked baseline, source, output and direct dependency
guards and exited 0 with `completed: 197, total: 425`. Stage196 had compiled
in the earlier stopped batch and was revalidated by this wrapper.

The runner SHA-256 is `43ed40f592406e902d36be404a3adc4f8ab492a5c80522e5e1d52bbed2e50105`;
the verifier SHA-256 is
`21c335e90ae8247f5f47638a46d8b6550e3d01a9a27e043a151474cbda7f74fa`;
the normalized warning SHA-256 is
`7c0c01e0b041b48ea83b9e4fe5cad46ddbe2c03c542b34ce6107a5aa3c630145`.
Exact source, log, verifier output, guards, quarantine and terminal receipts
are under `observations/`. Five-second process/memory sampling recorded no
Lean child; because the actual Lean compile lasted only 0.621 seconds, this
cannot establish the absence of brief overlap. The minimum sampled
MemAvailable was 18,608,672 KiB; monitor SHA-256 is
`d499de6719f3ff93dd7cc2083cb2798c5fd877434717299e5aff0deee696be22`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source-to-object origin, package, dynamic and broader
transitive ancestry remain open, as do 228 rebuild stages and the compact
model-to-iPRA join. File and resource checks are point-in-time.
