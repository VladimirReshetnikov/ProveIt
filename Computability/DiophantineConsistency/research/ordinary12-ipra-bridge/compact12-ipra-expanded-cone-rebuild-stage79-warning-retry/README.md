# Expanded compact/iPRA rebuild: stage 79 exact-warning retry

The earlier stage 79 was rejected because Lean emitted an unused-section-
variable warning for `hirr` in `KLower.raw_tagged`. The source has an explicit
`include hirr`, and downstream `KLowerTag` and `KLowerQHyp` pass that argument
to `raw_tagged`. Removing it would alter the theorem interface. This retry
keeps the source and theorem statement unchanged and accepts **only** that
exact, source-hash-pinned warning as a documented exception to the otherwise
fatal warning policy. The earlier rejected run and receipt are unchanged.

The separate `verify_warning.py` requires source SHA-256
`9c4d606be83bdb5da13115f7bbe05b84c8aee1a1f5a2b85518fa6dd4327ec5b7`,
the recorded rejected log SHA-256
`8200afd8ab177e93863b2e2f9deef49bfa79049b29d8d57a7bce2f60ce89aefa`,
and the full expected warning after normalizing only the source path.
It requires exactly one warning and no `error:` or `sorryAx`; the retry log
must match the normalized rejected log byte-for-byte. `check_mutations.py`
was run and rejected an extra-warning, missing-warning and wrong-variable
mutation. The verifier is a separately executed check, not a claim that an
independent reviewer audited the theorem or its dependencies.

The retry revalidated all earlier runner hashes and guards, the full selected
overlay and 425 source pins, and the direct guards from the rejected stage.
It moved the exact earlier rejected object to a distinct quarantine and
compiled `KLowerRaw` again. Lean exited 0 in 0.749 seconds and emitted the
same warning; the verifier accepted precisely that warning, and no other
warning or error. The retry object hash
`ca70aa5d67e2fdc4efef374b6071d4e5801046b2bc1cb863ebb43e5440dcca1c`
matched the rejected object's bytes; the separate quarantine and receipts
preserve the two run outcomes. The wrapper then rechecked the baseline,
source, output and direct-dependency guards and exited 0 with
`completed: 79, total: 425`. The 77–78 successful stages had been compiled
in the earlier stopped batch and were revalidated by this wrapper.

Exact source snapshots, log, normalized verifier output, dependency guards,
quarantine receipt and terminal receipt are in `observations/`. The runner
SHA-256 is `f749308aa658453e4ace9bb35a7aed47a4eb822e17cf0077cb3e1c92a39a38d9`;
the verifier SHA-256 is
`7330742b4934efe8a35fd68f55d6e7e2aa329092a2881cfeba755939dba48c9c`;
the expected normalized warning SHA-256 is
`99e2bfd537967357a084cd466ee67eaad26a8892b135d9b66dd1c591e0a81f00`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source-to-object origin, package, dynamic and broader
transitive ancestry remain open, as do 346 rebuild stages and the compact
model-to-iPRA join. File and resource checks are point-in-time.
