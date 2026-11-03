# Expanded compact/iPRA rebuild: stage 81 exact-warning retry

The earlier stage 81 was rejected because Lean warned that section variables
`hirr` and `ht` were unused in `KLower.tag_inhabited`. The source has an
explicit `include hs hirr ht`, and downstream `KLowerQHyp.lean` calls
`tag_inhabited hs hirr ht`. Removing those parameters would change the theorem
interface. This retry keeps the source and theorem statement unchanged and
accepts **only** this exact source-hash-pinned warning as a documented
exception to the otherwise fatal warning policy. The earlier rejected run and
receipt remain unchanged.

The separate `verify_warning.py` requires source SHA-256
`ef698a4b035fd93db09c51ff37c30d96ef3c5b944f8a75cd24168d12606461d3`,
the recorded rejected log SHA-256
`3ae640bddbe65eb5e086ee5bce8bfdfcb978a60fe4580e042575ccb6bffa11ff`,
and the full expected warning after normalizing only the source path. It
requires exactly one warning and no `error:` or `sorryAx`; the retry log must
match the normalized rejected log byte-for-byte. `check_mutations.py` was run
and rejected extra-warning, missing-warning and wrong-variable mutations. The
verifier is separately executed; this is not a claim that an independent
reviewer audited the theorem or dependencies.

The retry revalidated all prior runner hashes and guards, including the
separate stage79 warning baseline, full selected overlay and 425 source pins,
and direct guards from the rejected stage81. It moved only the exact rejected
stage81 object to a separate quarantine and compiled `KLowerTag` again. Lean
exited 0 in 0.785 seconds and emitted the same warning; the verifier accepted
precisely that warning and no other warning or error. The retry object hash
`48cf2bbd2d623aa105568704dc61b0ec1c073531e85d133a5df46e603d796829`
matched the rejected object's bytes; the quarantine and receipts preserve the
two outcomes. The wrapper rechecked baseline, source, output and direct
dependency guards and exited 0 with `completed: 81, total: 425`. Stage80 had
compiled in the earlier stopped batch and was revalidated by this wrapper.

Exact source snapshots, log, normalized verifier output, dependency guards,
quarantine receipt and terminal receipt are in `observations/`. The runner
SHA-256 is `47fcc5e077e12bfefe324f3a20c44792fcb9437dd1902b5853c65bb72e0ceb48`;
the verifier SHA-256 is
`d05bd282b32a40eb97d72e9dbb05eb904b6d674fa0e9eecf1e9f04650848fada`;
the expected normalized warning SHA-256 is
`c8876f4a91179aaf43af11f90ca9d67d00491f874c2ded22706c2c4545e9bdfd`.

This author prefix is not an iPRA endpoint, independent replay or complete
provider audit. Source-to-object origin, package, dynamic and broader
transitive ancestry remain open, as do 344 rebuild stages and the compact
model-to-iPRA join. File and resource checks are point-in-time.
