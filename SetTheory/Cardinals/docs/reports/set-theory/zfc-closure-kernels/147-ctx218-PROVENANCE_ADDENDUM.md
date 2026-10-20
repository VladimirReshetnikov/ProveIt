# Provenance addendum: a distinct 218-state alternative

During final release review on 2026-10-20, a separate public K218 packet was
identified in ProveIt commit
`c4568161bf0eafeabc9e6f5a4a5c8c0a90c22f70`. It is **not this release**.
This packet is therefore delivered as
`K218_Contextual_Alternative_2026-10-20.zip`; the internal directory name
`K218_Construction_2026-10-20` is retained for portability.

The public packet's archive SHA-256 is
`f22c853e1da435a932f9bf69321cfd790f7318acc2cc340a27f275d1c0d43f2c`.
Its native table, canonical table and source hashes respectively are:

- `2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`
- `06d7a91c583739e17f8b33ce3e03d0aeaf9e1faa186c76d596418942fe2a8730`
- `b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9`

This alternative has the corresponding hashes:

- `3c64cf321c9ca11153901cdb19e7326b8bfbd0d3c8d94357ead127a9c9b491c1`
- `7ca993f2c7f2cbdbca5b69756712d0fac17ff81e81e260190a599115c0643acb`
- `1dcd14a47c4f100316c71f8a346b84000f3d12efc29123d1cce212d4bbfa2efe`

Read-only byte inspection and independent breadth-first transition
canonicalization establish that the tables are distinct even after relabeling;
the source bytes also differ. The public README reports 312,909 blank-startup
transitions, whereas this alternative independently verifies 312,701. This
comparison does not replay or certify the public packet's proof, and distinct
transition graphs do not establish computational-behavior inequivalence.
See `verification/provenance_reconciliation/comparison.json`.

Both constructions employ the broad idea of consulting a preceding tape bit
to recover decoder context. No priority, unique state-count record, or
minimality claim is made here. This alternative retains its independently
reconstructed lineage from the pinned original K219 archive at commit
`26d5de6d21fa354d50e0b84fe851c289925b8d72`; the newly observed public K218
packet is not a construction input or a premise of its theorem.

No verified machine, source, recipe, proof checker, runtime certificate,
startup, pinned vendor archive or report bytes were changed for this
addendum. The separate public K218 ZIP is not bundled. The original K219
credit and inherited logical-calibration boundary remain as stated in
`NOTICE.md`, `PROVENANCE.json` and the report.
