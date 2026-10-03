# Review of the six-report placement at bbaf322e5

The normal merge `3b69f35cc` incorporates a second placement of existing deliveries. Every one of its **64 added files** matches a member of one of the six removed ZIPs byte for byte. The [inventory](placement_bbaf322e5_inventory.json) records all paths, source member/ZIP identities and hashes, with zero unmatched additions. These are not six newly proved reports. Original ZIPs remain in Git at `bbaf322e5^`.

| Canonical report and prefix | Existing review |
|---|---|
| `canonical-diophantine-certificates/19-no-borrowed-firings-*` | [Sandpile review](review_boundary_sandpile_060e08a07.md) |
| `canonical-diophantine-certificates/20-compressed-queue-*` | [Compressed queue](review_compressed_queue_aebfa.md) |
| `liveness-beyond-halting/12-clock-spectra-*` | [Spectral/clock review](review_spectral_060e08a07.md) |
| `stochastic-and-thermal-exactness/11-mixing-arithmetic-*` | [Mixing review](review_mixing_aebfa386e.md) |
| `stochastic-and-thermal-exactness/12-coercive-green-*` | [Coercive/connected review](review_coercive_connected_aebfa386e.md) |
| `stochastic-and-thermal-exactness/13-well-conditioned-*` | [Coercive/connected review](review_coercive_connected_aebfa386e.md) |

All report directories are below `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem`; code/data keep the corresponding prefixed filenames in their subdirectories. The original import names and package-relative commands remain unchanged inside the delivered source. Existing findings and separately pinned patches therefore remain applicable. Renaming files has not applied those repairs or made the original commands directly runnable from the prefixed directories.

The [portable stager](replay_placed_substrates_bbaf322e5.py) authenticates all 64 current files, retrieves the six pinned original archives from Git, restores all 88 members into their original layouts, and overlays the authenticated current source bytes. It executes no source code. Its [root receipt](replay_placed_substrates_bbaf322e5.json) verifies the full restoration and all current overlays. The 24 omitted delivery artifacts remain recoverable in the original archives; they are not treated as missing mathematical evidence.

```
python replay_placed_substrates_bbaf322e5.py \
  --repo /path/to/Proofs --destination /new/private/replay-directory
```

Run the existing review helpers on those package roots, or retrieve a ZIP directly for archive-based helpers:

```
git show bbaf322e5^:docs/incoming/Mixing_Does_Not_Remove_Arithmetic.zip > /private/Mixing_Does_Not_Remove_Arithmetic.zip
```

As with the [first placement](review_placement_224ca41df.md), this exact-byte check transfers source review, not a review of any future combined typeset manuscript. No mathematical claim, source operation ledger or witness domain changes in this placement.
