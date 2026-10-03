# Review of the six-report placement at 224ca41df

The normal merge `adc1d050e` incorporated `224ca41df` and its upstream merges while the ten-archive review was running. This is a placement of six existing deliveries, not six additional mathematical reports. Every one of its **81 added files** is byte-identical to a member of one of its six removed ZIPs. The [inventory](placement_224ca41df_inventory.json) records each placed path, SHA-256, byte length, source archive/hash and original member path. There are zero unmatched added files.

The source commits retain all original ZIPs. Of 105 original members, 81 are placed and 24 are intentionally omitted by that commit: original PDFs/manifests, duplicate documents/logs, and large regenerable coefficient fixtures. No source repair has been silently incorporated by renaming a file. Existing proof/source reviews transfer to these exact blobs, with their documented defects and patches still applicable.

| Placed prefix | Original report | Applicable review |
|---|---|---|
| `canonical-diophantine-certificates/17-positive-spectrum-*` | Positive Spectrum | [Earlier complete spectral review](review_spectral_060e08a07.md) |
| `canonical-diophantine-certificates/18-spectral-guards-*` | Spectral Guards | [Earlier complete spectral review](review_spectral_060e08a07.md) |
| `polynomial-witness-histories/01-boundary-transport-*` | Linear Boundary Transport | [Earlier boundary review](review_boundary_sandpile_060e08a07.md) |
| `polynomial-witness-histories/06-polynomial-histories-*` | Unique Polynomial Histories | [Earlier nine-report index](incoming_substrate_review_2a8a39599.md) |
| `polynomial-witness-histories/15-one-coordinate-*` | One Coordinate | [Current review](review_one_coordinate_aebfa.md) |
| `smooth-diophantine-finalizers/13-smooth-quartic-*` | Smooth Quartics | [Current review](review_smooth_quartic_aebfa386e.md) |

These report directories live below `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem`. Code and data files are stored in the respective `code/` and `data/` subdirectories. The unchanged README/Makefile commands refer to original package layouts and unprefixed Python imports. The placements alone are therefore not a directly runnable rewrite of those commands. This is a layout issue, not a new mathematical defect.

The [portable staging helper](replay_placed_substrates_224ca41df.py) authenticates all 81 current files, retrieves the pinned original archives from Git history, restores the omitted files and original names, then overlays the authenticated current files. It executes no recovered code and requires a fresh destination. The [root replay receipt](replay_placed_substrates_224ca41df.json) confirms six complete original layouts, 105 restored members and all 81 exact current overlays.

```
python replay_placed_substrates_224ca41df.py \
  --repo /path/to/Proofs --destination /new/private/replay-directory
```

The existing source-review helpers can then consume the listed package roots and apply their separately pinned repairs on private copies. For archive-based helpers, recover the original ZIP without changing the checkout, for example:

```
git show 224ca41df^:docs/incoming/Smooth_Quartic_Diophantine_Certificates.zip > /private/Smooth_Quartic_Diophantine_Certificates.zip
```

The source comment that smooth quartics and one-coordinate certificates had not yet been reviewed describes the placement's preparation time. Both have since received independent reviews and original/repaired replay where appropriate. The inventory is exact byte provenance, not a claim that the combined canonical-document organization or eventual typeset Parts have already been reviewed. The universal arithmetic ledger is unchanged.
