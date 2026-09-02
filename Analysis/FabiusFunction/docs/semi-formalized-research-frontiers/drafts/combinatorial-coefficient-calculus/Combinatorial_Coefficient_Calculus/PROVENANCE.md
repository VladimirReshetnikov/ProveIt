# Provenance and consolidation boundary

This ledger identifies the six manuscripts that are inputs to the
combinatorial-coefficient-calculus consolidation.  It freezes the
pre-consolidation source pool at commit
`55038f2fc7d20a483a48125f086a6c8488e45530`.  It does **not** claim that the
editorial union, claim review, proof repair, donor retirement, or final PDF
build has occurred.  The live plan and its deliberately pending rows are in
`SOURCE_DISPOSITION.csv`.

The six TeX files are research-frontier manuscripts.  Their theorem and proof
environments are human-readable mathematical writing, not evidence of Lean
verification.  No Lean build was run for this provenance checkpoint, and no
claim in the source pool is represented here as machine checked.

## Immutable intake chain

| Stage | Immutable commit | What the commit establishes |
| --- | --- | --- |
| Archive arrival | `c3720b763d159c3a009b66e6e89ac500b7843e98` | Adds the six ZIP archives under `drafts/incoming/`. |
| Safe extraction and filing | `d1d5c71e6a8b6aafa751ab5be816e5931b6a50fa` | Extracts one flat TeX/PDF pair from each ZIP, records the original member hashes, and deletes the filed ZIPs. |
| Shared-notation migration | `729820bfe079947d1f1af7877820fbbb9202a1f0` | Rewrites the six TeX sources to the shared notation API; it does not rebuild or alter the six PDFs. |
| Pre-consolidation snapshot | `55038f2fc7d20a483a48125f086a6c8488e45530` | Pins the exact current input files covered by `SOURCE_CLOSURE.sha256`. |

The archive, extraction, and migration commits are all ancestors of the
snapshot commit.  Consequently, the original bytes remain recoverable from
Git even after the live donor directories are retired.

## Identity model

Each input has three intentionally distinct identities.

1. **Original source** means the TeX member inside the ZIP at the archive
   arrival commit.  The same bytes were filed by the extraction commit.
2. **Current source** means the notation-migrated TeX at the pinned
   pre-consolidation snapshot.  Its hash generally differs from the original
   source hash.
3. **Retained historical PDF** means the PDF member from the arrival ZIP.  The
   filed PDF at the snapshot has the same bytes.  Since the notation migration
   changed TeX without rebuilding PDF, the PDF is not asserted to render the
   current source.

The six package-local `SHA256SUMS` files are derivative two-row ledgers, not
additional research payloads.  They are therefore outside the twelve-payload
closure (six TeX files and six PDFs).  This file, `SOURCE_DISPOSITION.csv`, and
`SOURCE_CLOSURE.sha256` are likewise consolidation metadata rather than source
manuscripts.

The stable source identifiers used below and in the disposition ledger are:

| ID | Filed directory | Arrival archive |
| --- | --- | --- |
| `CCC-2` | `Combinatorial_Coefficient_Calculus-2/` | `Combinatorial_Coefficient_Calculus-2.zip` |
| `CCC` | `Combinatorial_Coefficient_Calculus/` | `Combinatorial_Coefficient_Calculus.zip` |
| `CFIT` | `Combinatorial_Formulae_and_Inversion_Theorems/` | `Combinatorial_Formulae_and_Inversion_Theorems.zip` |
| `UCCC` | `Unified_Combinatorial_Coefficient_Calculus/` | `Unified_Combinatorial_Coefficient_Calculus.zip` |
| `UCF` | `Unified_Combinatorial_Formulae/` | `Unified_Combinatorial_Formulae.zip` |
| `UCFIT` | `Unified_Combinatorial_Formulae_and_Inversion_Theorems/` | `Unified_Combinatorial_Formulae_and_Inversion_Theorems.zip` |

All paths in the records below are repository-relative.  Archive paths have
the common prefix
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/incoming/`;
filed paths have the common prefix
`Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/`.

## Exact source records

### `CCC-2`

- Arrival ZIP: `Combinatorial_Coefficient_Calculus-2.zip`; Git blob
  `9034ceec1a65fa952e3c02eccb6d7c362b3ffab5`; 1,096,487 bytes; SHA-256
  `a0ca605c1d3f1ee3e00eac1d69a8181e786dd414407a1b3b6db1a60f74d8766d`.
- Original TeX member: `Combinatorial_Coefficient_Calculus.tex`; 262,054
  bytes; SHA-256
  `7952fc6161f983080cece0b23ab2f21966154c5fd10f64fbd1ec28d04c82c908`.
- Current TeX at the snapshot: 277,653 bytes; SHA-256
  `0b4176a295b8a1893d3a3b5b5c0cf7462f4d78931048735d11ab7c8d238c93f6`.
- Retained historical PDF: `Combinatorial_Coefficient_Calculus.pdf`;
  1,037,202 bytes; SHA-256
  `89e17636583c4ff64dcd1371d9ffcbd97094244cd28dbbae06f62e7f0d179a5b`.

### `CCC`

- Arrival ZIP: `Combinatorial_Coefficient_Calculus.zip`; Git blob
  `592357de555ae9803c8e0344582664c05ce6f860`; 1,094,284 bytes; SHA-256
  `a22479ac8f58e1710117af9d0a3f515c7d24ec250548f537520c9f9024f4321a`.
- Original TeX member: `Combinatorial_Coefficient_Calculus.tex`; 260,000
  bytes; SHA-256
  `09339c5829878aca14da8d1f87afdfce690dfe22642e94dc6c1cf0d0d8650f97`.
- Current TeX at the snapshot: 276,828 bytes; SHA-256
  `98497684f57b9f0b90f47e03ec5ddbd353ebdb8d336776a7837ba71d4e2ff63f`.
- Retained historical PDF: `Combinatorial_Coefficient_Calculus.pdf`;
  1,035,537 bytes; SHA-256
  `3f8da53a60368c76b6c126410a6142a920ef34931b6e90de69c856e3ba3562ad`.

### `CFIT`

- Arrival ZIP: `Combinatorial_Formulae_and_Inversion_Theorems.zip`; Git blob
  `66b3ded5b68fa30642ec9a9a98986014c6a25b96`; 1,101,493 bytes; SHA-256
  `dae561780a4442a9f11acb7edf1ec508daca1db237db01fabf77c695ec924960`.
- Original TeX member: `Combinatorial_Formulae_and_Inversion_Theorems.tex`;
  267,006 bytes; SHA-256
  `0eb7112348e8c145777998a00a0938a891b39f5232147bfbecbfad04b501ae04`.
- Current TeX at the snapshot: 283,111 bytes; SHA-256
  `f070ad0982dfb0a9cc550caecd3207c64cdb4287b293a029d4a17ca3cd4670b3`.
- Retained historical PDF:
  `Combinatorial_Formulae_and_Inversion_Theorems.pdf`; 1,039,362 bytes;
  SHA-256
  `0e0d2aea0d3e235dfeb07a787173a1575dbae93a47e8c5648fe199f2cd2fe509`.

### `UCCC`

- Arrival ZIP: `Unified_Combinatorial_Coefficient_Calculus.zip`; Git blob
  `eca796443cffda894141a1c8915b33b967585a6e`; 1,083,495 bytes; SHA-256
  `c4217b088444eb3e4bf24a7542d360f02dfb8e240418b562a155ad0c251ab559`.
- Original TeX member: `Unified_Combinatorial_Coefficient_Calculus.tex`;
  248,460 bytes; SHA-256
  `6e889b9f2a18cc206626885058916e5cd08bf7f5702ff2d280b6d3e1196ad04c`.
- Current TeX at the snapshot: 262,376 bytes; SHA-256
  `9566ce29854acdaca07ae07d13a7982d42f28c1d94c02911ee32da8d4c8f8947`.
- Retained historical PDF: `Unified_Combinatorial_Coefficient_Calculus.pdf`;
  1,028,631 bytes; SHA-256
  `f51f9bb147afa08613f38246db281ec03f8026b14fd1c48aa65169dcce82ddcc`.

### `UCF`

- Arrival ZIP: `Unified_Combinatorial_Formulae.zip`; Git blob
  `94bc569a8ef72c70435d02bff9eedf0c125553e0`; 1,015,842 bytes; SHA-256
  `611b14cfda15357b679a05d9586811d8fb39f6fe7d971f00424da2bb848a5594`.
- Original TeX member: `Unified_Combinatorial_Formulae.tex`; 219,612 bytes;
  SHA-256
  `0e3e1b79389f65ab0e22c64b18690d25a849d53898f5360ec832aed3be97c70d`.
- Current TeX at the snapshot: 232,717 bytes; SHA-256
  `089c6ece0009249a3f21648d9b2ef61da7ed02c0d8bfd7f54aca491a8cc81bb3`.
- Retained historical PDF: `Unified_Combinatorial_Formulae.pdf`; 966,943
  bytes; SHA-256
  `968c6a9aec61605f55e981841d123742f052ce4a4c53ab0c271d29e226d19c0d`.

### `UCFIT`

- Arrival ZIP: `Unified_Combinatorial_Formulae_and_Inversion_Theorems.zip`;
  Git blob `dd621f223220ab44825d9b3de72ed40b504f5463`; 1,062,893 bytes;
  SHA-256
  `ba62d0653fba9f0d1d867885e0b45272ba128973c1e49938d6cb1f597b457e33`.
- Original TeX member:
  `Unified_Combinatorial_Formulae_and_Inversion_Theorems.tex`; 243,109
  bytes; SHA-256
  `9b4c2d63ac0d93820d18ee2ab3eb03f1253baac87a395a2364bf712701e70775`.
- Current TeX at the snapshot: 257,216 bytes; SHA-256
  `7f41ee4b71c4d59e08d06eed1333e0adabcb60f40a00ee1ffca2f6b8d12417b2`.
- Retained historical PDF:
  `Unified_Combinatorial_Formulae_and_Inversion_Theorems.pdf`; 1,007,648
  bytes; SHA-256
  `a6d53f1a86c0ce11a0c7c6227cc5e2dfa357fa310db7108fb958bfb1ff4b4979`.

## Reproduction and verification

From the repository root, the twelve live snapshot payloads are checked with:

```text
sha256sum -c Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Combinatorial_Coefficient_Calculus/SOURCE_CLOSURE.sha256
```

The active rows in that file are conventional `sha256sum` rows.  Its commented
`HISTORICAL_*` rows identify data that no longer has a live filesystem path.
To reproduce one historical record, obtain the ZIP by its Git blob ID in a
binary-safe shell, verify the archive, and stream the named member:

```text
git cat-file blob <archive-git-blob> > <archive>.zip
sha256sum <archive>.zip
unzip -p <archive>.zip <member-name> | sha256sum
```

The same original member can be checked without the ZIP against its filed Git
blob at the extraction commit:

```text
git show d1d5c71e6a8b6aafa751ab5be816e5931b6a50fa:<filed-path> | sha256sum
```

Use a binary-safe pipe for the PDF form of the last command.  The archive Git
blob IDs, member names, byte counts, and expected hashes are given above and in
the commented historical records.  This gives two independent Git routes to
each original TeX/PDF identity: through the arrival ZIP and through the filed
extraction commit.

No command above establishes current-TeX/PDF render parity, mathematical
correctness, proof completeness, or Lean verification.  Those are separate
publication and formalization gates.
