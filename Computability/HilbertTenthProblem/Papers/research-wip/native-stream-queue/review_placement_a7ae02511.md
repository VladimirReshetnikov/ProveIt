# Exact placement review: a7ae02511

PASS. All **246 added files** in placement commit `a7ae02511c5584086ef9152f92d59ba77efa6148` are byte-identical to members of their intended incoming packages. There are zero unmatched source, data or supplemental-document additions. The only modified nonarchive file is `SetTheory/Cardinals/.gitattributes`, which adds a comment and two `-text` rules for delivered CRLF CSVs. Seven ZIP files are deleted; they remain recoverable at parent commit `38edfb31e40af6aa99c9d552a47e111d3f3eb8da`.

This review authenticates placement and reconstructs original package layouts. It does not rerun mathematical proofs or author suites: no new source or data bytes were introduced by these additions. Previously identified defects and separately delivered patches retain their prior status; byte-preserving placement does not apply those patches implicitly.

[Inventory](placement_a7ae02511_inventory.json) records every added Git blob's size/hash, its package-qualified archive/member matches, all original member hashes, archive omissions, content aliases, and the exact `.gitattributes` delta. [Portable stager](replay_placed_substrates_a7ae02511.py) and [receipt](replay_placed_substrates_a7ae02511.json) authenticate the current placed files, recover the pinned original archives from Git, and restore complete private layouts. They execute no recovered source.

## Package-qualified mapping and unambiguous counts

The mappings use both the maintained filename prefix and exact member bytes. A file beginning `17-reset-net-`, for example, must map to the reset-net archive; a coincidentally identical member in the universal-membrane archive is not used as its placement provenance. The six prefix bindings are explicit and pinned in the inventory. Ambiguous same-package duplicates are explicitly listed, not chosen by ZIP iteration order.

| Intended package | Added maintained files | Original member paths served by those files | Other members recovered from Git | Full original file manifest |
|---|---:|---:|---:|---:|
| Corrected conservative signals (`12-conservative-signal-`) | 36 | 37 | 8 | 45 |
| Eager Tree Calculus (`21-eager-tree-`) | 51 | 51 | 5 | 56 |
| Membrane motifs (`15-membrane-motifs-`) | 21 | 23 | 5 | 28 |
| Reset nets (`17-reset-net-`) | 51 | 51 | 33 | 84 |
| Sparse lattices (`13-sparse-lattice-`) | 35 | 36 | 13 | 49 |
| Universal membranes (`16-universal-membrane-`) | 52 | 54 | 18 | 72 |
| **Total** | **246** | **252** | **82** | **334** |

The difference between 246 maintained files and 252 original member paths consists of exactly six two-member aliases:

1. The membrane-motif focused receipt also equals its saved stdout record.
2. The membrane-motif quartic receipt also equals its saved export stdout record.
3. The universal-membrane `tm_table.json` is shared by the direct and packet frontends.
4. Its `virtual3.json` is likewise shared by those two frontends.
5. The sparse-lattice Morita audit script has identical original copies in `replay/core/` and `replay/morita/`.
6. The conservative signal machine JSON has identical original copies in `data/` and `numeric/`.

Thus six pairs of original member paths are represented by one maintained file each. Equivalently, each of those six maintained files restores two original paths. No original member is assigned to multiple maintained files. The stager validates all 252 member targets before overlaying them and compares every final restored root against its **entire original file manifest**.

An unrestricted hash-only census would find 261 active archive member identities matching some added byte sequence and would report 73 omissions. That overstates placement coverage: nine reset-net source members happen to equal files placed under the universal-membrane prefix. Those nine cross-package equalities are recorded separately and are not treated as reset-net placement. Consequently the package-qualified number of Git-only restored members is **82**, with `252+82=334`; 73 is not the stager's omission count.

Omitted members include original README/manifests, source manuscripts/PDFs, compressed fixtures, manifest/build utilities, and duplicate frontend source/generated data. The inventory lists every path. “Omitted” here means absent from this commit's package-qualified supplemental placement, not unavailable from Git or necessarily absent from every earlier maintained document location.

## Seven archive removals, six restored roots

Both old and corrected conservative-signal archives are removed. They share the extraction root `conservative-signal-release`. The original contains 38 files; the corrected archive contains 45. Thirty-six old members are unchanged, `SHA256SUMS` and `code/quadratic_packet.py` differ, and seven members are newly supplied by the corrected archive. There are no removed old member paths.

The stager authenticates both ZIPs and every member but stages only the corrected version. It does not overlay the old evaluator or old manifest onto that root. The older ZIP remains recorded as superseded provenance. Across all seven archives, **372 original file members** are authenticated; the six active layouts contain **334 files**.

| Removed archive | SHA256 |
|---|---|
| `Conservative_Signal_Diophantine_Frontend.zip` | `43eaf888d4d93942ab7cf311bcc2f53a1853efa0715805fb13cd14d706fa6f73` |
| `Conservative_Signal_Frontend_Corrected.zip` | `e2acf725fcf017e14b2705cc9097fa9e3eb8b02c2fc9faf8ce486d3614816990` |
| `Eager_Tree_Calculus_Research_Package.zip` | `5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4` |
| `Membrane_Motif_Research_Package.zip` | `47da14f271cccfb16fceb5cec859889a02d14e6ff5c23ca121f6f17a1ac98e99` |
| `Reset_Petri_Net_Certificates.zip` | `b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3` |
| `Sparse_Lattice_Diophantine_Certificates.zip` | `90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68` |
| `Universal_Membrane_Research_Package.zip` | `dc4fe8f07c278614d567029e40bbdf2db2326e5ea4b04f423bcc3b0b2610e3b5` |

## Repository metadata and staging checks

The `.gitattributes` modification consists solely of the `Batch 79J2` explanatory comment and these two attributes, relative to `SetTheory/Cardinals`:

```
docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/13-sparse-lattice-doubling-complete.csv -text
docs/reports/hilbert-tenth-problem/signal-machine-collision-certificates/data/13-sparse-lattice-false-signal-complete.csv -text
```

The delivered CSVs contain 17,577 and 9,262 CRLF line endings respectively, with zero bare LF line endings. Both current files match their source archive bytes. The stager checks the exact metadata delta at the placement commit and checks that the required lines remain present in the current checkout; later unrelated attribute additions are allowed.

The executed private staging run authenticated all archive/member pins, all 246 maintained files, all 252 qualified member mappings and the complete restored file sets/bytes for each of the six roots. It detected no path collision. The receipt records a deterministic full-member hash manifest digest per root. ZIP absolute paths, traversal, backslashes, symlinks and duplicate entries are rejected. Existing destinations are rejected; the stager does not overwrite another checkout or apply patches. Original file bytes and directory layout are restored; executable mode metadata is not part of this byte inventory, so shell scripts may be invoked through `sh`/`bash` as appropriate.

Default replay uses a disposable private directory:

```
python replay_placed_substrates_a7ae02511.py --repo /path/to/Proofs --expect replay_placed_substrates_a7ae02511.json
```

To retain the restored layouts, choose a destination that does not yet exist:

```
python replay_placed_substrates_a7ae02511.py --repo /path/to/Proofs --destination /tmp/placed-a7ae02511
```

The inventory defaults to the checker’s sibling `placement_a7ae02511_inventory.json`; `--inventory` can override that location without weakening its content pin. Both API and CLI receipts contain no absolute staging paths or timing fields. No author suite was rerun and no new mathematical correctness claim is inferred from the placement comparison.
