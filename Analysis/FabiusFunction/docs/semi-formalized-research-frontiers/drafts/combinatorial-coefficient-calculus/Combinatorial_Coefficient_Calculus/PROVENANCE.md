# Provenance and consolidation boundary

Six independently delivered manuscripts supplied the material consolidated into
this package. The five donor directories have been retired; their original
archives and their filed TeX/PDF pairs remain recoverable from Git. The canonical
source continues to evolve as proofs are repaired, strengthened, and formalized.

[`SOURCE_INVENTORY.csv`](SOURCE_INVENTORY.csv) records one row for each original
manuscript: its stable source identifier, filed package, immutable snapshot
commit, repository-relative TeX/PDF paths, archive Git blob, and archive member
names. These are recovery locators, not checksums of the current publication.
[`SOURCE_DISPOSITION.csv`](SOURCE_DISPOSITION.csv) separately records the
editorial decisions for each source, topic, and reviewed claim.

## Immutable intake chain

| Stage | Immutable commit | What the commit records |
| --- | --- | --- |
| Archive arrival | `c3720b763d159c3a009b66e6e89ac500b7843e98` | The six ZIP archives under `drafts/incoming/`. |
| Safe extraction and filing | `d1d5c71e6a8b6aafa751ab5be816e5931b6a50fa` | The original flat TeX/PDF pairs filed by theme, with the ZIP archives removed from the live tree. |
| Shared-notation migration | `729820bfe079947d1f1af7877820fbbb9202a1f0` | Changes to the six TeX sources; the arrival PDFs were not rebuilt. |
| Pre-consolidation snapshot | `55038f2fc7d20a483a48125f086a6c8488e45530` | The complete six-source input tree identified by `SOURCE_INVENTORY.csv`. |

The stable source identifiers are:

| ID | Historical package | Arrival archive |
| --- | --- | --- |
| `CCC-2` | `Combinatorial_Coefficient_Calculus-2` | `Combinatorial_Coefficient_Calculus-2.zip` |
| `CCC` | `Combinatorial_Coefficient_Calculus` | `Combinatorial_Coefficient_Calculus.zip` |
| `CFIT` | `Combinatorial_Formulae_and_Inversion_Theorems` | `Combinatorial_Formulae_and_Inversion_Theorems.zip` |
| `UCCC` | `Unified_Combinatorial_Coefficient_Calculus` | `Unified_Combinatorial_Coefficient_Calculus.zip` |
| `UCF` | `Unified_Combinatorial_Formulae` | `Unified_Combinatorial_Formulae.zip` |
| `UCFIT` | `Unified_Combinatorial_Formulae_and_Inversion_Theorems` | `Unified_Combinatorial_Formulae_and_Inversion_Theorems.zip` |

## Which source a record identifies

An **original source** is the TeX member of an arrival archive, also available
at the extraction commit. A **snapshot source** is the notation-migrated TeX at
the pre-consolidation commit. These are distinct revisions. The PDF at that
snapshot is the **arrival PDF**; it is not asserted to render the
notation-migrated source.

The **live canonical source** is the current TeX in this package. Its location
coincides with the original `CCC` manuscript's location, but its contents now
include the consolidation and subsequent work. The `CCC` inventory row always
identifies the historical snapshot, never the changing live source.

The earlier 174-page PDF was a historical consolidation render. Upstream
subsequently supplied a rebuilt PDF at its own checkpoint; that artifact is
retained, but the latest merged Stirling and Nörlund source edits postdate it.
No current render parity is claimed, and further PDF building remains skipped
in this work at the user's request. Render and compiler evidence are separate:
PDF parity and adjacent proof environments do not establish Lean verification.
Original arrival PDFs remain recoverable through the inventory's immutable
Git locators.

## Recovery and validation

The inventory provides two independent routes to the original material. To
recover an arrival archive, use its `archive_blob` value:

```text
git cat-file blob <archive_blob> > <archive>.zip
```

Read the named `tex_member` or `pdf_member` from that ZIP. Alternatively, recover
the originally filed member at the extraction commit:

```text
git show d1d5c71e6a8b6aafa751ab5be816e5931b6a50fa:<tex_path>
git show d1d5c71e6a8b6aafa751ab5be816e5931b6a50fa:<pdf_path>
```

Use a binary-safe shell or Git client when redirecting ZIP or PDF bytes. To
recover the notation-migrated source instead, use the inventory's
`snapshot_commit` and `tex_path`. No recovery procedure requires a standalone
checksum file. The retired checksum ledgers themselves remain in Git history.

From the repository root, run:

```text
python Analysis/FabiusFunction/docs/semi-formalized-research-frontiers/drafts/combinatorial-coefficient-calculus/Combinatorial_Coefficient_Calculus/validate_canonical.py --final
```

The validator uses the Python standard library and read-only Git object queries.
It checks exactly one inventory entry for each of the six inputs, safe and
expected repository/member paths, availability and type of the pinned Git
objects, and agreement with the six whole-source disposition records. It also
checks completed dispositions, the one-document layout, stale donor routes,
LaTeX structure, references, citations, and proof adjacency.

These checks do not compare current file contents with stored digests, rebuild
the PDF, or compile Lean. A successful run establishes the stated structural
and provenance checks only. Mathematical correctness and exact Lean coverage
remain separate obligations, tracked by the in-document formalization register.
