# Batch 80 corrected-edition placement: 8a4e64732

**PASS for byte transfer.** All **21 added or modified non-ZIP files** in `8a4e647326e8c92f53e222c10e9107b40918a1ff` are byte-identical to their intended corrected-package members: 13 existing supplements are replaced, and eight supplements are added. There are no unmatched code, data, correction-note or provenance changes. The three corrected archives removed by this commit exactly match the arrivals at `4e270aa4648c5fd7e18626507531046715976535`; their bytes remain available from Git.

The maintained application/marking/polynomial boundary repairs are now present. The placement keeps the historical flattened, prefixed supplemental layout; it does **not** turn that layout into the original directly runnable releases. This is a packaging limitation, not a failed source transfer or a new arithmetic defect.

[Portable checker](review_batch80_corrected_placement_8a4e64732.py) and [complete receipt](review_batch80_corrected_placement_8a4e64732.json) authenticate immutable Git blobs only. No archive source is imported or executed, no author suite is rerun, and no working-tree file or Git state is changed. The earlier [corrected-package review](review_batch80_corrected.md) contains the mathematical/API scope and targeted normal/optimized replays. This audit does not repeat or enlarge that review.

## Pins and comparison boundary

The checker uses full immutable commit IDs:

- Corrected archives: `4e270aa4648c5fd7e18626507531046715976535`.
- Placement: `8a4e647326e8c92f53e222c10e9107b40918a1ff`.
- Immediate placement parent: `37652b3e60a676e119746f5b874147cb4d9e1d2b`.
- Original uncorrected archives: `aebfa386e44f232be06b546be9fc2f6138ad34f2`.

| Corrected archive | SHA-256 |
|---|---|
| `Eager_Tree_Calculus_Research_Package_corrected.zip` | `2c053f50027ec632c2773c9d2ec3e2ace9f621eef5c08bebce0ca06c2d0f3dbd` |
| `Reset_Petri_Net_Certificates_corrected.zip` | `8d5b9b1a52c33aeadb8b4200fd9c138bd016f2651ebcfccf1a939e03715486d3` |
| `Sparse_Lattice_Diophantine_Certificates_corrected.zip` | `cf9b546baaece745c047f6ce33574d10104f03c9849f4114626a916c1deec1e2` |

The full 24-path placement delta is asserted: 21 supplemental additions/modifications and exactly three archive removals. There is no `.gitattributes` change in this commit. All three assembled `article.tex` files, all three assembled `article.pdf` files, and all three report READMEs are byte-identical to the immediate parent. Their exact hashes are included in the checker and receipt. This statement is pinned to this placement commit, not a claim about later editorial changes.

All eleven original package manuscript/PDF members are also unchanged between the old and corrected archives: Tree Calculus has one TeX and one PDF; reset nets likewise; sparse lattices have six TeX sources and one PDF. Thus this placement introduces neither a typesetting change nor a changed theorem source. It does not itself establish any new theorem or operation bound.

## Complete package-qualified mapping

The receipt maps each maintained path to explicit member paths of the intended package. It does not infer provenance from a coincidentally equal file in another package. Every file currently carrying the relevant package prefix at the placement commit is included, including the 124 unchanged supplemental files.

| Package / maintained report | Corrected members | Maintained files | Source member paths served | Archive-only members | Modified / added files |
|---|---:|---:|---:|---:|---:|
| `21-eager-tree-` / canonical-diophantine-certificates | 58 | 53 | 53 | 5 | 4 / 2 |
| `17-reset-net-` / quadratic-orthant-certificates | 87 | 54 | 54 | 33 | 4 / 3 |
| `13-sparse-lattice-` / signal-machine-collision-certificates | 52 | 38 | 39 | 13 | 5 / 3 |
| **Total** | **197** | **145** | **146** | **51** | **13 / 8** |

The sole extra member identity is the established sparse-lattice alias: `replay/core/morita_audit.py` and `replay/morita/audit.py` have identical bytes and are represented by one maintained `code/13-sparse-lattice-morita_audit.py`. No member is assigned to two maintained files. Cross-package copies of reset-net source tables remain outside its package-qualified placement coverage.

The commit-message count of “170 [unchanged] members, 124 identical to files already shipped, 46 not shipped” mixes physical files with original member identities. The exact split is **125 unchanged member identities served by 124 files, plus 45 unchanged omitted member identities**. The remaining six omissions are the three changed delivery READMEs and three refreshed manifests. Consequently `146 + 51 = 197` is the complete corrected-member ledger. This is a provenance-count clarification; no delivered bytes are missing relative to the intended supplemental changes.

The checker authenticates all 197 corrected member hashes and all **194 checksum entries** (57 + 86 + 51); each manifest covers every member except itself. Overlaying every authenticated maintained file onto its prescribed original member location reconstructs the full corrected archive dictionary exactly. This reconstruction is checked in memory, including the duplicate audit path; the helper neither extracts files nor executes the reconstructed packages.

## Repairs that are now maintained

The placed corrected bytes carry the already-reviewed repairs:

- Tree `Evaluation.app` rejects arguments outside exact natural Python integers before cache lookup or mutation. `code/21-eager-tree-tree_kernel.py` and the new application-domain suite match the corrected archive. The revised `reproduce.py` and two source-hash receipts match too.
- Reset `compile_peak` validates exact Boolean duration flags; `fire` validates exact natural markings and recognized place names; `initial` uses explicit natural-counter validation. Both implementation modules, the new boundary audit and receipt, the updated runner, and the refreshed provenance receipt match.
- Sparse `Poly` enforces the exact immutable canonical representation at direct construction. Its implementation, added exactness suite/receipt, runner, source-provenance note and two refreshed receipts all match.

All three newly placed `CORRECTION.md` files are exact archive members. No optional research optimization or broader schema hardening is included. Earlier review notes describing these defects or patches as unapplied describe their own pinned historical versions; they should not be read as saying that the current placed implementation is still uncorrected. The combined articles/READMEs were not revised by this commit.

## Omitted companions and runner layout

The 51 package-qualified omissions are explicitly listed in the receipt. They are recoverable from the pinned corrected ZIPs, not lost from Git:

- Tree, five: the delivery README, original TeX/PDF, `verify_manifest.py`, and `MANIFEST.sha256`.
- Reset, 33: delivery/check README files; original report TeX/PDF; `SHA256SUMS` and `verify-manifest.py`; original source-table/proof dependencies; and the unplaced large schemas, alternate nets and fixtures. Some source bytes are present under another report's package prefix, which does not restore the reset package's required paths.
- Sparse, 13: delivery README and `SHA256SUMS`; six original paper sources and the PDF; two compressed Morita fixtures; `replay/package_release.py` and `replay/verify_manifest.py`.

The placement intentionally retains the authors' source bytes, including original relative-path assumptions. Static checks provide eight concrete path witnesses:

1. Tree's moved `code/21-eager-tree-reproduce.py` still defines its root as its own directory and then uses `ROOT / 'code' / step` (line 29). In the maintained layout this seeks a nested `code/code/` and unprefixed scripts. The new domain test still defaults to its unprefixed sibling `tree_kernel.py` (line 16).
2. Reset's moved shell runner still invokes unprefixed `build_net.py` from its own directory (line 7), and the new audit imports `build_net` and reads `source/virtual3.json` from the original root (lines 11 and 28). Those expected paths are absent in the flattened package projection.
3. Sparse's moved release runner still copies `ROOT/'replay'` (line 14), while its new constructor test imports unprefixed `sparse_mass` (line 20) and opens a sibling `fixtures/binary_three_way_collision.json` (line 147). Those original paths were not installed by the prefixed placement.

The helper checks the literals and absence of the resulting paths in the entire corresponding report tree at the pinned commit. These are source/layout findings, not results of executing failing runners. The three original manifest verifiers and their manifests are unplaced as well. Running the instructions quoted inside the unchanged correction notes requires restoring the **corrected archive's original layout** first. Merely dropping a corrected manifest beside flattened supplements cannot satisfy it.

This review does not modify the historical `a7ae02511` stager, whose original-source pins appropriately identify the earlier uncorrected release. Use the corrected pinned ZIPs for the new release rather than mixing their source guards with old manifests or receipts.

## Reproduction and limits

With the four pinned commit objects available locally:

```sh
python review_batch80_corrected_placement_8a4e64732.py \
  --repo /path/to/Proofs \
  --expect review_batch80_corrected_placement_8a4e64732.json
```

`--output PATH` writes the deterministic receipt. All checks use explicit exceptions, and saved-receipt comparison is recursively type-sensitive. The helper uses only the Python standard library and read-only Git commands, authenticates archive hashes before inspecting ZIP contents, and rejects unsafe/duplicate member paths and symlinks. It reads Git blobs rather than the mutable working tree. No recovered module import, mathematical suite, PDF build, extraction, or repository mutation is part of this bounded audit.

## Root integration check

Root read the complete frozen checker and review, then reproduced the full
saved receipt in a fresh process using immutable Git inputs. The newly written
receipt is byte-identical. The original sources and report presentation remain
unmodified by this audit.
