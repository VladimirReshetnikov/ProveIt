# Independent Report64 release-tool review

**Verdict: PASS for the exact helper bytes and candidate-d bindings below. No blocking release-tool defect was found.** Review and tests completed 2026-10-04 UTC. This is an integrity, preservation, typesetting, archive and relocation review, not a mathematical/scientific audit.

## Exact acceptance bindings

| Accepted item | SHA-256 |
|---|---|
| `tools/release64.py` | `bf711f81494ecefc5ffeeb06fe5eb0795aefc3aaace644d8570ab7a486b0b45e` |
| `tools/build_report64.py` | `0467642900bbafd50c1046f0ba67b9ca2177126e45756f71fd887979f533e1e5` |
| `tools/selftest64.py` | `9d2123843e6b462d04596f565eceaf77c9c465f39349e4a80e8a77c7be9f70e5` |
| `INPUT_PINS.json` | `470faccf57b8c81849934c6167b90f48f9cc0989fd07d07647d5b415c7275e43` |
| `manuscript/MANUSCRIPT_PINS.json` | `cba694ca6bb470c100a0216584bfc198837c2668564eb338767922daee1999db` |
| Standalone `Report64.tex` | `52618709e5354630dacf5c33f18595605f6a8dd4e6d5ea1f6f44bc4bbc8a886e` |
| Packaged/rebuilt `Report64.pdf` | `c86cb407ffb93a37625d0d0a25e86bf2d0434eaee1104e3059a3b002d0210608` |
| `tools/BUILD_DEPENDENCIES_LOCK.json` | `0c8f1c05079b13f29f5b49d0da33a681c02552131dcac81e65af8aa6afb1be69` |

`ACCEPTED_BINDINGS.json` is the machine-readable binding. The full accepted input, manuscript and dependency pin maps are included separately. The input map covers **31 files and 9 internal directories**, including these five required subtrees: `science/frozen-proof`, `science/arithmetic`, `audits/physical`, `audits/arithmetic`, and `dependencies/proofs`.

## Method and results

The reviewer read all three complete helpers before execution, compared the adaptation against the inspected Report63 implementations, and waited for final authenticated embedded input/helper constants. Only release-only tools and ordinary TeX/PDF/PNG tooling were executed. No author/upstream mathematical program, native counter interpreter, physical simulator, saved collision schedule or Lean program was run. Scientific Python files were inert copied bytes throughout.

All mutations and outputs were in new external expendable fixtures. The deliverable directory contains only this review, test programs, accepted pin maps, compact receipts, preservation comparisons and its own manifest. It contains no recursive release copies, diagnostic ZIPs, rendered-page trees or synthetic fixture trees.

- **93 main checks passed**, including exact external authentication, independent frozen-tree inventory, independent eleven-module flattening, repeated preparation equality, actual locked PDF rebuild, adversarial cases, diagnostic archive/extraction, relocation, preservation and one invocation of the owned suite
- **13 supplemental boundary checks passed**, covering the isolation/no-site/no-bytecode/no-optimization interpreter requirements for each helper and rejection of an existing hardlinked output without changing its sentinel
- **39 owned selftests passed** in external fixtures, independently invoked after inspection. Their identity remains explicitly self-testing; their results are not substituted for the independently written checks above

Counts are test/compound-check labels, overlap in coverage, and are not additive scientific evidence.

### Fresh external outputs and preserved inputs

Existing output paths, relative paths, dot/dotdot/double-slash/trailing-slash aliases, release-overlapping destinations, every listed original protected source root, symlink ancestors, dangling symlink outputs and existing hardlink outputs were rejected. Source symlink/hardlink aliases, changed bytes, executable mode changes, one-nanosecond mtime changes, extra frozen files, empty directories and modified input maps were rejected. Tampered release-helper bytes were rejected by the builder before output creation.

The independent before/after comparison found the **entire reviewed release snapshot unchanged**, including root metadata, and all six protected original source trees unchanged. Every helper command also had an independent fixture-preservation comparison. The main receipt and `PRESERVATION_COMPARISONS.json` bind these comparisons to exact inventory hashes. Owned hostile `TMPDIR`, `TEMP` and `TMP` tests additionally confirmed that build temporary files stay under the external output.

### Dependency authentication, PDF and PNG

The locked build created a fresh TeX format with no shell escape and reproduced the accepted **21-page PDF byte for byte**. The reviewer independently reconstructed the four retained recorder sets (format and three document passes), added the five selected font maps, and obtained the exact **271-input** dependency union. Every locked system input was rehashed; the emitted dependency receipt equaled the preflight lock byte for byte.

An independently authored synthetic manuscript loaded `xspace.sty` only on document pass one. Its dependency remained in the union even though absent on the final pass; a lock omitting it failed when the first-pass recorder was checked. Incorrect external lock pins, stale executable hashes and stale system-input hashes were rejected before creating the build output. Bootstrap is correctly reported as BOOTSTRAP, not verified-lock PASS.

All 21 rendered PNGs were independently parsed and checked against the recorded page inventory, including signatures, chunks/CRCs, RGB dimensions, decompressed raster sizes and row filters. The public validator rejected malformed signatures, truncated/trailing bytes, CRC corruption, bad dimensions/color/depth, short/long rasters, invalid filters, extra zlib streams, unknown/duplicate chunks and invalid density metadata.

### Archive and relocation

The reviewed **diagnostic fixture snapshot**, before this review is added to the publication, was sealed and verified. Two archive operations produced identical ZIP bytes. Extraction independently restored 59 payload files and 16 internal directories with exact file bytes, modes and nanosecond mtimes, plus the manifest bytes. The extracted tree verified at a different path, and its locked rebuild again produced the accepted PDF exactly.

Invalid manifest paths, unsafe modes/types, invalid sizes/timestamps/digests, self-reference, extraneous directories, a manifest-directory collision and duplicate JSON keys were rejected. Extraction rejected extra/traversal entries, duplicate ZIP entries, changed payload bytes, wrong modes, symlink entries and an incorrect external manifest pin before creating the destination.

**Diagnostic fixture manifest SHA-256:** `f0c7eac21e3eac7a360d72235449a272b65516bf05d74d5ac397b41989a338cd`  
**Diagnostic fixture ZIP SHA-256:** `1804b9403d84091d0c822e576710b062fcbd13adebc828f81ed5712d97ed990e`

These two pins authenticate only the tested fixture snapshot. **They are not the final publication manifest/archive pins.** Adding manuscript/tool review evidence changes the publication inventory. The final publication must generate and verify its own manifest and archive after assembly.

## Scope and limitations

- SHA-256 pins are integrity commitments relative to the separately supplied accepted pins, not signatures or proof of mathematical claims
- `INPUT_PINS.json` verifies file/internal-directory inventories below `science`, `audits` and `dependencies`; the metadata of those three containing scope directories is not part of that input-map comparison. Operation snapshots and the whole-release manifest cover a broader tree. The archive manifest does not prescribe the extraction root directory's own mode/mtime
- The build lock covers interpreter/executable bytes, every recorded format/TeX-pass system input, and selected font maps. It explicitly excludes shared libraries, the Python standard library and the operating system. Relocation was tested under the matching locked Linux toolchain, not on arbitrary platforms
- Determinism was established by exact repeated archive and PDF equality in this environment. This finite review is not a proof against malicious concurrent filesystem/kernel manipulation or every possible malformed input
- Acceptance binds the helper bytes listed above. Changing a helper or embedded pin requires renewed exact-byte review; changing publication-only documentation requires a new final publication manifest but does not retroactively alter these test results

## Reproduction and evidence

Run `independent_review64.py` with `python3 -I -S -B`, providing `--release`, `--accepted-json`, `--work` (a fresh external directory) and `--dossier` (an existing external result directory). `supplemental_boundaries64.py` takes release-fixture, fresh-output and dossier paths. Their source is included. All original runs used expendable work outside both the accepted release and frozen source roots.

Primary evidence: `INDEPENDENT_TEST_RECEIPT.json`, `SUPPLEMENTAL_BOUNDARIES_RECEIPT.json`, `OWNED_SELFTEST_RECEIPT.json`, `ACTUAL_RELEASE_BUILD_RECEIPT.json`, `RELOCATED_BUILD_RECEIPT.json`, `DEPENDENCY_AUTHENTICATION.json`, `INDEPENDENT_PAGE_INVENTORY.json`, `ARCHIVE_AND_RELOCATION_RECEIPTS.json`, and the preservation summaries/comparisons. The expected duplicate-entry ZIP warning in the concise run log comes from constructing the deliberately invalid archive fixture; extraction correctly rejected it.
