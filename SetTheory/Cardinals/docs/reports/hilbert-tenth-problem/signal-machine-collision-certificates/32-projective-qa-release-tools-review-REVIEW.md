# Independent review of Report62 release tools

Date: 2026-10-04 UTC

## Verdict

**ACCEPTED at the exact final source pins below, within the stated release-tool scope. No unresolved correctness or execution-boundary blocker was found.**

The review independently executed 127 checks, comprising 97 supplemental authentication/schema/path/raster/archive checks, 29 actual-report build/environment/roundtrip checks, and one explicit shell-escape check. The final owned 39-case selftest suite was also independently rerun successfully. The latter remains author-authored testing, distinguished from the 127 independent checks.

Two findings were returned to the implementation owner and corrected before acceptance: inherited temporary-directory variables could mutate a frozen directory, and a manifest could name its reserved manifest filename as a directory. Both corrections were inspected and tested at the final pins. No frozen original was changed. All scientific programs, prior constructors, upstream code, simulators, saved schedules and Lean files remained inert. The independent scientific checker was also inert in this review; its separately reviewed portable replay was checked for unchanged integration and transport.

This review is not manuscript/math approval or human all-page visual approval. The actual 22-page report was used to test the release pipeline and every generated page PNG was checked structurally. The final distribution must be resealed after this dossier and any later manuscript/visual evidence are assembled.

## Exact accepted revision

| Item | SHA-256 |
|---|---|
| `tools/build_report62.py` | `b4bccb4f71120978746845adab454bff3a50dca03e6b13c010359644ffb8813b` |
| `tools/release62.py` | `60c40588d569943e64246011f65e77379c18eb3b405eec6a3df082b8ad9a74d8` |
| `tools/selftest62.py` | `6ba27fb4acf99401d5c43008b6c75d23eb43a778b79e3ec71d4a496f8deab362` |
| `tools/BUILD_DEPENDENCIES_LOCK.json` | `59ee80be4c4ff42f68e6b3613da2010f52831d34c65915a71cb6098d92c648e9` |
| `manuscript/MANUSCRIPT_PINS.json` | `643c37451af5fb280f9da64ab45ca26eef7a1f39c8fce71a24d3e5675df1adf3` |
| `Report62.tex` | `3e7a002438b86eae5ef0a4156899185926ce9c838e9ac5ad466164fb52f0283d` |
| `Report62.pdf` | `1051897d89f648725ecb8c22634c67738606a7a07da9cfeeb973720c50b8f560` |

`FINAL_SOURCE_PINS.json` also records frozen input-map, integrated replay and unchanged checker pins. The bootstrap PDF cited when this review began belonged to an earlier manuscript pin-map; it is not confused with the accepted 22-page candidate above. Both the hostile-environment build and the subsequent relocated locked rebuild reproduced the candidate PDF byte-for-byte.

## Findings and resolution

### 1. Inherited temporary directory could modify protected input metadata

At initial builder hash `8c2bd19631e2825ee60d80bc0c839216b5899957a7c816243ca38e3fac48b357`, `TemporaryDirectory` inherited `TMPDIR`, `TEMP` and `TMP`. A disposable release copy with `TMPDIR` pointing inside its frozen science root created and deleted the TeX workspace there. The build then rejected the changed release, but the frozen directory's nanosecond mtime had already changed. Evidence is in `FINDING_1_ORIGINAL_TMPDIR_RESULT.json` and its stdout. Only a copy was affected.

The owner anchored the temporary workspace with `dir=out`, after the output is validated as a fresh canonical external directory. The final owned suite independently tested all three temporary variables separately. The independent actual-report test combined all three with hostile Python, executable-search, home, TeX, epoch and timezone settings, using space/Unicode source and output paths. It passed, preserved the complete input snapshot, produced the expected PDF, and executed no trap module or trap executable.

### 2. Reserved manifest path accepted as a directory

At initial release-helper hash `6ac7b8bcef3d9211d17f62f0284188515c026922dc3a566df4f356c61b2f701c`, the schema accepted `RELEASE_MANIFEST.json` in the directory inventory with a child file. That is inconsistent with extraction's required manifest file. The owner changed validation to reject the reserved name in either inventory and updated the builder's helper pin. An independent malformed-schema regression and the owner's new regression both reject it at the final revision.

## Static assessment

### Frozen authentication, path guards and stable reads

- The helper authenticates `INPUT_PINS.json` against a literal inspected SHA-256 before parsing it. The complete 26-file frozen inventory is compared, including science, the original independent audit, and dependency proof/provenance files. Original frozen root and nested directory mode/mtime rows are included. The newly introduced wrapper directories are release metadata, not claimed original scientific metadata.
- Every file in the frozen pin-map was individually corrupted in a disposable clone with its original length and mtime restored. Every case failed authentication. Frozen directory mode changes, a missing file, FIFO, extra empty directory, symlinks, internal and external hardlinks, modified pin-map and unexpected files were rejected across the independent and rerun owned suites.
- The canonical path checks reject relative paths, traversal, duplicate separators, dot aliases, trailing separators, symlink components and existing/dangling-link outputs. Output overlap with the release or protected original roots is forbidden. Complete tree traversal rejects nonregular entries and aliases.
- Single-file reads require a single-link regular file, use `O_NOFOLLOW`, and compare device, inode, full mode, link count, length, nanosecond mtime and ctime around open/read. A controlled intervening-write probe was detected. Aggregate release snapshots compare byte hashes, lengths, file/directory modes and nanosecond mtimes; they do not purport to retain every possible filesystem attribute.
- The nine manuscript files must flatten deterministically into the standalone source under an externally supplied pin-map digest. Separate modular and standalone corruption cases failed before output creation.

### Build isolation, lock and recorder accounting

- The builder refuses optimized Python and requires `-I -S -B`. It loads the owned helper only after verifying the helper's literal source hash. No scientific source is imported or executed.
- Subprocesses use fixed absolute TeX/Poppler executable paths and a small constructed environment. A fresh format is generated with INITEX in the fresh external workspace; the build does not reuse an ambient pdflatex format. Shell escape and automatic bitmap/font generation are disabled. Three document passes are made.
- A controlled synthetic manuscript asserted that the actual `pdfshellescape` primitive was zero in all three passes and attempted a harmless marker-producing `write18`. The primitive assertion passed and no marker appeared. This is `SHELL_ESCAPE_RESULT.json`, not a general sandbox claim.
- The dependency lock is authenticated by its external digest before TeX starts. Executable identity includes the running Python binary, TeX binaries, `kpsewhich`, and the Poppler binaries. All locked system-input bytes are checked before launch. Executables are checked again before every command and after rendering.
- Four recorder files are retained separately: fresh-format generation and all three TeX passes. First-pass-only dependencies are included, as exercised by the synthetic `ifthen.sty` case. On the actual report, the independent union reconstruction found 269 recorder-union paths plus five selected font maps, exactly the 274 lock entries.
- Post-build dependencies were byte-identical to the preflight lock. Tampered executable hash, input size, outside-root input, extra top-level fields and malformed system-input inventory failed preflight. Adding a valid but unused locked system input failed the post-build exact-union check and produced no success receipt. An omitted first-pass-only dependency was rejected in the owned suite.
- Bootstrap success is explicitly labeled `BOOTSTRAP`, never lock-verified `PASS`. This review used locked builds for the candidate report and relocation result.

### PNG and PDF evidence

- The candidate PDF rebuilt to exactly 22 pages and matched the packaged PDF. All 22 PNG names and numeric page indices were checked against the PDF count. Independent parsing also rechecked each chunk CRC, IHDR format, decompressed RGB raster length, row filter values and inventory hash/size/dimensions. This was repeated for all 22 relocated-build PNGs.
- Adverse PNG tests covered CRC/truncation/trailing data, duplicate/missing/reordered chunks, missing image data or IEND, invalid raster lengths and filters, multiple zlib streams, unknown chunks, zero dimensions, invalid density and unsupported formats. A valid split-IDAT image passed.
- The builder rejects final overfull boxes and unresolved-reference/rerun warnings. Human layout judgment and mathematical/content approval remain separate review responsibilities.

### Sealing, archive and relocation

- Manifest validation is strict about object fields, canonical relative names, integer types, modes, sizes, timestamps, lowercase hashes, directory closure, file/directory overlap and the reserved manifest path. Duplicate JSON keys are rejected.
- Manifest generation excludes the manifest's own bytes and release-root metadata by design. All other files and subdirectory metadata are inventoried. The reserved manifest file receives fixed extraction metadata because its own metadata cannot be self-authenticated by this scheme.
- Repeated archives of the actual report candidate were byte-identical: SHA-256 `4a8eda323f70d823aee46e8f160b9ce464645ed0d599779a6edf48ea44f50fe0`. Their size was 10,768,169 bytes. The source candidate manifest digest was `7a64e2b269de36a0615ff444c6baa5146d685b2e2541a7b55e8b6cbd140bc87c`. These are diagnostic candidate seals, not the eventual release seal after later evidence is added.
- The extractor authenticates the manifest with the supplied external pin before writing, checks exact sorted ZIP membership, payload hashes/lengths, regular-file types, modes and CRCs, then restores directory/file modes and nanosecond mtimes. Duplicate, absolute/traversal, symlink-mode, wrong-mode and changed-payload ZIP cases failed before output creation.
- The actual archive was extracted to a new space/Unicode path. Its manifest verified, all authenticated metadata roundtripped, and the locked 22-page PDF rebuilt byte-identically. Preservation snapshots before/after both actual builds are byte-identical.

### Portable replay integration

The integrated and archive-relocated `tools/portable-replay/` file inventories were compared byte-for-byte with the separately reviewed 23-file replay packet. `replay.py` remains `d1917acf7ef7880e874d2e302095b893ddb2a2001b3e8d9f33119a50e9d29ba2`; the independent checker remains `a945491e115e5f96dfc11e3d6e714ef367ecc0daddfce425d8310cb5949f4fec`. Its documented explicit science/audit/pins/output interface is compatible with the relocated release layout. This review did not modify or rerun that checker and relies on its separately supplied source-bound replay review for mathematical-evidence replay behavior.

## Preservation and limits

The independent original-input before/after snapshots are byte-identical. They cover 17 science objects, 11 independent-audit objects, 82 Report60 objects and 13 Report61 objects, including roots. The independent snapshot tuple includes device, inode, full mode, link count, size, nanosecond mtime and every regular-file hash. Reads may affect atimes, which are deliberately omitted.

The trust boundary remains important:

1. The reviewed source bytes, externally supplied pins, installed interpreter, standard library, operating system and quiescent POSIX filesystem must be trusted. A digest distributed only beside an untrusted artifact is not independent authentication.
2. The lock covers executable bytes and the selected recorded TeX inputs/maps. It does not inventory dynamic libraries, Python's standard library, the kernel or all operating-system state.
3. These tools are not an OS/network sandbox for arbitrary hostile Python or TeX. The manuscript, helper and recorded system packages are reviewed/pinned inputs. Before/after checking does not prove safety against concurrent adversarial writes, mount changes, or change-and-restore races.
4. Failed builds may retain their fresh output for inspection; they have no success receipt. Some severely malformed schema types produce an ordinary nonzero Python traceback rather than the friendly refusal diagnostic; the tested case remained fail-closed and created no output.
5. This acceptance is bound to the exact sources and demonstrated manuscript/dependency pins. Manuscript/package changes need fresh applicable build/lock review; tool changes need source-bound re-review. Later ordinary evidence additions require a new final manifest and archive, not reuse of the candidate seal above.

## Evidence and safe integration

This is a clean flat dossier. Copy only the regular files listed by `REVIEW_MANIFEST.json`, together with that manifest and `SHA256SUMS.txt`, into `qa/release-tools-review/`. Do not copy the external diagnostic workspace: it deliberately contains malformed ZIPs, hardlinks, symlinks, FIFOs, corrupted inputs and temporary fixtures.

The retained independent test-source files document how the reported results were obtained. They expect the original external diagnostic workspace and prepared fixture layout; they are not standalone end-user entrypoints from inside `qa/`. The release's own documented selftest command remains the supported fresh-fixture regression entrypoint. The copied results embed individual outcomes and relevant stdout. Final source pins and the review receipt are explicit and machine-readable.
