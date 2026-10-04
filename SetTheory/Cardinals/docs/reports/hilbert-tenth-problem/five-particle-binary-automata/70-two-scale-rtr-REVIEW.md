# Independent Report70 release-tool review

Disposition: **ACCEPTED. No required correction.**

The inspected Report70 release/build/selftest sources and their stated presentation-only workflow passed 116 independently written checks or operations: 83 intended rejections and 33 successful validations/operations. The complete 39-case author-owned selftest suite was also reproduced separately; its cases are not counted as independent checks. The primary receipt has 113 operations, one of which invokes that owned suite; the supplemental receipt has four additional independent checks, giving 113 − 1 + 4 = 116.

## Scope and method

The complete current README and all three current tool sources were read before execution and their supplied SHA-256 pins were verified. An independently computed normalized diff confirms that the retained Report66/68 implementations differ only in report identity, fixed input map, module names, protected source paths, pinned helper digest and synthetic fixture paths. No predecessor program was executed.

The main release was never modified. A fresh external candidate was copied with file/directory metadata, independently checked, and separately sealed. That snapshot contains 140 payload files and 21 descendant directories, including the manuscript-review material already present when copied. It does not contain this release-tool dossier or later final-release changes. Its candidate hashes must not be presented as the final release hashes.

Only the inspected presentation tools, independently authored test scripts and synthetic TeX were run. Scientific files, source interpreters/compilers, radius-two checkers, CA/physical/trajectory simulators, saved schedules, archived programs and Lean remained inert. This review establishes presentation/release behavior, not mathematical correctness or new scientific execution.

## Accepted evidence

- All 45 copied original source/audit files matched their original-path mappings in bytes, sizes, modes and nanosecond mtimes. Original file device/inode/ctime/link metadata also remained unchanged during the primary review. Six mapped original directories matched the frozen directory metadata.
- The manuscript flattening and external manuscript-map pin agreed exactly. The fixed input-pin map could not be replaced with a reformatted or newly repinned map, including a map made to match modified inert source data.
- Direct and authenticated relocated locked builds reproduced the packaged 21-page PDF byte for byte. Every rendered PNG matched between builds and the previously accepted v5 render. A separate reference parser independently verified all 42 PNG files' chunk CRCs, dimensions, RGB raster structure, deflate boundaries and row filters.
- All 275 recorded/selected system inputs and the executable records matched the dependency lock. Format and all three TeX-pass recorder files were independently reconciled with their recorded input sets and selected font maps.
- Fresh synthetic TeX retained the first-pass-only ifthen.sty dependency and 62 format-only dependencies in the union. Removing either class was rejected during recorded execution; stale system and executable hashes were rejected at preflight, before an output tree was created.
- Bootstrap receipts explicitly reported BOOTSTRAP and dependency_lock_verified=false. Locked replay was separately required and verified.
- Separate hostile TMPDIR, TEMP and TMP environments pointed inside frozen scientific input directories, with additional hostile inherited TeX variables. All builds preserved the candidate and reproduced the synthetic packaged PDF.
- Two complete candidate ZIPs were byte-identical. Authenticated extraction restored all descendant bytes, modes and nanosecond mtimes, and relocated verification and replay succeeded.

## Rejected adversaries

The receipt enumerates exact commands and rejection reasons. Coverage includes missing isolation flags and optimization; relative, noncanonical, existing, dangling-symlink, aliased and protected-tree outputs; source symlinks; wrong or malformed manifest/manuscript/lock pins; changed helper bytes; frozen bytes/modes/mtimes and directory metadata; unexpected, missing and empty descendants; hardlinks, symlinks and FIFOs; duplicate JSON keys and unsafe manifest schemas; invalid PNG signatures, CRCs, truncations, trailing bytes, dimensions, format, chunk order, deflate boundaries, raster lengths and row filters; ZIP traversal/absolute paths, duplicates, order changes, missing members, changed payload/mode, nonregular/non-Unix entries, authenticated malformed manifests and raw CRC corruption. Rejected archive cases were refused before creating extraction output.

## Explicitly exercised boundaries

Manifest bytes require a digest supplied outside the archive. The manifest's own filesystem metadata and the release root's mode/mtime are outside its inventory; changing those alone is deliberately accepted, with per-operation preservation still checked. Every descendant directory and payload file remains exactly inventoried.

Extraction authenticates the ordered member inventory, regular Unix file type, payload bytes and authenticated file modes. ZIP dates, compression method and comments are container metadata outside that authentication boundary. A rewritten container with changed values was accepted and its extracted payload verified. Extraction assigns a fresh mode-0700 root and a mode-0644, fixed-epoch manifest.

The lock does not inventory shared libraries, Python's standard library or the operating system. The workflow assumes inspected/pinned tools and manuscript; it is not a general security sandbox for arbitrary hostile TeX. Access times and transported creation/change times are not release-integrity claims. No concurrent malicious filesystem writer was introduced.

## Candidate identity and evidence

- Candidate manifest SHA-256: f19d84a61897d328876e5420cf763c95918c6636995086e20c993839163911c9
- Candidate ZIP SHA-256: 738bb61c4e18c5c4f55af0cda5e6398fdc4aea0a28170767516857a659e69bfa
- PDF SHA-256: d061fda50f26cad711e4f20d028d126d1ce232469425b0745728eed014895010
- Manuscript-map SHA-256: 944b95cbd26caf7bca3967fc8be0c4395b9fd5df3e517fe953767c39cdaf0332
- Dependency-lock SHA-256: a467e715df8470d46d66d94e64da543bf3aaf4a5e2192cc486ddaf98d913df9c

The compact dossier contains the two independent scripts, combined and raw receipts, original-file/directory checks, source pins/diffs, reference PNG inventory, direct/relocated build receipts, page inventories and recorder-union evidence. Full candidate copies, command logs, synthetic fixtures, rejection artifacts and ZIPs remain in the external review workspace. Test scripts preserve that workspace's absolute evidence paths and are reproducibility records rather than the release's supported portable runners. Use the inspected tools/ commands in the release README for portable operation.
