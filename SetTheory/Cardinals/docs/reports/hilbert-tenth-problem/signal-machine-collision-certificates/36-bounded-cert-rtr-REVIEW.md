# Independent review of Report66 release and build tools

Date: 4 October 2026 (UTC)

## Verdict

**ACCEPT for the tested release-tool contract and final article candidate.** All 142 independently authored synthetic, adversarial and full-article checks passed: 117 primary checks, 13 additional refusal-path checks, and 12 article/archive checks. A further independent raw-PNG pass checked all 42 rendered pages from the two full-article builds and found identical page inventories. No release/build code correction was required.

One documentation precision issue was reported and corrected before acceptance: the release manifest does not authenticate the outer root's mode/time or its own filesystem metadata, and extraction does not authenticate every ZIP container field. The reviewed README now states those limits explicitly. This verdict is about the identified tool sources and article candidate. It is not an independent signature of a subsequently assembled release archive.

## Independence and execution boundary

The reviewer read all of `release66.py`, `build_report66.py`, `selftest66.py`, and the README before executing the reviewed release/build code. The sources matched the supplied external hashes. The reviewer wrote separate test harnesses and independent inventory, hash, recorder-union and PNG oracles. The author-owned `selftest66.py` was inspected but **not executed**, and its 39-test receipt was not substituted for reviewer evidence.

Only inspected Report66-owned release/build code, newly written independent release/static tests, Python standard-library facilities, and TeX/Poppler presentation tools were executed. All destructive/hostile mutations were confined to newly made inert copies in a separate review directory. No science or mathematical-audit checker, native counter interpreter, physical simulator, saved schedule, author/upstream mathematical program, or Lean source was imported or executed. Reading, copying and hashing their files is not scientific execution.

The direct comparison against Report64 sources shows the same operational contract: Report66 naming, input pins, module paths and protected-source list were adapted, with an additional explicit metadata check for the `science` and `audits` scope roots. This is not a new sandbox or stronger operating-system isolation claim.

## Exact tested source pins

| Item | SHA-256 |
|---|---|
| `tools/release66.py` | `6a86de64d934a9bf13a3780edf7ef92942d72a860146b442ad89949606360344` |
| `tools/build_report66.py` | `e12e30e6fd2503466fccac8212f28b4ee4814fa78a96a42ab08e53948c826b0e` |
| `tools/selftest66.py` (read only) | `9c92ed278635ebdb780f7d193aff5be8faf9aa71425e56d7784a600b04ee6f3b` |
| `INPUT_PINS.json` | `6ddfffa2d40fec72b14da420676a018ac05e5ab527c64feaf16fed13457fa4da` |
| Article dependency lock | `600f1af2999954df4ce9662cf5317e49867c04b0a613eabb418e0943090f9617` |
| Final manuscript-pin map | `ad42c8401fac8b7f6c7e0e03ad8eb2de792862a39463f7f0e686daef68ec30e1` |
| Final flattened `Report66.tex` | `a5e165a083800b93b56a122920c7e50e2304e1e27eea58080fbb4a3ad564a0b8` |
| Final `Report66.pdf` | `27209f12b5e2bf07c1851a5db538a6124c171467d92bff6f45b79fe85f65d69f` |
| README after metadata qualification | `ab6bd588c22385e51573f7873930c0bd352f3db01b6f22c1f14b5b675524dc13` |

Later additions of review receipts or verdict wording require a new final release inventory; they do not change the listed tested executable and article pins.

## Adversarial coverage

The independently written primary harness created its own synthetic manuscript. A `calc.sty` dependency appears only in its first TeX pass. Its path survives in the recorded union and dependency lock; deleting that single input from an externally repinned lock causes the locked build to fail. A stale system-file digest and an altered executable digest fail preflight before output creation. Wrong manuscript/lock pins, uppercase/noncanonical pins, a disallowed render DPI, unisolated Python and optimized Python are rejected.

The tests also establish:

- Exact frozen descendant inventories, bytes, modes and nanosecond mtimes, including the newly enforced `science`/`audits` root mode and mtime checks
- Rejection of missing/extra files, unexpected empty directories, special FIFO entries, source symlinks, and multiply linked files
- Safe, fresh external outputs; refusal of relative, dot, dot-dot, repeated-separator, trailing-separator, existing, protected-overlap and symlink-ancestor destinations
- Refusal of symlinked source roots, dangling existing output paths, changed/symlinked/hardlinked release helpers, and symlinked/hardlinked archive inputs
- Successful locked, byte-identical synthetic builds with hostile `TMPDIR`, `TEMP`, and `TMP` values pointing into frozen source copies; additional hostile TeX/Python environment settings are ignored by the explicit build environment
- Rejection of malformed manifest paths, missing/extraneous directory inventories, file/directory and manifest-name collisions, duplicate JSON keys, extra fields, unsafe modes, Boolean numeric fields, negative sizes/times and invalid digest encodings
- Rejection of truncated, trailing-data, bad-filter, bad-size, bad-color, bad-CRC and extra-compressed-stream PNG specimens; acceptance of a valid independently constructed RGB raster
- Byte-identical repeated ZIP creation, exact independently checked member ordering and fixed metadata, extraction restoring authenticated descendant metadata, verification from a relocated copy, and locked PDF equality after relocation
- Rejection before output creation of archives with traversal/absolute entries, duplicates, missing/reordered members, extra empty directories, symlink/non-Unix entries, wrong file modes, changed payloads and malformed authenticated manifests

No concurrent hostile process, mount/bind-mount alias, archive decompression bomb, hostile kernel or compromised system binary was simulated. The rejection checks cover the ordinary filesystem/link aliases available without changing system security or mount settings. They are not a proof against all races or resource-exhaustion attacks.

## Full final-article replay

A copy of the final article candidate was made with original bytes, modes and nanosecond mtimes. Both the initial locked replay and a second locked replay from metadata-preserving archive extraction:

- Passed with `--require-packaged-match` and `packaged_pdf_match: true`
- Produced the exact final PDF digest above, with 21 pages
- Used a fresh local TeX format and fresh font-map construction, disabled shell escape, and three LaTeX passes
- Returned a dependency receipt byte-identical to the externally pinned article lock
- Preserved all source-copy entries, including directory metadata and the root metadata observed for each operation
- Rendered all 21 pages at 120 DPI, with identical page hashes across the two replays

An independent parser reconstructed the union directly from the four retained `.fls` files and the five selected map lookups, then rehashed every external dependency. It matched 268 system inputs. The format recorder contains 64 distinct external inputs, and each article compile recorder contains 206. The actual article has no necessary first-pass-only discriminator; that edge case is established by the independent synthetic `calc.sty` experiment, not inferred from this article.

The independent candidate manifest SHA-256 is `d30847734b9bb2ebe6b69a5754b9226a989a48ff6166e429bb592febae62d08b`. Two independently requested candidate archives were byte-identical, with SHA-256 `1743096a372c1b752e39bdeea7abc97ff9f5ab94cfbb6083a512beb596b127f8`. These identify the reviewer's pre-final-assembly copy, not the author's later sealed release ZIP.

## What metadata is and is not promised

1. The externally pinned manifest authenticates the exact listed descendant file bytes/sizes/modes/nanosecond modification times and descendant directory modes/nanosecond modification times. It rejects extra empty directories. Regular files must be single-link. The fixed input map separately enforces inert science/audit inputs, including their scope roots.
2. The outer release root's filesystem metadata is outside that manifest. Its current metadata is checked by per-operation preservation snapshots. Extraction creates a fresh root with mode 0700; its timestamp is newly produced, not transported.
3. The manifest's own bytes are authenticated by the external digest. Its mode/mtime cannot be self-authenticated by this inventory design. Extraction assigns it mode 0644 and epoch `1791072000000000000` nanoseconds. Tests deliberately altered this metadata and correctly observed successful verification.
4. ZIP creation emits sorted `Report66/` members, fixed timestamp `(2026, 10, 4, 0, 0, 0)`, Unix regular-file type/modes, and level-9 deflate. Repeated bytes were established in the same installed Python/zlib environment, not across all possible versions.
5. Extraction checks the exact member list/order, manifest pin/schema, CRC, regular Unix file types, payload bytes/hashes/sizes and manifest-listed file modes. It reconstructs descendant directories from the authenticated manifest. Member timestamps, compression choices, comments and other container metadata are not all authenticated. An archive whose README member timestamp was changed still extracted successfully, while all authenticated payload metadata was restored.
6. Access times, ownership, inode identity across filesystems, creation/change timestamps, ACLs and extended attributes are outside the transported contract. File-reading races receive the implemented identity checks; no global concurrent-adversary guarantee is claimed.

The final README accurately states the relevant boundaries. Extraction is followed by relocated verification, which also validates the fixed frozen-input map.

## Preservation and reproducibility limits

`ORIGINALS_BEFORE.json` and `ORIGINALS_AFTER.json` are identical independent scans of both original release evidence scopes and all six protected source roots, including their file/directory modes and nanosecond mtimes. `ARTICLE_AND_TOOL_PRESERVATION.json` additionally checks final original article, manuscript, input-map and tool metadata against the copy made before replay. The author's concurrent authorized README clarification is explicitly excluded from that comparison. The reviewer did not edit the release.

The toolchain lock inventories named executable/interpreter bytes, all recorded external format/LaTeX input bytes, and selected font maps. It does not inventory the Python standard library, linked shared libraries, all files read internally by Poppler, fonts outside the recorded TeX scope, the operating system or the kernel. Preflight checks the locked files; an omitted or newly encountered TeX input is detected after the recorder-producing invocation, so this is not a pre-execution sandbox for arbitrary unreviewed TeX. The manuscript and helper must already be inspected and authenticated.

Successful typesetting/archival replay establishes presentation reproducibility. It does not prove the mathematical theorems, independently execute inherited scientific evidence, re-formalize the constructive Pell theorem or compiler theorem, or replace the separate manuscript/visual/mathematical reviews.

## Evidence and harness note

The compact accompanying evidence contains the independently authored harness sources, complete named-test receipts, final article pins and replay receipts, all-pass recorder evidence, independent page checks, preservation records, the reviewer's candidate manifest and an evidence-file hash inventory. Large fixture clones, rendered pages, duplicate article PDFs and ZIPs stay in reviewer scratch storage and are deliberately excluded from the release evidence subset.

The harness sources document the exact scratch paths used for this review. They are historical review evidence, not drop-in replacements for the packaged user's replay commands. One preliminary harness attempt removed the owner-execute bit of a copied directory and consequently prevented the reviewer's own scanner from entering it before the reviewed tool was invoked. That harness-only setup issue was corrected to change a non-owner mode bit, and the complete 117-check primary suite was rerun from fresh fixtures. No product test failure is concealed by this correction.
