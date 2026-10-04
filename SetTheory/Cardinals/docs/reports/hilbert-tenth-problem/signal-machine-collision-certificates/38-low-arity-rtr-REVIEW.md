# Independent Report69 release-tool and README review

Date: 4 October 2026. Verdict: **PASS for the identified presentation-only candidate**, with one explicitly unavailable operating-system probe and no required tool correction.

## Identity and boundary

The reviewed stable tree was `/workspace/shared/report69-tool-review-candidate-v5`. Its complete README and all three Report69-owned Python tools were read before any of them was executed. `REVIEWED_PINS.json` authenticates the precise inspected bytes. The candidate was intentionally pre-seal: its README states that the independent reviews are pending and it has no final release manifest. The whole-candidate manifest and archives constructed by this reviewer belong only to isolated external copies. They are **not** the eventual delivered release manifest or archive.

The writer may subsequently replace only the README's Presentation acceptance paragraph to report the completed reviews, and add their dossiers before final sealing. This verdict does not assert the contents of those future additions or a future terminal verification. The tool bytes, command pins, PDF and manuscript pin map reviewed here must remain the identified bytes if this review is cited for them. The final release still requires its separately authenticated manifest and terminal verification.

This review addresses release authentication, safe path/output handling, exact inventory and metadata, deterministic archive creation, preserving extraction, reproducible presentation building and honest README scope. It does not independently establish the article's mathematical correctness, novelty, literature priority or visual page quality. The mathematical-transcription/page review is separate.

Only the three inspected Report69 presentation tools and freshly written, inspected review scripts were run or imported as task programs. Their permitted presentation operations invoke the system TeX and PDF tools. Scientific files in `science/` and `audits/`, upstream scientific programs, counter interpreters, physical simulators, schedules, Lean, and the predecessor Report68 tools were never executed or imported. Scientific trees were treated only as inert bytes and metadata. No original or candidate content, modes or mtimes were changed.

## Inspected principal pins

| Item | SHA-256 |
| --- | --- |
| README.md | `975cae6eca069477fb5164d506b68ff8b7351bab7209a916ddb72e9a06d7036a` |
| tools/release69.py | `cf70098ca75442d0e7868bf63fe03a15f80694895aa2ffe660d16f67c4ed3807` |
| tools/build_report69.py | `16074885d6203a09cbcc448478d4d4cbfb4ac91c36c018963da793d08194e2cb` |
| tools/selftest69.py | `c3beaf2f18090c851ead535239e6ef91964a3241bce11ea8004f980f9cd326f4` |
| Report69.pdf | `fc0db742d499ee0e515700134460f78b44d3c7301f14c63c77cfa6fb9a6686ce` |
| Report69.tex | `9f0508066f9354b6c7d74b4d6b8a10498e632e5e31b149ff8312ffb75f82cfd0` |
| manuscript/MANUSCRIPT_PINS.json | `38b3f7a8a3bb1f837ace42df35edffd8d7627d3af476f4869106903e31824e4c` |
| tools/BUILD_DEPENDENCIES_LOCK.json | `62d196ba3a660790910afa4ac4eb83f1410b8b64e6a401ad52d1388ee812f3f5` |
| INPUT_PINS.json | `5b1563a78935432a6d96f6665335f78c7c996f25d65e7b9e6e2532d909a9649d` |

## Results

- Candidate `check-inputs`: PASS for all 85 inert input files and their pinned metadata.
- Fresh locked candidate build: PASS. Exact packaged PDF, 17 rendered pages at 120 dpi, four recorded phases (fresh format plus three TeX passes), and 269 system-input entries.
- Owned selftest rerun: all 39 tests PASS. This remains owned testing and is not relabeled as independent evidence.
- Independent adversarial suite: 117 checks PASS and one filesystem-socket probe NOT RUN because this environment denied socket creation. The first authentic failed harness and traceback are retained. The second harness deliberately avoids repeating or circumventing that denied operation.
- Independent build probes: all 12 PASS, including a different first-pass-only dependency (`calc.sty`) and read-only fault injection of system and executable postflight changes.
- Full-candidate operations: all 12 recorded checks PASS, including two byte-identical archives, preserving extraction, relocated verification and exact PDF/PNG replay.
- Preservation: all 1,381 entries across 12 roots (the candidate plus 11 protected original roots) are identical before/after in bytes, modes, nanosecond mtimes and recorded root metadata. The two independent inventory files are byte-identical, SHA-256 `73b08dc6ca888af6de57e076c6ba43740035fa44b901be1dc756ece14c6c339e`.
- All 1,202 entries in the candidate's original-input baseline agree with the current independent original-source inventory. Original and copied source/audit entries agree directly, in addition to the tool's frozen-pin check.

The separate suites are reported separately rather than presenting their overlapping assertions as a single distinct-coverage count.

## Detailed findings

### Authentication and inventory

Verification first reads the manifest as a single-link regular file, authenticates its actual bytes against a caller-supplied lowercase SHA-256, rejects duplicate JSON keys and validates an exact schema. Files and directories have disjoint inventories; every parent directory is required and extraneous empty directories are rejected. Content digests, byte counts, file/directory modes and nanosecond mtimes are compared exactly. A manifest is not accepted merely because it is contained in its own archive.

Tests rejected absent/duplicate/extra members, wrong member ordering, duplicate JSON keys even with the malformed JSON independently re-pinned, manifest self-reference and manifest-directory collisions, file/directory overlap, missing parents, extra fields, booleans substituted for integers, negative sizes/times and set-ID modes. Same-size content replacement with original mtime restored still failed verification. One-nanosecond file and directory changes and mode changes failed separately; restoring the complete external fixture restored successful verification.

`INPUT_PINS.json` is itself fixed by a literal digest in the inspected release helper. Changing even its source-location metadata is refused; re-signing some surrounding release cannot silently replace this frozen map while retaining the inspected helper. `check_inputs` verifies complete inert inventories and scope-root metadata, not a convenient subset of files.

### Path and filesystem guards

Fresh outputs require a canonical absolute spelling, an existing canonical parent and a nonexistent final target. Candidate and protected-original overlap checks apply before output creation. Tests rejected relative paths, dot/dot-dot aliases, duplicate separators, leading double slash, source/output overlap, symlink ancestors and existing dangling symlink outputs. Existing hard links, including links whose other name lies outside the input tree, are refused. `read` uses no-follow open and compares descriptor/path identities around the read.

Tree inventories reject symlinks and nonregular entries. FIFO tests demonstrated refusal before a blocking read; malformed ZIP entries marked as FIFOs, sockets and symlinks were separately rejected. The live filesystem-socket test was unavailable because the environment denied `socket(AF_UNIX)` itself. This limitation is not reported as a successful filesystem-socket test. Static inspection confirms the same nonregular-tree branch covers such an entry.

These are safeguards for inspected, stable local releases and trusted system tools. They do not claim a privileged adversarial mount-race proof, a complete hostile-kernel sandbox or transactional cleanup after every operating-system failure. No such claim is made in the README.

### Archive and extraction

The isolated full-candidate manifest authenticates 158 files. Its SHA-256 is `86662a712b9f924b251f0e2df26cc61593018417530f315db69b5a34d3b2e0ce`. Both fresh deterministic archives contain 159 regular members, including the manifest, and are byte-identical with SHA-256 `d76ac913e139cd05033c32d5a22192539bb98131d10912e6a9543e8d09776fe9`. An independent ZIP inspection checked sorted names, the Report69 prefix, Unix regular-file attributes, fixed 2026-10-04 timestamp, deflate type and CRC success.

Before creating the extraction root, the extractor authenticates the manifest, validates its schema, checks the exact ordered member list, CRCs, payload sizes/hashes and regular Unix file modes. All malformed-archive cases in the independent suite refused without creating their requested destination. Archive input symlinks and hardlinks were also refused. A valid synthetic extraction independently restored a deliberately non-round nanosecond mtime and non-default file/directory modes.

Full extraction independently reproduced all authenticated descendant metadata and payloads and created a 0700 root. The relocated verifier then passed. The README correctly excludes the release root's metadata and the manifest file's own filesystem metadata from the descendant inventory, describes their extraction treatment, and does not claim to authenticate ZIP timestamps, comments, compression or all container metadata. The extractor's subsequent verification step remains necessary for the fixed Report69 inert-input policy.

### Presentation build and dependency accounting

The inspected builder hash-pins its release helper before executing that helper. It validates the external manuscript map, verifies deterministic flattening against the packaged standalone TeX, checks the external dependency lock and executable/system-input fingerprints before creating the build output, and uses a new format and selected font map in a temporary directory explicitly placed under the fresh output. All engine commands disable shell escape. Only an allowlisted environment is forwarded; inherited HOME, TeX search settings, temporary-directory variables and shell-escape settings are not authoritative.

The independent synthetic manuscript imports `calc.sty` only when the first-pass auxiliary file is absent. Its recorder showed that dependency only on pass one, and the union retained it. Removing it from a newly pinned test lock caused an explicit unpinned-input refusal after the first pass, with a preserved-source failure receipt. The owned test separately exercised `ifthen.sty`. Thus final-pass-only accounting was not accepted as complete coverage.

Executable and system-input preflight mismatches, wrong external pins and a changed helper all refused. Two instrumented tests left real system files untouched: the review wrapper changed bytes returned by the helper's read function only at the designated postflight stage. The system case triggered `System input changed during build`; the executable case triggered `Executable post-build mismatch`. Both produced FAIL receipts with preservation true and no successful build receipt. These are guard fault-injection tests, not claims that actual installed binaries changed.

The full candidate and its relocated extraction each reproduced the PDF exactly. Every one of their 17 PNG files matched the packaged final-build image byte-for-byte, and their complete page-inventory JSON and dependency-receipt JSON were also byte-identical to the packaged references. PNG checks covered signature, chunk CRC/order, allowed RGB format, dimensions, density structure, bounded decompression, exact raster length and row filters. Malformed dimensions, chunks, compression trailers, truncated streams and raster lengths were refused. Raster equality is not substituted for individual visual inspection.

The dependency scope is accurately limited to interpreter/executable bytes and recorded TeX/font inputs plus selected maps. It does not cover shared libraries, the Python standard library or the entire operating system. Bootstrap truthfully labels itself unverified and never claims preflight lock verification.

## README acceptance and preservation qualifications

The README's command pins agree with the inspected candidate. The example commands use isolated Python without site packages or bytecode writes. It distinguishes stored scientific audit evidence from newly executed presentation checks; retains the earlier historical preservation interruption rather than asserting a false static interval; describes owned tests and independent reviews separately; and leaves later terminal verification outside the eventual sealed archive. No correction is required to these descriptions.

The mathematical summary is outside this tool audit's proof scope. No scientific result, historical audit count or primary-literature novelty claim is certified merely by passing these tools. The final acceptance paragraph must be updated honestly after both independent reviews, without implying that a later terminal receipt was already inside the sealed archive.

Preservation excludes access times, filesystem birth/change times and machine-specific inode numbers from portable equality. The independent before/after snapshots additionally record file link counts and original root metadata. They are equal. No failure log, fixture or original source was deleted to obtain that result.

## Evidence and retention

Principal receipts are `REVIEWED_PINS.json`, `FULL_OPERATIONS_RECEIPT.json`, `ADVERSARIAL_RECEIPT.json`, `BUILD_PROBES_RECEIPT.json`, the owned `SELFTEST_RECEIPT.json`, the two preservation inventories, and all corresponding stdout/build/recorder artifacts. The original interrupted `adversarial69.py` and `adversarial.stdout` remain intact beside the completed `adversarial69_v2.py` run.

`dossier/` is the compact inclusion set: this review, precise pins, inspected tool/README copies, fresh review scripts, all run stdout and build/recorder logs and receipts, preservation inventories, the candidate test manifest and page/dependency inventories. `EXTERNAL_EVIDENCE_INDEX.json` identifies the external working evidence by exact relative path, metadata and content digest. Bulky copied candidates, synthetic fixture trees, duplicate ZIPs, PDFs and rendered PNG payloads remain in the external working directory and are **not** claimed to be included in the compact dossier. Their relevant exact inventories and hashes are included. `DOSSIER_MANIFEST.json` authenticates the compact dossier's actual file set; the separately returned dossier-manifest digest authenticates it.

All review scripts are records of this isolated local review, with deliberately fixed local paths. They are not substituted for the README's portable consumer replay commands.
