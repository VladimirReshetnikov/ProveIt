# Report 59: independent release-tool review

**Result: PASS after targeted hardening, for the exact tool and manuscript bytes below.**

The initial standard suite passed 142 checks. Seven additional structural/interleaving probes exposed gaps that were then fixed. The final focused regression passed all 42 checks, including a fresh isolated hostile-environment build at the final manuscript pin. There are no unresolved release-blocking findings in the tested scope.

## Scope and execution boundary

This is a safety, packaging, preservation and reproducibility review of `tools/build_report59.py`, `tools/derive_presentation.py` and `tools/release59.py`. It is not a mathematical audit, proof review, physical-model validation or independent assessment of the replay adapter.

The three tools were read before execution; subsequent edits were reviewed as source diffs before the final regression. Tests used independent newly authored checkers, inspected release tools and installed TeX/Poppler programs. No author constructor, author checker, historical/upstream research program, physical simulator, saved collision schedule or Lean process was executed. The separately supplied portable replay tools were carried only as inert bytes in a scratch archive.

All mutation and failure-injection tests used copied releases and external test destinations. The production frozen directories `science/`, `independent-audit/`, `dependencies/`, `real-input/`, `real-input-audit/` and `real-input-dependencies/` remained byte-for-byte unchanged. Both initial and final inventories record this preservation. The reviewer did not edit production sources; the release author applied the recommended hardening.

## Exact final reviewed bytes

| File | SHA-256 |
|---|---|
| `tools/build_report59.py` | `7a8216a4510aecdf35456d7c9e6fc6cb27293e3f25497a864d5fe9ce9364cd64` |
| `tools/derive_presentation.py` | `4b9927e7dc688cf90ea4ba7ab068a5deb1caafa11bc2b049843bfd7ce7e59373` |
| `tools/release59.py` | `d340309902a5bcf7fcca750dd528982bd016f69474f9ead347653dba438cfe47` |
| `manuscript/report59.tex` | `3473c1fe22ecbfe55fd2728c9d243c166677811e3738e241dee8f2ff88ed8c66` |
| `manuscript/fixture-table.tex` | `d3ce355756c41d21966cac575c8f98afabac56e81c91c37512e4fe871e07bf2e` |
| `manuscript/geometry-figure.tex` | `3fdb9ee48c04fa0e5217cc775c8c8e10f68f9cb70252bd7b6877674f931ead59` |
| Final PDF, 22 pages | `a5fb0f18f1d60efb6d6ba2c884434a719ccae488b6dc89aebdbfbff5b4201fb0` |

The final fresh reviewer build used `python3 -I -S -B`, fresh TeX format generation, three compilation passes, no shell escape, text extraction and all-page rendering at 120 DPI. Its PDF, extracted text and all 22 PNGs were byte-identical to the release author's final draft7 build. `--require-packaged-match` also passed against the same final PDF copied into the scratch release.

The two earlier independent clean/relocated builds used manuscript SHA-256 `941a0deb94d7b59ba9ff4ee0f81793b63633aa2899b6bebaca9c0a5bf76344a3` and produced identical PDF, text and 22 PNGs. Their PDF SHA-256 was `0cb46f9a78c2dbb84890c794d90535aed46576d64f5834af3bc7cf631e7ee713`. These older results are retained as tool-determinism evidence, not mislabeled as the final manuscript build.

## Findings and disposition

1. **Build snapshot incompleteness: fixed.** The original preservation census silently skipped an absent frozen directory, followed a top-level input-directory symlink and ignored a FIFO. Four direct snapshot probes demonstrated these behaviors, including a symlinked manuscript directory. The final implementation requires every input base to be an `lstat`-confirmed real directory and every descendant to be a directory or regular single-link file. Both direct probes and CLI attempts now refuse before creating an output.

2. **Editable manuscript pins were only a consistency check: hardened.** Both the builder and release checker now contain the three reviewed manuscript hashes. Mutating the manuscript and updating `MANUSCRIPT_PINS.json` to match no longer passes either entry point. The final source hash is the one in the table above. The tool bytes must themselves be obtained from the authenticated release; hardcoded hashes do not authenticate a modified checker.

3. **Manifest destination race: fixed.** A controlled interleaving created a competing output immediately after the fresh-destination check. The original `write_bytes` overwrote it. Exclusive `open('xb')` now refuses and preserves the competing bytes.

4. **Archive exception cleanup could delete a competing output: fixed.** In the same interleaving, exclusive archive creation correctly failed, but the original exception handler then unlinked the competing file. The final implementation does not unlink on failure. A competing destination remains intact; an injected failure after creating a new archive leaves that new partial output for inspection.

5. **Archive source-to-manifest race: fixed.** A source mutation after manifest validation but before the archive's second inventory previously yielded a printed PASS while the ZIP disagreed with its embedded manifest. The final implementation requires that second inventory to equal the authenticated manifest plus the pinned manifest bytes before opening the archive. The regression refuses the mutation with no output created.

The race tests use deterministic in-process hooks around the inspected `fresh_file` boundary. They emulate an exact concurrent filesystem interleaving without timing-dependent threads or touching production. `APPLIED_HARDENING.patch` records the actual final source changes. The earlier `recommended-hardening.patch` contains preliminary edit hunks and is retained only as historical review material; it is not the final patch.

## Coverage

- Canonical absolute destinations, fresh external outputs and relocated source roots, including a source path with spaces
- Rejection of relative, double-slash, dot, parent-component, trailing-slash, release-internal, pre-existing, missing-parent and symlinked output paths
- Preservation of pre-existing output files, directory markers and symlink targets
- Rejection of ordinary, optimized, site-enabled and bytecode-enabled invocations
- Extra, missing, tampered, symlinked, hardlinked and top-level symlink-directory tests for every frozen subtree and the manuscript
- Builder rejection of extra/missing/tampered/symlinked/hardlinked manuscript files
- Presentation-tool rejection of missing/tampered/symlinked/hardlinked pinned evidence and symlinked evidence roots; derived table and figure exactly matched the frozen manuscript assets
- Manifest verification rejection for an incorrect external manifest hash and extra/missing/tampered/symlinked/hardlinked release files
- Independent exact manifest-to-filesystem inventory and ZIP name/content/metadata checks
- Deterministic repeated ZIP generation, including final-tool regression archives
- No generated Python bytecode; before/after frozen input preservation
- Final-source PDF, text and every rendered page reproduced under hostile environment settings

Hostile settings included poisoned `PATH`, `PYTHONPATH`, `PYTHONHOME`, Python optimization variables, home directory, temporary-directory location, TeX input/configuration/format/font-map variables, locale, timezone, source epoch, shell escape and TeX input/output-policy variables. Poison executables and TeX files were not used. Fixed executable paths and the restricted subprocess environment controlled the build. An independently located temporary directory changed diagnostic logs, not the PDF/text/page bytes.

The final-tool scratch packaging test generated a manifest for 122 files and a ZIP containing those files plus `MANIFEST.json`: 123 entries total. Both repeated ZIPs had SHA-256 `55775e4b64ba32c0a4e82e0cbc617c45e205f40ab038fd3eb0a5d4e37b4d182f`; their manifest SHA-256 was `542b1aebd8c988ae6da5a0fe6a2c0355781d5cec9a1afef7a9917846de757e5e`. These are **test snapshot** hashes, not the subsequently sealed production release hashes. Every ZIP member matched the embedded manifest and filesystem, with sorted entries, fixed timestamps, regular read-only mode and DEFLATE compression.

## Boundaries and residual qualifications

- Success means exit code zero plus the printed PASS receipt. A retained partial archive from a failed command is not a completed release.
- The presentation tool authenticates the two evidence inputs it uses. It does not claim to authenticate every unrelated file in `science/`; complete frozen-input authentication is the release checker's job.
- The builder checks preservation and reviewed manuscript bytes. Complete frozen science/dependency authentication remains `release59.py check-inputs` / pinned-manifest verification.
- Manifests inventory files, not empty directory names. ZIP inventory claims have the same file-only meaning.
- PDF, extracted text and page images are reproducible in the tested installed environment. Random temporary paths make diagnostic logs and their receipts unsuitable for a claim that the entire build directory is byte-identical.
- TeX executable and recorded TeX/font-map input hashes are captured. Dynamic libraries and the complete operating-system/Python/zlib stack are not fully inventoried, so this is not a cross-platform bit-reproducibility claim.
- These tools are not a sandbox against a malicious operating system, modified interpreter, hostile installed native libraries or an attacker continually replacing path components as the same user. Ordinary path guards and the demonstrated races are covered; universal race-free filesystem confinement is not claimed.
- The final production manifest and final distributed archive must be verified after all review material has been added. This review validates the exact tool versions and scratch packaging behavior, not a future unobserved release inventory.

## Evidence index

- `SOURCE_SNAPSHOT.json`, `SUMMARY.json`, `TEST_RESULTS.json`, `RUN.log`: original pinned snapshot and 142 standard checks
- `SNAPSHOT_PROBES.json`, `RELEASE_RACE_PROBES.json`: seven reproduced original gaps
- `audit_release_tools.py`, `probe_build_snapshot.py`, `probe_release_races.py`: independent test sources
- `revised/SOURCE_SNAPSHOT.json`, `revised/SUMMARY.json`, `revised/REGRESSION_RESULTS.json`, `REGRESSION_RUN.log`: exact final tools and 42 passing regressions
- `regress_hardening.py`: final regression source
- `revised/REFERENCE_BUILD_RECEIPT.json`, `revised/build/BUILD_RECEIPT.json`: final-reference and fresh hostile-build receipts
- `APPLIED_HARDENING.patch`: reviewed final fixes
- `command-logs/`, `revised/*.log`, `outputs/`, `revised/build/`: retained detailed transcripts and build outputs

The curated `evidence/` directory contains the report and essential receipts/checkers without the intentionally corrupted test copies or failure artifacts.
