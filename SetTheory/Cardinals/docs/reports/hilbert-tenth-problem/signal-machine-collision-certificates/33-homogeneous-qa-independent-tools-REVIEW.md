# Independent Report63 release-tool review

## Verdict

**PASS for the exact tool sources and final manuscript candidate identified below. No required tooling correction was found.** This fresh review is independent of the owned selftest implementation. It comprises full source inspection, 103 separately authored diagnostic checks, a fresh execution of all 39 owned selftests, two actual locked builds separated by deterministic archive relocation, independent recorder-union reconstruction, source preservation checks, and authenticated reviewer-checker replays. It is not an all-parameter mathematical proof review or an all-page visual-layout review.

The actual manuscript was the final 18-page candidate d. The two locked PDF builds are identical to its packaged PDF; all 18 PNG raster hashes are identical between builds. The diagnostic archive is deliberately not described as the final distributed archive: integrating reviewer/visual QA changes the release inventory and requires final sealing again.

## Source commitments

| Object | SHA-256 |
|---|---|
| tools/release63.py | dda555a5681b2d33626e4cfb25c1b5990208f77c1e0e3f392040dc6df57f2675 |
| tools/build_report63.py | 6e62162d625fa17df712ee704950c099ea5e95e0e278820a7985a6a847374bd9 |
| tools/selftest63.py | 2d7572a9217b9eb301fb84ab0be87734b2446fc94ceebef8fc36e5d42037c804 |
| INPUT_PINS.json | b078c2b3b0f3582461fb9a250795dab1ecaa69b4920f80187daa946337e377b3 |
| tools/BUILD_DEPENDENCIES_LOCK.json | c92b3fb240739cfbd8617e9e14407288c7e60c62fb41c433684c9e5f44541d74 |
| final manuscript/MANUSCRIPT_PINS.json | 8dbeb0e7bdcbf949ebba9a699ab262dbb84b0111d9bb60d85c4c2a69aa10cbf1 |
| final standalone Report63.tex | 232bac78b073aa9b3896aa1dade2a5f6372a000240ec67e9923dc6287555eb65 |
| final Report63.pdf | eb8d4d7c0cc0c98a7b706efe5e262d6b17699e21be7976957725f836420ad3ed |

The raw initial authentication receipt records the earlier manuscript pin observed when the tools review began. It is historical only. The explicit `final_manuscript_pins_sha256` in the actual release receipt and `FINAL_MANUSCRIPT_BINDINGS.json` identify the candidate actually built and accepted here. Tool and frozen-input bytes did not change between those stages.

## Authentication and execution boundary

All three owned Python tool files were read in full before execution. The ten final modular TeX sources were inspected before the actual build. The release helper's hardcoded frozen-input commitment and the builder's helper-source commitment matched. All 59 frozen files matched their bytes, modes, and nanosecond mtimes; the original scientific and scientific-audit trees matched their packaged copies. Both embedded manifests authenticated, and all four copied dependency proof/review files matched their historical originals as well as the additional release copies.

Only owned release/build/selftest code, independently written diagnostic review code, standard typesetting/rendering executables, and the two specifically authenticated independent static reviewers were executed. No author mathematical checker, upstream constructor/program, physical simulator, saved collision schedule, or Lean source was imported or executed. The arithmetic DAGs and scientific data were inert input to the explicitly allowed static review.

The reviewed core checker, SHA-256 `6aef665f0f902c185ab542496f03d53ede3f21fae31a09de8c0b38541575ae9e`, was read in full and replayed in archived-source mode on a freshly copied, relocated scientific packet. It passed 832 named checks. The reviewed certificate checker, SHA-256 `0a426f4b8743804e846b3d6faf882fe676a7ebce391430cc61403f61af165f13`, was likewise read in full and passed 737 checks on the same relocated packet. The latter uses standard-library sparse integer polynomials. The former used SymPy 1.14.0; runtime entry-point provenance is recorded separately and is not represented as a full package/shared-library lock. These runs test independent exact algebra and inert declarations, not collision simulation or physical-word execution.

## Inspected contract and adversarial evidence

### Fresh outputs, paths, and source preservation

The helpers require fresh canonical absolute output paths with canonical, nonsymlinked existing ancestors; reject overlapping protected inputs; prohibit symlinks and multiply linked files in inventoried input trees; and compare pre/post release inventories. The build creates its temporary format/home/cache workspace explicitly inside the new external output directory. It supplies a minimal subprocess environment and ignores inherited temporary-directory choices. Owned tests separately challenged TMPDIR, TEMP, and TMP. The actual candidate build set all three to three different frozen source scopes and still preserved all source bytes and metadata and removed its temporary workspace.

Independent tests covered dot/dotdot/double-slash/trailing-slash aliases, absolute/relative malformed names, dangling output symlinks, an existing FIFO, all six protected source roots, frozen-file content/name/pin-map changes, directory mode/mtime changes, a source-directory symlink, and a source FIFO. Failure paths were checked for unchanged diagnostic input snapshots; relevant preflight failures were checked to create no output. All adversarial mutations were confined to fresh diagnostic copies.

Original scientific and scientific-audit trees were compared before/after for bytes, file/directory modes, modification times, and change times. All four upstream original dependency files still matched the prior source-bound bindings including change times. The relocated scientific packet was unchanged after both allowed reviewer replays. Access timestamps are outside the preservation claim.

### Build lock and recorder union

The actual lock independently authenticated seven invoked/resolved executable records and 274 system input records. The builder bootstraps a fresh format, runs three document passes, saves each recorder before the next pass, and accumulates their union plus explicitly selected font maps. The review independently reconstructed every saved recorder's system-input set, checked its hash, and verified that the four-pass union plus those maps equals the 274-input lock. The preflight lock and post-build dependency receipt are byte-identical. Executable bytes are checked before each command and again after rendering; recorded system-input bytes are checked on acquisition, on repeated observation, and after TeX execution.

The owned synthetic manuscript makes ifthen.sty appear only on the first document pass. Its dependency remains in the union, and removing it from the lock is rejected. Independent tests also challenged wrong executable hashes, stale system size, altered schema/scope, helper-source tampering, standalone flattening mismatch, missing isolation/no-site/no-bytecode flags, optimization, and render DPI bounds. An additional valid but unexecuted system input passed preflight authentication and was rejected by the exact post-run union comparison. That failed build cleaned up its temporary directory and preserved its source.

This lock intentionally excludes shared libraries, Python's standard library, and operating-system components. It is a reproducibility/integrity record for inspected trusted sources, not a sandbox against hostile TeX or a concurrently malicious same-user filesystem actor. The review does not claim dynamic mutation of the real system executables; their repeated checks were inspected statically and their current hashes independently verified.

### PNG validation

The validator checks signature, every chunk CRC, allowed chunk types/order, bounded noninterlaced 8-bit RGB dimensions, optional pHYs constraints, terminal empty IEND, exact decompressed scanline length, complete single zlib stream without trailing bytes, and legal per-row filter values. Independent cases cover missing/duplicate IHDR, missing IDAT/IEND, nonempty IEND, post-IEND bytes, unknown chunks, zero/oversized width, wrong color/depth, invalid filters, short/long rasters, extra or concatenated compressed streams, truncated compression, and late/invalid pHYs. Every actual PDF page produced a validated PNG. This does not substitute for direct visual inspection.

### Manifest, archive, and relocation

Manifest validation rejects duplicate JSON keys, unsafe/noncanonical paths, self-reference, a directory at the reserved RELEASE_MANIFEST.json name, file/directory overlap, missing/extra/empty parents, special or boolean modes, malformed sizes/timestamps/digests, and extra entry fields. Independent extraction tests use newly pinned diagnostic manifests and challenge traversal, absolute paths, duplicate members, member order, extra directories, symlink members, wrong member modes/content, missing members, backslashes, malformed/duplicate-key JSON, the reserved manifest-directory collision, and CRC corruption. Rejections occur before an extraction destination is created for this malformed corpus.

A separate minimal archive confirms exact nondefault file/directory modes and nanosecond mtimes. For the actual candidate, two complete archives were byte-identical (diagnostic archive SHA-256 `6b3c04c1091004820d14e48378251c0b5c779c0effdf6d27c14925eeb7708b3e`). Its 126 manifest-bound files and all manifest directories survived relocation with exactly the same contents, modes, and nanosecond mtimes. A relocated manifest verification and locked rebuild passed; the PDF, dependency receipt, and complete 18-page PNG inventory were identical.

The root directory's own mode/mtime and the manifest's self-metadata are deliberately outside the recursive manifest. Extraction sets its root to mode 0700 and the manifest to documented fixed metadata; the manifest cannot hash itself. Ordinary ZIP extraction is not claimed to preserve nanosecond timestamps. Failed extraction is fail-closed with respect to protected inputs, but extraction is not a transactional filesystem rollback mechanism for arbitrary resource/permission failures. The suite does not claim an archive-size/resource-exhaustion defense or exhaustive operating-system fault injection.

## Safe final integration

1. Copy the supplied compact dossier into the release's `qa/independent-tools/`. Do not add anything below `science/`, `audits/`, or `dependencies/`: their complete frozen inventories are pinned, and any addition would invalidate authentication.
2. Keep diagnostic fixtures, FIFO/symlink attacks, temporary directories, and diagnostic ZIPs outside the distributed release. The compact packet contains ordinary evidence files only. The review harness sources are an audit record; their original execution used external diagnostic fixtures documented in the receipts.
3. Complete manuscript/layout review and all other QA before final sealing. If any tool bytes, manuscript module, frozen input, or dependency lock changes, rerun the affected source-bound checks and update the commitments; do not silently reuse this acceptance for new bytes.
4. Run `check-inputs` and a locked build using the final manuscript and dependency pins. Require exact packaged-PDF equality. Use a fresh external output directory, never a path inside the release or any protected source.
5. Generate the manifest to a fresh external file, copy that one reviewed manifest into the release, and record its digest independently. Run verify, create two fresh external ZIPs, compare their bytes, extract to another fresh external directory using the trusted manifest pin, and run relocated verify/build. Re-seal after any further release-file or metadata change.
6. The diagnostic manifest/archive digests in this dossier describe this review's pre-integration fixture. Publish the newly generated final manifest/archive digests, not those diagnostic values.

## Evidence location and limits

The compact packet includes the named test receipts, authenticated checker replay outputs, actual original/relocated build receipts and saved recorders, current commitments, preservation summary, and independently authored review sources. The full external dossier also retains each command stdout, diagnostic copies, and mutation fixtures. The counts 103, 39, 832, and 737 describe tests with overlapping purposes and must not be summed as independent theorem counts. This review provides release-tool acceptance for the named bytes only; mathematical acceptance and direct all-page layout inspection are separate work.
