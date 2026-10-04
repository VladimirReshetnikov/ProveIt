# Report 61 release-tool review

Date: 2026-10-04 UTC. Verdict: PASS for the exact source and tool bytes in SOURCE_PINS.json, within the limitations below. This is a release-engineering review; mathematical and visual approval are supplied separately.

## Final bindings

- build_report61.py: `afbebee95df6497f1308dd329d83afed9f13887775480ebb5dc65e321ea28b0d`
- release61.py: `bcbb67b4cf45852afe4990aa9765a558dd1f68b51a0cbc3546405f4cc6330513`
- INPUT_PINS.json: `acfe4a9a7ac4247b29203c28af9e9907d5e05cfea1e454ac65a846b2221e8c45`
- BUILD_DEPENDENCIES_LOCK.json: `b66cdb2bac9cf5d1b4163d181145aaec996e4217423a119a680d14354760b09b`
- MANUSCRIPT_PINS.json: `768309347285fb5c98be4a3a0c691755cb0228b373543beb486f04797ad8f277`
- Standalone Report61.tex: `133122c9c7c2c894fdbe30a67d9f5274d9d5293d8bc638a212c9e883181af683`
- Final 19-page Report61.pdf: `bb9f61e0620fd23186b351c1427521f83c6eacd90ce18717417235f2fc7d4893`

## Inspection and changes before approval

Both initial tools were read before first use; their initial hashes were 2e85258122b40c2a85456d1e32bbfe6e9b78893443ff009206b810697fecd665 and 7e480f1138e2d4418f698e845c39d429c0cc5eb5f50db3ff482238b0bbe1ae74. Report60 tools were read only as design references and left unchanged. The approved Report61 versions close these gaps:

1. The initial builder's dependency JSON was an observation receipt, not a lock. An explicitly labeled bootstrap build collected installed dependencies. Its receipt was inspected and promoted to the pinned lock. Ordinary builds now authenticate that lock, all six executable name/resolved-path/byte records and all 270 TeX/font-map inputs before invoking TeX; then require equality with the union of actual format-generation and every compile-pass recorder input. Inputs and executables are checked again afterward. Bootstrap refuses an existing lock. The original bootstrap receipt explicitly says toolchain_lock_verified=false; all final reproduction receipts say true.
2. All 19 frozen science/audit files, their exact subtrees, both manifest payload maps and both SHA256SUMS lists were authenticated as inert data. The pinned input map includes the manifests and checksum lists themselves. Extra files, extra frozen directories, deletion, corruption, symlinks, hardlinks and special files are rejected.
3. JSON parsing rejects duplicate keys and nonfinite values; manuscript, dependency and release manifests have strict schemas and exact integer/hash records. Source flattening requires exactly one of each named module input, refuses remaining input/include commands and checks byte equality with standalone TeX.
4. PNG validation now checks every PDF page, exact page numbering/count, chunk bounds/CRC/order, one valid RGB8 IHDR, optional correctly placed and formed pHYs, complete IDAT/IEND, bounded exact decompressed raster size, filter-byte range and absence of trailing data. It is deliberately a validator for this renderer's RGB8 PNG output, not a general PNG implementation.
5. Release creation rejects unsafe member names, canonical-path aliases and existing or internal destinations; verifies generated ZIP inventory/CRCs/payload; extracts into a fresh private temporary directory and compares the entire extracted byte inventory. Fixed sorted member order, timestamp, permissions and compression settings produce deterministic ZIP bytes in the tested environment. A supplied manifest SHA verifies the exact sealed inventory. A stale existing manifest is refused, and prepare refuses sealed trees.

A supplementary independent source inspection identified the all-pass recorder and pHYs issues before final approval; both were corrected and exercised below.

## Final evidence

The final fixture suite passed 87 CLI cases (8 expected successes and 79 expected rejections). All rejected operations preserved their copied source inventories, bytes and recorded file metadata. Tested refusals include source and destination symlinks/hardlinks, FIFO, unsafe names, relative/dot/dotdot/double-slash/trailing-slash paths, existing outputs, release overlap, missing parents, frozen-file mutations/extra/missing entries, malformed/duplicate/nonfinite JSON, boolean byte sizes, incorrect or unsafe dependency records, altered modules/standalone TeX, unresolved module inputs, stale/invalid manifests and incomplete Python isolation flags. Optimized Python is intentionally rejected, including the tested -O invocation; the tools do not depend on assertions for guards.

Clean, hostile-environment and extracted-source locked builds reproduced the final PDF byte for byte. Clean and hostile builds also produced byte-identical PNGs for all 19 pages. The hostile fixture supplied poison PATH executables, Python startup/import files, HOME/TMPDIR, TeX class/format/search locations, locale/time/epoch, shell-escape and file-access settings; none changed output or executed the poison sentinel. All compiler subprocesses receive a newly constructed environment; temporary work is explicitly under /tmp and does not inherit TMPDIR. TeX uses a freshly generated format, private cache/home, no shell escape, restrictive input/output policy and disabled automatic font generation. No blocking final layout/reference warnings occurred.

The PNG suite validated every final page and rejected 15 malformed PNG variants, including CRC-correct malformed compressed data, dimensions, filters and ancillary metadata. Four additional integration probes passed: an input inserted only in the first-pass recorder was retained and rejected by post-build lock equality; corruption of a middle-page PNG, omission of a middle page, and an extra page all failed without a successful build receipt. These four probes deliberately instrumented the inspected builder's output boundary on throwaway copied fixtures; they are fault-injection regressions, not claims that real TeX produced those faults.

Two fixture ZIPs were byte-identical, and their extracted release verified against its manifest and rebuilt to the packaged PDF. Their archive hash in TEST_SUMMARY.json belongs to the test fixture (whose visual record is explicitly marked as a fixture), not the later deliverable ZIP. The finished release receives its own separately supplied manifest/ZIP hashes after supporting audit records are copied. No final deliverable ZIP hash is claimed here.

## Preservation and execution boundary

All 19 original frozen release files retain their initial hashes, lengths, modes and modification timestamps; frozen-before.json equals frozen-after.json. Only owned build/release tools, independent engineering-test harnesses and installed TeX/Poppler programs were executed. Frozen author scientific code, independent scientific checkers, constructors, upstream executables, simulators, stored collision schedules and Lean were not executed by this review. The portable arithmetic adapter has a separate review; its checker bytes were not changed here.

## Limitations and use

- Trust the interpreter, standard library, installed operating system and filesystem. This is not an OS/network sandbox and does not protect against hostile concurrent replacement, bind-mount aliasing, compromised loaders or kernels. The guards target quiescent ordinary POSIX filesystems; O_NOFOLLOW must exist.
- The toolchain lock authenticates named executable bytes and recorded TeX/font-map files. Python, dynamic libraries, kernel, Poppler ancillary dependencies and the complete system configuration are not locked. The observed byte reproducibility is for this authenticated environment; a different toolchain is expected to fail the strict lock.
- Recorded TeX inputs are checked before execution if listed in the lock, and the complete observed union is checked afterward. An unexpected input may have been read before the build is rejected. Owned manuscript bytes must be reviewed; this is not an untrusted-TeX safety sandbox.
- Checks protect and authenticate bytes and package structure, not mathematical truth or the substantive correctness of a visual-review note. prepare intentionally regenerates only the two authoring outputs and requires an unsealed authoring copy. Review and a fresh seal are needed after edits.
- Output failures can leave a partial fresh output directory or archive for diagnosis; there is no transactional rollback guarantee. No existing destination is overwritten.
- This audit's harnesses record absolute test-workspace paths and are provenance evidence, not the portable scientific replay interface. Raw logs and copied fixtures remain in /workspace/shared/report61-release-tools-independent-review-20261004. The release includes concise source-bound results and harness source.

Use python3 -I -S -B with the authenticated manuscript and lock digests, a fresh external output path, and --require-packaged-match to check the delivered PDF. Authenticate the release against externally supplied final manifest/ZIP hashes before calculating local command-line pins from it.
