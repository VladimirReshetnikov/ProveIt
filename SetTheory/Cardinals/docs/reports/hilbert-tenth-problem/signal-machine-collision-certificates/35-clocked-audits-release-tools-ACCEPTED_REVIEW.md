# Accepted model-performed independent release-tool review

Date: 2026-10-04. Scope: Report65's fresh report-owned builder and release/archive
tools, their documented checks, and reproducibility of the final article. This is
model-performed review and testing, not human inspection, mathematical validation,
or a fresh formalization of the report's inherited research.

## Decision

**Accepted for the documented static report-build and release workflow.** The final
frozen versions pass 99 expected regression outcomes plus one independently crafted
local-header-only ZIP-extra-field rejection. All originally demonstrated gaps are
fixed. No current blocking release-tool finding remains.

The positive locked build, hostile-environment build and extracted-ZIP build are
byte-identical to the final pinned PDF and flattened TeX. Each reports
`sealed_artifacts_matched: true`, no selected layout warnings, and exactly 266
observed pinned system inputs. Repeated ZIP creation is byte-identical in the tested
Python/zlib environment. Candidate and original source preservation checks pass.

## Accepted versions

| Item | SHA-256 |
|---|---|
| `tools/build_report65.py` | `2e7139e00744d75cd353f096387d868b930bf8c53b9868f9ae903e4ad41d4e0c` |
| `tools/release65.py` | `1ac3a8066038014bb7cfc674fc00f483442279dd8e77662e475409879e4140ee` |
| `tools/BUILD_DEPENDENCIES_LOCK.json` | `655822c2dee2f0f4d1a0a8d00208579e4a53d558ce8ca385557e1d88c5e614e2` |
| Final `Report65.pdf` | `729213d2a1b3cab8bd00912a0bbdc8a035ebd26c4e4af22da4aab5e5e2b89bf8` |
| Final `Report65.tex` | `870025b5d7f633890db20ae3d166deeafcf83657f7fc4746ad221aa933719857` |

The final article remains 20 pages. The review-owned sealed copy's manifest pin is
`77f87162e24c2fdf3c859276d311edf9fd9cd80cc3b214e20d8fd46ce13d2320`;
its repeated 64-member ZIP hash is
`79062e2c31d18ff5f045fb37d3e7012203ef81f99a9cebc2c5c8d9539264d05e`.
These two pins identify the review copy, not the eventual release after QA records
are added. The final release needs its own externally published manifest digest.

## Confirmed fixes

1. **Sealed artifact equality.** A deliberately inconsistent but newly sealed flat
   TeX copy now fails before creating its requested output directory. A deliberately
   inconsistent but newly sealed PDF fails after compilation, before promoting the
   final output PDF or writing a success receipt. Successful receipts explicitly
   state that sealed artifacts matched. This validates the assertion, not just the
   production of output hashes.
2. **Exact directory set.** An extra empty directory now fails sealed-build
   preflight, consistent with release verification and archive creation. The builder
   also snapshots directory modes, modification times and change times during the
   build and requires them to remain unchanged.
3. **Manifest permissions.** Filesystem verification, sealed-build preflight and ZIP
   checking reject manifest mode 0777. Seal explicitly sets mode 0644; a dedicated
   umask-0077 test proves it does not produce a self-invalidating mode-0600 manifest.
4. **Canonical ZIP metadata.** Central extra fields, member comments, archive
   comments and local extra fields are rejected. The separate local-header test
   inserts an extra field only into a local header while preserving empty central
   extras and readable unchanged member content. It fails for the intended local
   extra-field check.

## Coverage

The final regression suite reruns the original accepted positive tests and the
adversarial matrix: locked executable/input preflight; bad external manifest or
dependency-lock pins; missing lock; unsafe locked paths; hostile inherited TeX,
PATH, HOME, locale, date and shell settings; output existence/overlap/symlink-parent
checks; sealed draft-mode refusal; changed/missing/extra files and ordinary file
modes; symlinked files/directories and FIFOs; changed manifest content; unsafe,
duplicate or hash-invalid input pins; empty directories; duplicate, extra, missing,
unsafe-path, nonregular, encrypted, changed-content, changed-mode and changed-time
ZIP members; normal extraction and expected metadata timestamp differences.

The README's updated `python3 -I` invocation was used in the final pass. The main
test interpreter is Python 3.12.14. A supplemental Unicode-path check also used
system Python 3.13.5. Python 3.9 compatibility is supported by source syntax review,
not an actual execution on a Python 3.9 installation.

## Preservation and execution boundary

All execution and mutations took place in newly owned review copies and fresh
external output paths. Both complete tool scripts and their changes were inspected
before execution. All 49 pinned original input files retain their bytes, byte sizes,
modes, modification times and change times. The candidate's preexisting files and
the sealed owned base also retain their checked metadata. Ordinary reads may affect
access times, which are outside the pins and the preservation claims.

No inherited author/upstream research or audit mathematical program, physics
simulation, saved accepting schedule, native interpreter or Lean was imported or
executed. The review ran only inspected report-owned release tools, newly inspected
static review drivers, ordinary system TeX/PDF tooling and unzip.

## Limits and accurate assurances

- A manifest digest supplied independently is the trust anchor. Sealing a mutated
  copy authenticates that different copy; it cannot establish that the article or
  research is correct. Adversarial resealing here was confined to labelled fixtures.
- This review establishes the exercised checks and reproducibility in this
  environment. It does not prove a general hostile-TeX sandbox, adversarial race
  resistance, arbitrary ZIP-parser correctness, or reproducibility on every OS.
- The lock pins five executable identities and 266 TeX/font inputs. It does not lock
  the Python interpreter, the complete OS/shared-library stack or all runtime state.
- Preflight failures exercised here leave their fresh output absent. Later
  compilation or PDF-equality failures can retain diagnostic work files. No claim
  is made that every failure precedes every output.
- Archive extraction was tested with the installed Info-ZIP unzip. Standard Python
  archive extraction is not assumed to preserve Unix modes automatically.
- The report's mathematical scope, literature, visual layout and inherited proof
  trust dependencies are outside this release-tool acceptance.

## Evidence and packaging

The original findings remain in `ORIGINAL_REVIEW.md` and `RESULTS.json`; they apply
to superseded initial tool hashes. Final results are in `delta/RESULTS.json`
(99/99), `delta/LOCAL_HEADER_RESULT.json` (pass), the final `BUILD.json` receipts,
and `delta/logs/`. The final regression ledger SHA-256 is
`6bfd0746bd02b9f7cb6cea2189a1475ddc7b8ccdc71dab1d92ab9d7d5aadb0ef`.

Use the compact `publication/` subset when adding evidence to the eventual release.
The full review workspace deliberately contains rejected ZIPs, symlinks and FIFOs;
it is a test fixture archive, not a safe release-source subtree. The publication
subset contains only ordinary files and its own hash inventory. It preserves the
initial findings as history and the final acceptance as the applicable decision.
