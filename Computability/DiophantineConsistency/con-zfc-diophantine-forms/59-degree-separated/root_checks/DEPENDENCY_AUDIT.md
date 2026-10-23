# Independent dependency and reproducibility audit

## Scope

The six current authored deliverable families are encoding, sun, nine,
signed, positive and short. Incoming archives and search scratch are not
executed. The audit copied the six families into a fresh temporary
tree without incoming archives or other research directories, then ran only
reviewed authored builders/checkers. Historical upstream Python was not executed. Source
JSON, proof text, and coefficient bytes were treated as data.

This is a packaging/arithmetic replay audit, not a new proof of unbounded
compiler semantics or consistency. The repaired executable snapshot was taken on
2026-10-23 at approximately 19:32 UTC after the six families froze. All 21
successful commands and the expected nine-variable optimized rejection
behaved correctly. Final source, path, manifest, PDF-metric and snapshot
identity checks also pass.

## Findings communicated immediately

1. The initial positive/check_merger_independent.py still expected operation
   counts 104/97/96/105. The reproducible current product/system/shifted/SOS
   counts are 102/95/94/103. Both normal and optimized runs failed at that
   stale operation-count assertion, after the algebra/literal checks.
   The author updated the checker and review records; the repaired checker
   passed normal and optimized runs in the fresh final snapshot.
2. The short/circuits JSON binding originally used COEFFICIENT_BINDING.json
   without declaring that it was relative to the family root. It now uses
   ../COEFFICIENT_BINDING.json, explicitly relative to each circuit file.
   The short generator, auditor, circuit files and manifests were refreshed.
   This is metadata only; no polynomial or count changed.
3. signed/ARTIFACT_HASHES.json and encoding/RELEASE_FILES.json were stale
   during active edits. Both final manifests now match. The signed author
   regenerated coverage over all 70 intended deliverable files, including
   the new compact/split assets. The final metadata receipt reports no stale
   hash and no omitted candidate file.
4. positive/check_ordinary_merger.py requires NumPy. The independent
   check_merger_independent.py is standard-library only, but does not certify
   degree bounds. Final requirements/instructions must retain NumPy for the
   full ray/degree replay, rather than claim the complete package is stdlib-only.
5. nine/verify_nine.py deliberately rejects -O/-OO, with a clear error and
   README disclosure. The separate nine/independent_review.py passes both
   modes. An expected optimized rejection must not be counted as a successful
   main nine audit, nor as silently disabled checks.

## Source, path, and tuple checks

- The metadata checker verifies 76 local source-pin records and 51 active
  binding/payload/circuit-relative paths. No missing active file or incorrect
  source/binding hash was found in that scan. Git-blob hashes are also
  recomputed for every supplied member-level Git-blob identity. Archive-level
  authentication remains the separately pinned incoming-archive evidence;
  this audit does not require or pretend those archive bytes are in the release.
- The Sun, signed, positive, short and primary-nine old31 payloads are
  byte-identical, complete four-port tuples: beta=2^1064921-1, shifted MF,
  native mask population 1064921, and the required mask phases.
- Nine's native packet52 tuple is kept separately for comparison circuits.
  Primary generated circuits declare old31; comparison circuits declare
  native52. No individual port mixing was found.
- Canonical Python modules contain no /workspace or /tmp dependencies. The
  fresh-copy tree contains only the six deliverable families, and no canonical
  checker imports incoming archive or other historical research code.
- encoding/explore.py has an optional legacy wave7 fallback, but it is
  discovery provenance, not imported by verify_split.py or test_split.py.
  The explicit encoding release list excludes optional discovery files.
- sun/data/coefficients_binding.json retains an obsolete historical
  complete_interface_proof path. INSTANCE.json explicitly overrides
  historical relative metadata. The current complete proof exists at
  sun/upstream/COEFFICIENT_PROOF.md and is source-pinned. Original bindings
  in other families are likewise preserved inert provenance, not active adapters.
- The encoding proof's common source-scale example was updated from
  2^2140030 to 2^2134940 during this audit. Nine's preserved upstream copy
  still records the former example, but nine/PROOF.md independently proves
  its own weaker parity-tuned scale 2^2134939 and does not import the stronger
  old numeric floor as an unmet hypothesis.

## Optimized-mode safety

AST scanning of canonical modules finds one Python assert:
sun/circuit.py:54 validates that a builder's fixed power is a nonnegative
integer. It is not a semantic checker or degree certificate assertion.
The independent Sun checker uses explicit runtime checks and passes -O.
Replacing that input guard with a ValueError would improve defensive
behavior for malformed builder calls, but no check required by the supplied
fixed construction disappears in the independent optimized audit.
All other canonical checker conditions use explicit runtime exceptions.

## Initial isolated replay

All families except the stale positive independent ledger passed their
expected behavior. Encoding's ten corruptions were rejected; Sun's rebuild
was byte-identical; nine and signed recreated their circuit data and
certificates exactly; positive and short builder outputs were byte-identical.
No pre-existing file changed after the copied builders/checkers ran.
Normal and optimized outputs matched for the passing paired checkers.
The initial failure and every stdout/stderr hash are retained in
DEPENDENCY_REPLAY_initial.json and the corresponding input hashes.

## Repaired isolated replay

The latest replay has 21 successful commands, one separately classified
EXPECTED_REJECTION, no failures, and no modified pre-existing artifacts.
All normal/optimized paired outputs agree. The signed checker includes both
the 520-operation degree-11,546,112 circuit and the new compact 518-operation
degree-11,543,632 circuit. Its additional independent source-minimum checker
also passed both modes for both source-padding variants: three universal
polynomial identities and 192 bounded stress cases (120 with negative g).
These bounded diagnostics are not substitutes for the stated all-integer proof.

The executable snapshot is hash-bound in DEPENDENCY_INPUT_HASHES.json.
DEPENDENCY_FINAL_SNAPSHOT_CHECK.json confirms that all current family files
still match it. The observed runtime is CPython 3.12.14 with NumPy 2.3.5.
Any subsequent script/circuit change requires another replay; proof/PDF/
manifest-only changes require refreshed metadata and PDF checks.

All six PDFs contain their currently reviewed metric values, including the
signed nine-page compact recommendation. DEPENDENCY_PDF_METRICS.json binds
the PDF identities and records this textual check. It is not a layout audit
or an independent derivation of those metrics; each author separately
performed the relevant PDF visual review.

## Receipts and reproduction

- run_dependency_replay.py: isolated-copy runner, only authored family code.
- check_dependency_metadata.py: independent path, source-pin, tuple and AST checks.
- DEPENDENCY_REPLAY.json: latest executable replay receipt.
- DEPENDENCY_INPUT_HASHES.json: exact input snapshot.
- DEPENDENCY_METADATA.json: current binding/pin and static results.
- ABSOLUTE_PATH_SCAN.json: authored text scan.
- DEPENDENCY_PDF_METRICS.json: PDF hashes, page counts and metric presence.
- DEPENDENCY_FINAL_SNAPSHOT_CHECK.json: unchanged frozen-input confirmation.
- Per-command stdout/stderr files: full observed evidence.

Final result: PASS for this six-family dependency/reproducibility scope.
There is no unresolved active-path, source-hash, manifest, copied-tuple,
metric-staleness or optimized-check blocker. The documented NumPy dependency,
nine optimized-mode rejection, inert historical metadata, and one nonsemantic
Sun builder assert remain explicit limitations rather than hidden failures.
The parent release assembler must separately verify its final combined PDF,
root manifest and ZIP; those are outside this family snapshot audit.
