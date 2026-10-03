# Portability and provenance adaptation ledger

## Immutable scientific identity

The delivered optimized `source.json` is byte-identical to the frozen producer
artifact and has SHA-256
`fa61d06178d718511232a80a05e02192d940fde3c273f0c202f0623253b2ade3`.
The six companion generated files (`primitive3.json`, `normalized3.json`,
`reversible5.json`, `reversible2-primitives.json`, `certificates.json`, and
`build-stats.json`) are also unchanged. The optimized generator and loader are
unchanged. The six retained files in `dependency/` and all three
`compiler-reference/` files are unchanged.

Every active check begins with a mandatory known-input hash verification,
either directly or through the baseline helper. `verify_pins.py` contains fixed
SHA-256 values for all seven optimized outputs, the unchanged optimized
generator/loader, all retained source/compiler
inputs, and the original baseline generator/loader/output-pin specification.
The exact package manifest additionally covers all adapted scripts, proofs,
receipts, and documentation. These are content pins, not digital signatures or
a replacement for the provenance of the trusted report/source hash.

## Eliminated external dependencies

The producer's independent relabel audit and rebuild verifier previously read
a neighboring predecessor release. The portable checker instead runs the
bundled **original, unchanged** `baseline/build_source.py` in private temporary
storage using the same pinned `dependency/virtual3.json`. It requires every
regenerated file to match the seven mandatory historical output hashes in
`baseline/expected-outputs.json`, including baseline source SHA-256
`38c586706fa1069442d3e5103151adb156448b7d7c783f5c46d9d507b87fe73a`.

The graph checker then reads these fully materialized, pinned baseline tables;
it never imports either generator. This preserves independence of its graph
reconstruction and arithmetic checks. Baseline regeneration is an input
materialization route, not a replacement for the independent row checks.
The original loader is bundled for exact function-AST comparison. No optional
external-path fallback exists. A missing pin or mismatched dependency fails.

Only one copy of the new literal tables is delivered. No old table archive,
third-party PDF/scan image, full primary-paper text extraction, development log,
cache, or unused historical checker is included. The compact 30-cell TM table,
its independently transcribed comparison columns, and pinned dependency rows
are sufficient for all executable checks. Bibliographic URLs remain citations
and are never fetched during replay.

## Active script changes

- `check_primary_table.py`: added mandatory scientific-input verification and
  changed its receipt to identify primary-paper inspection as historical;
  still compares all 30 entries against the independently transcribed columns
- `verify_virtual3.py`, `validate_source.py`, `verify_affine.py`,
  `class_expansion_ledger.py`, `test_loader.py`, `test_concrete.py`, and
  `verify_initialization.py`: added mandatory scientific-input verification;
  the mathematical and literal traversal checks are unchanged
- `independent_audit.py`: added mandatory pins and clarified that unavailable
  primary visual inspection describes the producer's history, not a new fetch
- `independent_relabel_check.py`: added mandatory pins and replaces its external
  predecessor root with `regenerated_baseline()`; every row reconstruction,
  relabel check, all-natural injection condition, counterexample, 336 embedding
  checks, 1,398 history traces, and 13 physical prologues remain active
- `verify_rebuild.py`: rewritten to compare a fresh new build byte-for-byte and
  a fresh old build to all mandatory historical pins; it deliberately does not
  claim to revalidate the entire external frozen release
- `verify_exact_delta.py`: added a complete table/dimension/name delta census,
  explicit eight-row five-counter delta, and old/new predicted prologue costs
- `verify_pins.py`, `baseline_support.py`, and `offline_stage.py`: added mandatory
  pin checks, temporary baseline materialization, and offline audit enforcement
- `run_checks.py`: replaced with non-mutating normal/optimized fresh-copy replay,
  canonical-output comparison, byproduct checks, and negative controls
- `verify_manifest.py`: replaced with exact-inventory verification; it rejects
  extra files and symlinks as well as missing or mismatched files;
  `write_manifest.py` is the explicit release-author inventory writer

There is no Python `assert` statement in any active stage; explicit exceptions
remain effective with `-O`. The bundled reference compiler is a mathematical
reference, not an active full universal-CA allocation stage.

## Documentation and historical receipts

The proof/audit documents have a portability note distinguishing inherited
mathematical and visual provenance from this replay. The optimization note and
relabel audit identify the regenerated-baseline route. Other mathematical
arguments are retained. `README.md` and this ledger describe current commands.
`PROVENANCE.json` is an adapted current record with inherited source citations.

`historical/predecessor-preservation-receipt.json` is explicitly sanitized and
historical. It retains the original receipt/manifest/source hashes and bounded
counts; it excludes a developer-log/cache listing. It records the earlier
preservation check and **is not** a claim that portable replay re-reads those
external files. `historical/portability-adaptations.json` gives the packaging
comparison hashes for inherited files and labels unchanged versus adapted
bytes. It is not a substitute for the exact current manifest.

Current scientific receipts and saved traces are recomputed by the full fresh
normal/optimized harness. `replay-receipt.json` describes that packaging-time
execution. No historical PASS is used as a substitute for a current executable
check. The report12 lower-bound theorem, primary universality theorem, and
human-readable compiler correctness proof retain their stated dependency scope.

## Exact delta caveat

Four of 233 collision pairs swap labels, changing exactly eight named
five-counter rows. Five-counter controls and row-name sets are identical.
The prime expansion's private-name allocation can propagate those changes, so
the expanded two-counter control-name set is not identical even though every
layer's numerical dimensions are unchanged. No identity or conjugacy of the
old and new CA global maps follows from equal compiler geometry.

## Sealed orientation-optimality proof addendum

The three files copied into `orientation-addendum/` are the completed producer
`FIRST_ENCOUNTER_OPTIMALITY.md`, `first-encounter-independent-audit.md`, and
`first-encounter-manifest.json`, all byte-identical and pinned. Unqualified
references in those notes to the existing macro/audit files refer to this
subpackage's parent directory. No source, builder, old checker, or trace was
changed to add this theorem.

The first-encounter theorem and the `2^227` startup-optimal assignments concern
only the `2^233` static pair orientations within the fixed normalized source,
recorder, and prime templates. They make no claim of a globally optimal
universal machine. The independent mathematical audit is supplied in full.
Its recorded 4,096 orientation/input arithmetic comparisons, 36,864 boundary
checks, and 975 suffix comparisons are inherited finite evidence, not newly
executed literal-source paths in this package.

`verify_orientation_pins.py` is a new **artifact-identity check only**, and its
`pin-verification-receipt.json` says `PIN_MATCH`. It validates all sealed hashes
and the addendum manifest's two-proof-file scope. It is included in both fresh
replay modes, but is not represented as an executable theorem prover. The
addendum's original manifest covers the two original notes; the portable outer
manifest also covers the original addendum manifest and new pin receipt.

## Report 18 extension: cellular-clock domination

The preceding sections describe the retained Report 17 package. Report 18
changes no machine table, builder, loader, compiler reference, or inherited
proof. The new proof `cellular-clock/CA_CLOCK_DOMINATION.md` and final independent
`cellular-clock/audit/AUDIT.md` are copied byte-for-byte from their sealed
producer package. The shared-offset proof in `certificate-reference/` is also
byte-identical and mandatory-pinned; it is reference-only, with no certificate
code or universal polynomial replay claim.

All six new stages are mandatory in both fresh replay modes. There are no
optional external-file checks, sibling-directory fallbacks, or skipped audit
programs. Both startup comparisons use the same pinned regenerated-baseline
route as the inherited graph audit. The new independent audit still performs
its own graph reconstruction, prime-clock accounting, and row traversal; the
baseline generator only materializes its already pinned input tables.

Changes to original cellular-clock programs are limited to the following:

- `clock_verify.py`: inject package-local mandatory pin verification and require
  the bundled source root; the default source points to the package parent
- `compare_empty_startup.py`: receive the pinned regenerated baseline in a
  context manager and use the bundled optimized source; all clock logic remains
- `audit/check_ca_clock.py`: local pinned source/baseline inputs; retain and check
  all five generated graph/source files for both machines; use bundled pinned
  compiler/ledger files instead of missing duplicate baseline copies; original
  external manifest reads are replaced by the mandatory manifest stage. Input
  receipt keys are stable logical names, never private absolute paths
- `audit/check_proof_corollaries.py` and `audit/check_old_new_startup.py`: local
  pinned inputs, regenerated baseline context, stable output names, and stable
  source labels for temporary baseline paths
- All independent audit receipts replace `python_optimization` with a shared
  `mode_policy` statement. The aggregate records actual interpreter flags and
  independently requires normal/optimized byte agreement
- `verify_manifests.py`: replace external full-workspace reads with mandatory
  locally pinned source-manifest identities, the relevant scientific-byte
  comparisons, complete retained Report 17 inventory checks, reversible edit
  verification, and seven regenerated baseline-output comparisons. Packaging
  separately verified every entry of the original inventories; this historical
  inspection is explicitly distinguished from portable replay

`run_checks.py` extends the inherited offline harness from 14 to 20 stages and
21 to 28 canonical output files. It also negatively tests absence and corruption
of every mandatory scientific-input pin, including all new proof/reference/source
manifest pins. Three unchanged producer outputs (the main clock receipt, old/new
clock receipt, and full five-counter traces) must match their sealed producer
manifest hashes after each live replay. `verify_pins.py` extends the
immutable pin catalog, including saved row traces and the target ledger used by
new checks. `write_manifest.py` changes the release label. `README.md`,
`PORTABILITY.md`, and `PROVENANCE.json` explain the new scope. Mathematical
formula and traversal bodies are unchanged in all ported scientific scripts.

`historical/report18-adaptations.json` gives exact original/portable hashes and
reverse line edits for all adapted inherited or producer scripts/documents.
The manifest checker reconstructs original bytes from those edits and requires
their identities to match the pinned original manifest. Generated receipts are
separately recreated and compared by the aggregate, rather than represented as
source-code edits. The final outer manifest binds all adapted/current bytes.
These hashes are identity checks, not digital signatures or a formal proof.

Original producer manifests are retained byte-for-byte as historical records;
they include hashes for excluded logs and old output files, but none of those
logs or absolute-path receipts is delivered or required. The unchanged proof
and audit notes may discuss those producer-time checks; current executable
coverage is the aggregate, not an inference from their historical prose.
