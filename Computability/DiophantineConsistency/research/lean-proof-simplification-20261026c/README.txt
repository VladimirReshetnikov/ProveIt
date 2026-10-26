SHORTER LEAN PROOFS FOR DIOPHANTINE CONSISTENCY
26 October 2026

Reviewed repository:
  https://github.com/VladimirReshetnikov/ProveIt
Reviewed commit:
  60e9c5d620c6c387d932876cfa2d9376f64ea56c
Lean:
  leanprover/lean4:v4.32.0
Mathlib:
  81a5d257c8e410db227a6665ed08f64fea08e997

START HERE

Read report.pdf (or report.tex). It contains the full source-grounded review,
mathematical explanations, prioritized proposals, implementation cautions,
and verification scope. Each cited repository module links to the pinned
commit. The report's 18 sections cover immediate reuse, arithmetic identities,
scanners, coefficient proofs, shared circuit blocks, and object-model proofs.

The repository was reviewed without editing its tracked files. The supplied
patches are review artifacts; no commit or pull request was created.

MOST CONCRETE RESULTS

* Seven private list proofs can use existing Lean-core lemmas. The patch
  removes 40 physical lines and applies cleanly; its replacement terms are
  checked, but the five complete modified modules were not rebuilt.
* The generic scanner framework has seven checked theorems with no axioms.
* The half-radix identity, bound, and parity facts are checked with Lean core.
* A generic assignment-transport law and elementary row-operation facts are
  checked. Their concrete project integrations remain separate work.
* Two circuit register rewrite lists shrink 19 -> 7 and 36 -> 9. The generator
  and generated file are patched together. Source transformation checks pass;
  generated-module Lean replay is still required. The emitted Lean file loses
  844 bytes; its physical line count is unchanged.
* The Split and Gap natural circuits have an exactly matching 99-node suffix
  after an explicit reference map. Source pins and regeneration of four Lean
  files were checked. A shared-block Lean semantic theorem is proposed.
* Coefficient-bound and coefficient-map candidates remove 549 and 303 physical
  lines. Their last isolated-data proof check timed out after 90 seconds
  without diagnostics. These are UNVERIFIED candidates, not completed savings.

FILE MAP

report.tex, report.pdf
  Complete report. The TeX source has no private external content inputs.

lean/checked/
  ScannerCore.lean, ScannerAudit.lean
  LookupCleanup.lean
  HalfRadix.lean
  AssignmentTransportCore.lean
  RowOperations.lean

  These files have successful checks for the exact packaged hashes. All except
  RowOperations use only the core Lean toolchain; RowOperations imports two
  small Mathlib modules. A checked generic lemma does not certify a full
  project migration. See evidence/verification.json.

lean/candidates/
  AssignmentTransport.lean
  DAGInvariant.lean
  CircuitCoreRefactors.lean
  SplitCircuitRegisters59.short.lean
  NativeCoefficientBounds.refactored.lean
  NativeNinePolynomial52.refactored.lean
  MapRowCoefficient.lean
  IsolatedCoefficientChecks.lean

  These are proposed project-dependent integrations or an isolated check
  harness. They must not be described as kernel-verified. The last harness
  contains exact extracted coefficient/envelope definitions; its proof attempt
  timed out. The extracted-data hashes can be verified separately.

patches/
  lookup-cleanup.patch
  split-register-cuts.patch
  coefficient-refactoring.patch

  All three passed git apply --check on the pinned snapshot. Applicability
  does not imply successful compilation or downstream integration.

scripts/
  audit_sources.py       Reproduce source census, hashes, tactic token counts,
                         declaration-span estimates, and import edges.
  inspect_shared_tail.py Check source pins, four regenerated Lean files, and
                         the exact 99-node suffix equality.
  verify_extractions.py  Check that the isolated algebra harness contains the
                         exact pinned coefficient/envelope declarations.
  check_core.py          Replay the small checked examples and record results.
  build_report.sh        Run XeLaTeX twice.

evidence/
  verification.json      Consolidated, explicitly scoped status.
  source_metrics.json    Census summary; all 546 active Lean files included.
  source_files.csv       Per-file source hashes and metrics.
  declaration_spans.csv  Lexical approximate spans, not Lean AST measurements.
  imports.csv            Direct import edges.
  core-replay/           Actual replay logs and commands for packaged core files.
  syntax/, circuits/, arithmetic/
                         Detailed check receipts, source comparisons, hashes.
  build-limitations.json Resource-limited attempts and interpretation limits.
  pdf-quality.json       Final document checks.
  upstream-lake-manifest.json
                         Exact dependency manifest from the reviewed snapshot.

notes/
  Three detailed family-specific reviews with precise source anchors.

MANIFEST.sha256
  SHA256 of all delivered files except this manifest itself.

REPRODUCTION

1. Use a clean checkout at the exact commit above. Do not silently substitute
   a newer main branch or Mathlib revision.

2. Reproduce read-only source observations from this archive's root:

     python3 scripts/audit_sources.py /path/to/ProveIt /tmp/dc-source-audit
     python3 scripts/inspect_shared_tail.py /path/to/ProveIt
     python3 scripts/verify_extractions.py /path/to/ProveIt

   The shared-tail checker loads the pinned repository generators in read-only
   mode and compares their renderings with the tracked source files. It does
   not write to the checkout and does not prove a Lean semantic-block theorem.

3. Replay all core-only checked examples:

     python3 scripts/check_core.py --lean /path/to/lean-4.32.0/bin/lean \
       --out /tmp/dc-core-checks

   To also check RowOperations against an already prepared pinned Mathlib
   environment, add --repo /path/to/ProveIt. The script does not download
   dependencies, invoke lake update, apply patches, or edit the repository.
   It uses single-threaded Lean with a configurable memory cap and timeout.

4. Check patch applicability before any integration:

     git -C /path/to/ProveIt apply --check /absolute/path/to/patches/lookup-cleanup.patch

   Apply a patch only in your chosen working branch/worktree. Then build the
   modified modules and their downstream checks, and compare #print axioms for
   the affected public endpoints. Follow the report's generator-output advice
   for generated files. The archive does not claim these full replay steps
   have already succeeded.

5. Rebuild the PDF:

     bash scripts/build_report.sh

   Requires XeLaTeX, standard TeX Live packages, Latin Modern fonts, and
   DejaVu Sans Mono. The PDF was rendered and visually inspected after the
   final build. No generated page images are needed to compile the report.

INTERPRETING COUNTS AND CHECKS

Physical lines include comments and blanks. The active tree has 546 files and
73,971 lines: 326 library/aggregate files with 66,857 lines, and 220 check/audit
files with 7,114 lines. Historical manuscript copies outside this active Lean
tree are excluded. Tactic counts are lexical after comment/string masking.
Generated lines are not counts of independent mathematical arguments.

No whole-project build, end-to-end consistency equivalence, global percentage
saving, or speedup is claimed. Shared-host memory pressure prevents meaningful
benchmark comparisons in this session. Exact candidate source-size reductions
and successful general-lemma checks are reported separately.

LICENSE AND PROVENANCE

The reviewed project is released under the MIT No Attribution license.
licenses/ProveIt-MIT-0.txt preserves its license text for the adapted snippets
and proposed full-file replacements. Dependency source and compiler/cache
binaries are not bundled. Exact pins, source hashes, and check receipts are
included for reproducibility.
