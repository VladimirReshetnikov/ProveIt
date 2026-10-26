Lean proof simplification for the new construction modules
Fourth review, 26 October 2026

Read report/report.pdf first. Its editable LaTeX source is included.

SOURCE AND NOVELTY BOUNDARIES
Candidate source: 09d65a93c9df8684c1a226341d6a5120623d1cdb.
Final bounded comparison: 663fb267f6142ca4c0ea5bcd2d4f607f9a4b0eda.
Repository: https://github.com/VladimirReshetnikov/ProveIt
The final comparison covers 28 manuscripts: 23 placed packets and five
incoming archives. All prior proposals are assumed available for novelty
accounting, not asserted to coexist in a compiled implementation.
See catalog/EXCLUSION_AND_ADOPTION_LEDGER.md and catalog/late663/.
The duplicate exists_coordinate projection cleanup was withdrawn.

RECOMMENDED PROOF-ONLY PILOT
1. physical/patches/order_iso.patch: replace the new finite-ordinal rigidity
   induction by an existing pinned mathlib order-isomorphism theorem.
   WangTiles942PhysicalOrder.lean: 180 -> 156 physical lines.
2. controller/patches/controller_coprime_cardinality.patch: use the existing
   modular cast/divisibility bridge. ControllerAuxiliaryChoice.lean: 50 -> 44.
3. controller/patches/controller_hs_inline.patch: direct small modular
   rewrites remove a private helper. CurrentControllerData2011.lean: 184 -> 169.
Together: three full production files, 414 -> 369 lines (45 fewer).
All public statements, imports and computational definitions are retained.

SEPARATE OPTIONS
- physical/patches/fin_pred.patch changes the nonStartIndex definition body
  to core Fin.pred and uses its successor law. It removes seven further
  production lines. The supplied original-constructor rfl regression has
  NOT been compiled. This option is not described as proof-only.
  If choosing both physical edits, use physical/patches/combined.patch on
  the unchanged source instead of applying both alternatives plus combined.
- word/patches/marker_tail.patch proves the exact marker-only convolution
  response on fields 1991 through 2010. It retains the exceptional bare
  contribution at 2008 and arbitrary numeric control maps. It adds 19
  physical production lines, including all three new helpers and retained
  old wrappers. This is an optional stronger interface, not compression.
- Core plus Fin.pred: 414 -> 362 (52 fewer lines).
- Core plus marker tail: 673 -> 647 (26 fewer lines).
- All options: four files, 673 -> 640 (33 fewer lines).
Counts include comments and blank lines; detailed nonblank/code/token
counts are labeled separately. Do not add alternative variant savings.

VALIDATION STATUS
Every new Lean candidate and regression in this archive is UNCOMPILED.
No Lean elaboration, kernel check, axiom comparison or speed benchmark was
performed. Existing upstream compilation receipts are documentary evidence
only. The archive does not prove polynomial equivalence or internal ZFC
formalization, and does not discharge the explicit hK residue assumptions.

OFFLINE READ-ONLY REPLAY
From any working directory, using Python 3:
  python3 -X utf8 -B /path/to/packet/verify.py
  python3 -X utf8 -O -B /path/to/packet/verify.py
These verify the sealed files, 664 source-to-Git-blob bindings, exact patch
reconstruction and composition, preserved textual interfaces, source
accounting, pinned library evidence, and finite arithmetic/geometry models.
They run four script stages in each mode and print JSON to stdout.
They require no Git, network, Lean, or third-party Python packages.
Finite tests and lexical interface checks are NOT proofs of Lean acceptance.
Do not edit sealed files and then interpret a manifest failure as a proof
failure. Extract a fresh archive for an unchanged replay.

LEAN ACCEPTANCE WORK STILL REQUIRED
Use an authorized build checkout at the candidate source pin, with its
lean-toolchain and lake-manifest.json. Select the desired patches, apply
them to that checkout, and compile each affected module after dependencies
are ready, followed by its Checks modules, clients and normal project checks.
Compile physical/candidate/PhysicalOrderRegressionChecks.lean only with the
chosen predecessor variant. Check #print axioms for retained theorems.
The repository explicitly warns that LAKE_JOBS=1 does not constrain this
Lake version. Keep one Lean process/module at a time in dependency order;
do not start an aggregate build that fans out across stale dependencies.
Do not set LEAN_NUM_THREADS=0. See baseline/README.md, corrected build note.
No timings or inference about performance follow from source line counts.

CONTENTS
report/       LaTeX, PDF, build instructions and PDF QA record.
baseline/     Frozen maintained Lean tree and selected project metadata.
              This is not the complete external dependency/build closure.
physical/     Alternative full files, patches, core/mathlib evidence,
              uncompiled regression and a finite/static checker.
controller/   Two full files/patches, pinned mathlib evidence, rejected
              overlap record and static/finite checker.
word/         Stronger tail candidate, patch, exact accounting and checker.
audit/        Independent combined source/patch/finite audit.
catalog/      Novelty and final adoption/comparison evidence.
evidence/     Main-source hashes, Git bindings and source census.
MANIFEST.json SHA-256 seals for every other included file.

All deliverables are review candidates. No upstream repository changes
were made by this review.
