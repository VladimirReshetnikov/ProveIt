SHORTENING AND SIMPLIFYING PROVEIT'S LEAN PROOFS
26 October 2026

This is a source-specific proposal package, not a newly verified Lean release.
The report is in report/report.tex and report/report.pdf. Read its priority recommendations
first, then inspect the small patches before considering the larger interfaces.

Pinned ProveIt commit
  60e9c5d620c6c387d932876cfa2d9376f64ea56c
  https://github.com/VladimirReshetnikov/ProveIt/tree/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency

Pinned toolchain
  Lean 4.32.0
  mathlib 81a5d257c8e410db227a6665ed08f64fea08e997

STATUS
  Exact source inventories and patch applicability were checked.
  Proposed Lean files have NOT been elaborated or kernel checked here.
  Finite Python tests are sanity checks, not substitutes for Lean proofs.
  No upstream repository changes, commits, or pull requests were made.
  See VALIDATION.json for the final machine-readable scope.

CONTENTS
  algebra_examples/    Nine proof-only proposals in five module patches,
                       before/after harnesses, unchanged-header evidence,
                       measured source sizes, and a read-only auditor.
  checker_examples/   A six-file standard-library cleanup patch, plus
                       iteration, lookup, dispatch and closure prototypes.
  proposals/           Shared free-carrier tail and neutral div/mod theorem.
  prototypes/native/   Word-context, carry and finite-block proposals;
                       a finite mathematical regression script.
  SolutionTransport.lean
                       Guarded existence congruence and composable
                       forward/backward existential obligations.
  baseline/            Original main Lean subtree and selected documentation
                       at the source pin. This is a PARTIAL source snapshot,
                       not a complete runnable ProveIt checkout. External
                       project modules and mathlib are not included.
  evidence/            Whole-project source inventory with hashes.
  validation/          Pinned library API evidence and optional core checks.
  MANIFEST.json        SHA-256 for every other delivered file.

STATIC REPLAY
  Requires Python 3 and Git. From the extracted package:
    python3 -B verify.py

  This checks sealed bytes, all 546 bundled main-subtree Lean sources, the
  nine algebra replacement manifests and patches, the separate checker
  cleanup patch, and finite native regressions. It never runs Lean or writes
  source files. Its PASS must not be described as a Lean verification PASS.

  To inspect all 711 Lean files in a full checkout at the pin:
    python3 inventory.py /path/to/ProveIt
  The package baseline contains the 546 main-subtree files, not all 711 files.
  To reproduce the local umbrella-import coverage (also works on baseline):
    python3 inventory.py baseline --umbrella
  The umbrella does not reach 39 neighboring modules or the 182 separate
  check files. This is an import-coverage fact, not a claim about upstream CI.

OPTIONAL LEAN CORE CHECK
  With an existing trusted official Lean 4.32.0 executable:
    python3 validation/check_core.py --lean /path/to/lean \
      --output-dir /tmp/proveit-core-checks
  Use an output directory OUTSIDE this package. The script installs nothing
  and serially checks three standalone core examples only. It does not
  compile the module patches or establish full-project integration.

FULL ACCEPTANCE BEFORE ADOPTION
  1. Use a disposable checkout at the pin with the exact pinned dependencies.
  2. Establish an unchanged baseline build and preserve its logs.
  3. Inspect and apply each patch separately in that disposable checkout.
  4. Compile dependencies in topological order, ONE Lean process at a time.
     The repository README explicitly warns that LAKE_JOBS=1 and a single
     lake build invocation do not themselves prevent dependency fan-out.
  5. Recheck theorem statements, axiom reports, all affected clients and
     exact witness-count/degree/operation-count theorems. Keep natural,
     positive and unrestricted-integer domains and every sign guard intact.
     Include the independent check/audit modules, not just the umbrella.
  6. Measure elaboration time, memory and proof size independently. Fewer
     source lines do not establish improvements in those other metrics.

Candidate harnesses may use broader imports than production modules and
must be compiled separately: before and after versions deliberately use
the same declaration names. A passing extract is not a passing full module.
The two iteration prototypes are alternatives: prefer the bridge to existing
Function iteration APIs; the core-only file explains the mechanism without
mathlib. Do not introduce redundant parallel APIs unnecessarily.

The original source is retained under the included baseline/LICENSE.
This report does not prove a new equation-to-Con(ZFC) endpoint or an internal
ZFC derivation. The current native-language links remain separate obligations.
