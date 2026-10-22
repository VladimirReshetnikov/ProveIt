COLLECTION-FIRST QUOTIENT PROOF COMPONENTS

Baseline repository:
https://github.com/VladimirReshetnikov/ProveIt
Commit: 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95
Compiler: Lean 4.32.0

Run from this directory, with a checkout of that exact commit:

  python3 check_repository.py /path/to/ProveIt /path/to/lean

The checkout must contain Computability/BusyBeaver/Lean,
Logic/FirstOrder/Lean, and SetTheory/ZF/Lean. No Mathlib download is needed
for these components. The script writes build/ plus repository-check.log
and repository-check.json next to itself, and never edits repository files.

This checks 35 modules (30 repository dependencies, 5 proposal modules).
The JSON records the compiler version, baseline commit, source hashes and
exit status for every module. The log records the actual axiom reports.

The two quotient adapters retain the complete current theorem statements
under fresh namespaces. The WF adapter is a second application of the
same generic partial-Replacement-to-Separation theorem. Production sources
and the complete K215 endpoint have not been rebuilt or modified.

SEMANTIC_DESIGN.md explains the mathematical proof, dependency reordering,
raw-trace compatibility obligation, exact checking scope and honest size
accounting. Local proof-body reductions are not net repository savings.

QuotientCollectionFirst.lean incorporates the repository's existing
KQ1Collect proof and liftEnv helpers, with attribution in its header.
Retain the upstream repository license and attribution when integrating.
