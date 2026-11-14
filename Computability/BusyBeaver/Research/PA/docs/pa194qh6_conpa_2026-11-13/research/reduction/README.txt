QH6 finite state-reduction experiments
=====================================

Place this directory at research/reduction inside the release. It uses the
accepted machine/, construction/, and verification/reference/ directories.
No network or repository checkout is required. Python3.10+ and g++ with C++17
are sufficient. Do not disable Python assertions.

From the release root:

  python3 research/reduction/replay.py
  python3 research/reduction/replay.py --whole-merges
  python3 research/reduction/source_rotation.py

The first command repeats five bounded local searches using frozen windows.
The second also repeats all 62,073 whole-source row-choice mergers (about one
minute, machine-dependent). The third reproduces the rejected 193-control
scanner/address experiment, whose entire source CFG is preserved but whose
literal simulation fails 52 contracts. Outputs go to fresh temporary folders;
use --output PATH to retain an explicitly chosen location.

To rederive both window lists from every source outcome, all literal register
list inductions, unary scan interiors, and complete blank startup, add:

  python3 research/reduction/replay.py --derive-contexts

That longer run checks exact byte equality with the frozen window files. The
literal derivation can take several minutes. To run from another location,
pass --package-root /path/to/release. Compiler executables are created only
in the chosen output folder; they are not shipped here.

All searches are finite. Empty hit lists do not prove state minimality. The
context lists are discovery inputs, and every positive candidate would still
require fresh complete simulation and source-semantic verification. The
accepted machine remains 194 states.

Provenance: action_merge_future.cpp and eliminate.cpp are copied verbatim from
ProveIt@2e00058366845a6e2e0368004fd9ed2050a06a9a,
Computability/BusyBeaver/Research/PA/docs/pa194ns_conpa_2026-11-13/research/low_level.
The start-aware variant differs only by admitting control 74 as a merge partner;
a resulting candidate would need its initial label redirected accordingly.
The whole-source row-choice search is adapted from the PA194HS search package
at that same revision. Context derivation adapts the PA194NS recipe, with new
independent literal-box windows for QH6. Original notices are retained in
licenses/ and alongside the release's shared executors.

No completed count is reported for the interrupted spare-append policy
experiment; it is deliberately absent from the quantified results.
