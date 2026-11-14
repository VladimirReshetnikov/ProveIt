U213: a 213-state binary Turing machine for Con(PA)
28 October 2026

PRIMARY RESULT

machine/u213.tm has 213 working states (0 through 212), two symbols, one
two-way infinite tape, blank symbol 0, initial state 0, and separate halt
label 213. All 426 transition rows are included. Initialization is counted.

The new mathematical preservation theorem is

  PA proves: Halt(U213, blank) iff Halt(U214, blank).

Together with the supplied U214 numerical-calculus and unary-power-cover
calibration, this gives

  PA proves: not Halt(U213, blank) iff Con(U) iff Con(PA).

This package contains mathematical proofs and executable certificates.
It does not claim a newly compiled Lean, Rocq, MM0, or exported PA proof
of the complete consistency endpoint. See the paper for the precise scope.

WHAT CHANGED

Six closed source-tree rotations preserve all 3,928 primitive instructions
and their complete guarded ordinal control-flow graph. They change 430
addresses and expose two decoder roles with different preceding tape bits.
An existing selector implements both roles, deleting native state 214.
Relative to U214, 15 retained rows change and two rows are deleted.

All 5,109 arbitrary-register symbolic primitive cases passed. Blank startup
takes exactly 95,726 steps and reaches the same calibrated seed as U214.
Independent source, local whole-tape, startup, and dense-label checks pass.

REPRODUCE (Linux/WSL, Python 3.10+, standard library; no network or optimizer)

  python3 -B reproduce.py
  python3 -B reproduce.py --full --report replay.json

The first command reconstructs all machine/source files, checks the manifest,
replays independent local/source proofs and negative controls, audits the
saved runtime's exact coverage and hashes, independently replays blank
startup, and checks the complete included predecessor.

The --full command additionally rederives every symbolic primitive case
from the literal final table and compares the complete records. It normally
takes several minutes. Run without -O or PYTHONOPTIMIZE. Temporary work is
removed automatically. An explicitly requested report is the only output
that reproduction writes persistently.

Exact-byte reproduction was tested on Linux. Use Linux or WSL; native
Windows newline conversion affects the included predecessor's byte checks.

CONTENTS

  paper/report.tex, paper/report.pdf   Research report and editable source
  paper/transition_table.tex          Complete dense table printed in PDF
  machine/u213.tm                    Primary dense literal machine
  machine/u213.native.tm             Same machine in inherited native labels
  machine/sites.json                 Reassociated source (199 distinct subtrees)
  machine/rotated214.native.tm        Intermediate before the final local fold
  machine/state_map.json             Verified dense/native bijection
  machine/delta_from_u214.json        All 15 changed rows and two deleted rows
  inputs/rotations.json              Exact six-step source/table recipe
  inputs/U214_*.zip                  Unchanged predecessor and its dependencies
  code/                             Offline construction and checking code
  evidence/                         Fresh runtime and independent proof receipts
  research/                         Scoped search results and uncompiled sources
  PROVENANCE.json, SHA256SUMS        Source pins and exact release identities
  NOTICE.txt, licenses/              Attribution and inherited licenses

Compressed .json.gz evidence files use ordinary gzip. They retain the full
95,726-step startup trace and every symbolic primitive derivation record.
The full checker rederives its induction schemas rather than trusting a
saved positive status. Research sources are not additional accepted TMs.

PRIMARY DENSE SHA-256
58f43593c862742268c20bb17584913a560a1a8595ce7484ad5f9fcebcfd60a0

PRIMARY NATIVE SHA-256
310364dec119bb64bf8201956c0c14cb37fa4b692fbb7012bfeb7f05e1f27259
