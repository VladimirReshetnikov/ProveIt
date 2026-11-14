FINITE BOOTSTRAP EXPERIMENTS

No sub-194 blank-start PA-consistency machine was established by these
experiments. The supplied runtime193 table remains an invalid blank-start
candidate. Its runtime contracts and initialization must be distinguished.

Offline replay (Python 3 standard library and a C++17 compiler):

    python3 reproduce_bootstrap.py --output /tmp/pa-bootstrap-results

The replay typically takes several seconds. It checks the pinned runtime
bytes, compiles both search programs, repeats the finite experiments, and
checks exact simulation/transition/outcome counts against the recorded run.
No network, optimization solver, Lean installation, or stochastic search is
needed. Wall-clock times are not asserted to be reproducible.

FIRST-WRITE REDUCTION
Before the first transition that writes 1, a blank tape stays entirely blank.
Starting instead at the state of that first write gives exactly the same
continuation, up to translation. If no 1 is ever written, the finite zero-read
control graph either halts or repeats a state; its behavior is immediately
arithmetizable. Thus the first-writing controls suffice when looking for a
blank start that reaches a represented source frame. Every table in the
physical-permutation run has the same eight first-writing controls.

PAIR EXPERIMENT
The input pool consists of 346 corrected local row proposals from the pinned
incoming packet, plus an unchanged sentinel. Some proposals change arithmetic
box rows and have no independent equivalence proof. This experiment treats
all entries as candidates, never as already proved source equivalences.
Every pair on distinct rows is tested. Each table is run from all its controls
whose zero transition writes 1. The detector accepts a complete canonical
frame at ANY of the 3,673 source sites, with ANY values of all nine registers,
any translation, header distance 48+n for n>=0, and any finite nonempty spare
tail. It checks the entire finite support of the tape. The run limits are
one million literal transitions, head displacement 20,000 and support 20,000.

There were 471,684 simulations and 586,554,596 literal transitions: 117,967
halts, 353,129 certified outward rays, 588 bounded runs, and zero complete
source frames. A bounded run is not a divergence proof. Failure to reach a
frame within the bound is not a general impossibility statement.

PHYSICAL-PERMUTATION EXPERIMENT
All 9! permutations of the nine physical unary-register locations are tried.
The code modifies only read-1/write-0/right dispatcher transitions into the
skip chain. It does not permute the skip-chain engine itself. The intended
logical-to-physical map is perm composed with (6,2,0,4,3,7,8,5,1).
All eight first-writing blank starts are tried. An accepted safe frame would
be at source site 25..44 with T,W,H zero and arbitrary six working registers.
None is reached. All 2,903,040 runs are classified, without fuel exhaustion:
725,760 halt and 2,177,280 enter a certified outward blank ray, after a total
of 86,728,320 literal transitions. A ray certificate uses a cycle of zero-read
transitions all moving in one direction into untouched blank cells; symbols
written behind the head do not affect its infinite continuation.

The identical finite counts arise after adding the stride-two scheduler's
extra reader to runtime193: the failures occur before that reader can repair
the incomplete initialization. The accompanying receipt records this run.

OTHER SEARCH RECEIPTS
receipt.json and final_logs.txt also summarize the other completed bounded
screens and the 900-second grammar anneal. The compact replay command above
reproduces the two bootstrap experiments, not every discovery search.
These scoped negative results give no lower bound for arbitrary PA-consistency
Turing machines and do not invalidate a different future 193-state design.
