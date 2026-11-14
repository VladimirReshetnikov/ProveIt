BOUNDED LOCAL-RELATION SEARCHES ON U208

Outcome and limits
------------------
No additional accepted reduction was found. This directory does not
contain a 207-state candidate. It preserves two completed search scopes
and identifies interrupted exploratory extensions separately.

A failure on an overapproximating finite-history context can be caused by
a tape neighborhood that never occurs in the blank-tape run. Consequently
these results do not establish a lower bound on state complexity. Branch
and microstep budgets can also prevent the symbolic procedure from proving
a valid transformation with a longer or more elaborate certificate.

1. Completed shifted-head quotient search, both U208 classes
-----------------------------------------------------------
Choose a noninitial state q whose incoming transitions all move in the
same direction d. Delete q, choose a retained state r (including initial
state 0), redirect every incoming q target to r, and reverse the direction
of every such incoming transition. This implements the configuration map

    (q,h,tape) -> (r,h-2d,tape),

while other old states retain their head coordinate. Allow one arbitrary
replacement row at r: either read bit, either write bit, either direction,
and any remaining working-state target. The other keeper row is inherited.
The candidate must simulate one parent step by a positive child block of
at most 71 steps at each exceptional old state q and r.

Each of the two distinct U208 machine classes has 177 eligible deleted
states. For each, 207 retained keepers and 2*2*2*207 row actions were
examined. Thus each class has exactly:

    36,639 ordered (deleted,keeper) pairs
    60,674,184 one-row action assignments
    zero finite-screen survivors

The screening inputs are exact depth-12 forward-history bit cylinders,
with initial state 0 re-injected with unrestricted tape at each round.
For each cylinder and each compatible current read bit, the C++ screen
uses two deterministic pseudorandom completions (mt19937 seed 510292).
Every completion is a concrete member of the cylinder. Complete tape
agreement is checked by an exact mismatch count, together with the
projected head and state; no tape hash is used in this search.

The zero-survivor result excludes certificates valid on all of these
concrete screen inputs with the stated 71-step block bound. It cannot
exclude reductions valid only on a stronger reachable-configuration
invariant. No symbolic acceptance stage is necessary when the finite
screen has no survivor.

A separate preliminary direct shifted-head search, without keeper-row
mutation and excluding keeper 0, covered 36,462 pairs on class A at
history depth 12 and bound 71. Four finite survivors failed the symbolic
check. Its receipt is retained, but the broader completed one-row screen
is the principal result above.

2. Completed multiple-step block quotient search, one finite cluster
-------------------------------------------------------------------
Class A was searched for deletion of one of the native states

    163, 211, 217, 215, 157, 184, 67, 148, 186.

For each deleted state, every noninitial distinct keeper was considered.
All targets of the deleted state are redirected to the keeper; the head
projection is unchanged. One arbitrary keeper row may be replaced. Both
the parent execution and the child execution may take positive blocks
before rejoining at the same projected state, head coordinate and complete
tape. This is broader than requiring the child to reproduce a single old
step. The finite-history depth is 9; both block bounds are 31; the symbolic
branch-processing budget is 4,096 per guard.

The completed run examined 1,854 ordered pairs and 3,070,224 row-action
assignments. Twenty candidates passed its initial finite screen. None
passed the full symbolic cylinder checks within the stated budgets. The
retained report therefore states zero accepted candidates; it does not
prove that every transformation in this family is semantically invalid.

3. Interrupted source-conditioned extensions
--------------------------------------------
The partial/ directory contains incomplete logs from an extension using
actual canonical runtime tape windows as discovery guards. Tool-session
transport interruptions left two searches without completion markers:

    208A_source_block_quotient.log
    208A_source_block_full_screen.log

They must not be counted as completed sweeps. The latter retained prefix
contains 1,342 finite hits. A second finite refinement retained 212, and
all 212 failed exact symbolic block-convergence rechecking under the
harvested guards. No source-conditioned candidate was accepted. The
filenames are historical research names; the word "full" in one filename
does not claim that its interrupted sweep completed.

The source-conditioned C++ prototype uses a 64-bit tape-difference hash
only as a discovery filter; it cannot certify a reduction. Exact symbolic
checking is required after that filter, followed by a fresh complete
primitive-runtime and startup proof for any hypothetical survivor. The
prototype source is retained for transparency, but its interrupted broad
search is not one of the default reproducible completed experiments.

Offline reproduction
--------------------
Run from any directory, using the desired absolute script path:

    python3 run.py --output /tmp/local-relations-check

This verifies input/evidence SHA-256 hashes, completed receipt counts,
completion markers and the explicitly partial status of the extension.
It does not rerun a search and records that distinction in its receipt.

To compile and replay both completed shifted-head screens (g++ with C++17):

    python3 run.py --mode headshift --output /tmp/local-relations-headshift

To replay the completed class-A block cluster (Python standard library):

    python3 run.py --mode block --output /tmp/local-relations-block

The block replay can take approximately a minute or more. Its microstep
bound, cluster, deterministic sampling and guard construction are fixed
by the wrapper. Arbitrary exploratory invocations are possible using the
individual scripts, but do not change the scope of the retained results.

The local history_contexts.py implements the same forward-image cylinder
recurrence used in the supplied Entry Context discovery packet. The
retained depth-12 cylinder inputs are hash-bound; their provenance is the
208-state native table in the same input directory. The table hashes are
b348a466... (class A) and 5f936da0... (class B), with full values in the
manifest. Native halt is 254; it is separate from the 208 working states.

No state-complexity lower bound, proof-assistant certificate, or new
machine table is claimed by these negative experiments.
