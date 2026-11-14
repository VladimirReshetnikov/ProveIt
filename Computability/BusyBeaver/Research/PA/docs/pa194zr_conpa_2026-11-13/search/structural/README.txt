Structural reduction screens for the final PA194ZR
=================================================

These are completed finite negative searches, followed by one concrete rejected
alternative. They found no certified 193-state reduction. They do not establish
a lower bound on the number of states needed for Con(PA), or even a lower bound
within other transformations of this particular machine.

The machine input is ../../machine/pa194zr.native.tm, with SHA-256
745dd4343d88f6d3458cbde6146cfe360283bc7e8a9113d020eed999b81ad85d.
All paths below are relative to the complete research package. No network or
external repository is needed. The symbolic scripts use Python 3 and its standard
library, plus the already bundled reference_cs/ compiler and runtime. The context
screens require a C++17 compiler. No executables or large context dumps are stored.

Recorded results
----------------

  Screen                                     Trials       Passing candidates
  302 mergers                                676          0
  Alternative (113,0) actions, deleting 302    776          0
  Radius-6 arbitrary pair folds               28,755,456   0
  Radius-8 folds involving 302                297,984      0

The last two trial counts count individual proposed row actions during the
screen, not distinct complete Turing machines. The first two counts also refer
to specified transformations; they should not be added to unrelated decoder
search iteration counts and described as distinct machines.

search_receipt.json binds the table and source inputs and records exact figures.
The compact original terminal logs are under logs/. The Python files are
portable versions of the executed scripts: path setup and result formatting
were cleaned up, while the enumerated families and checking algorithms are
unchanged. The portable source-contract list was compared exactly with the
original list of 4,754 contracts. Counts were independently recomputed from
the final table and checked against the logs. This packaging step did not add
any new search family.

1. Whole-source primitive-contract merger screen
------------------------------------------------

Delete native state 302 and redirect every target of 302 to a kept control.
There are 169 choices for the kept control: the deleted state, the inherited
register-box controls, and source-frame control 84 are excluded. For each read
symbol independently, choose the merged row from either old control, projecting
its target through the alias. This gives 169 * 4 = 676 trials.

The reference executor is first run on all 4,754 unchanged PA194ZR contracts,
recording which controls each contract visits. Each trial checks every contract
that can encounter an affected original control. Unaffected original paths are
unchanged, so this avoids unnecessary repeated checks without omitting a case.
The executor's symbolic fuel is 1,024. No trial passed all relevant contracts.

Replay from the package root:

  python3 -B search/structural/primitive_screens.py mergers

The symbolic runtime uses the inherited register-box lemmas. A hypothetical
passing candidate that changed an engine row would still need a fresh engine
proof and a full blank-startup check before acceptance. No passing candidate
is asserted here.

2. Delete 302 and replace its remaining external incoming row
-------------------------------------------------------------

After the two PA194ZR edits, the only external transition targeting 302 is
(113,0). The other target is its own (302,1) self-loop. Delete both rows of 302
and replace (113,0) by every action with either write bit, either direction,
and any remaining control or the halt control. There are

  2 * 2 * (193 working targets + 1 halt target) = 776 actions.

Each trial is checked against the complete ordered list of 4,754 source
contracts, stopping at its first failed contract. The best trial, (0,L,40),
passed only the first five contracts. No trial passed the list.

Replay:

  python3 -B search/structural/primitive_screens.py redirects

A failure to obtain a symbolic certificate is not, by itself, a concrete
counterexample to that candidate's blank execution. It is a negative result
for this bounded certification method.

3. General local-context pair-fold synthesis
--------------------------------------------

context_fold_scan.cpp constructs an inductive overapproximation of blank-tape
reachability using the control and a window of 2*r+1 tape bits centered on the
head. A move shifts the window; the newly exposed outer bit is allowed to be
0 or 1. The initial abstract configuration is native state 74 with an all-zero
window. This conservative closure contains every actual reachable local window.

For radius 6, the window has 13 cells and the closure contains 272,471
control/window pairs, including terminal configurations. Every unordered pair
of working controls other than start control 74 is considered: choose(193,2)
= 18,528 pairs. One control is aliased to the other. Each merged row may write
either bit, move in either direction, and target any remaining working control
or halt. The preliminary enumeration has

  18,528 * 2 read symbols * 2 writes * 2 directions * 194 targets
  = 28,755,456 trial row actions.

A local trial must simulate the projected original single transition from
every abstract context of both original controls, reproducing its complete
window and head position. It may take up to 64 literal transitions and must
not read outside the recorded window. During the preliminary screen, a visit
to the as-yet-unassigned other merged row is retained as a possibility. Pairs
of retained row actions are then checked together. The program has a guard
against excessively large row-pair combinations; the actual run recorded
skipped=0, so that guard excluded no pair in this run.

No quotient passed. This says nothing about larger windows, longer witnesses,
different simulation boundaries, nonlocal tape invariants, new controls, or
other source programs. A candidate may also fail because the abstraction
contains a local context unreachable in the actual blank run.

Replay, putting temporary binaries outside the package:

  g++ -O3 -std=c++17 search/structural/context_fold_scan.cpp -o /tmp/pa194zr_context_fold
  /tmp/pa194zr_context_fold machine/pa194zr.native.tm 6

The summary is written to stderr; any accepted candidates would be on stdout.
The recorded stdout was empty.

4. Larger context screen restricted to state 302
------------------------------------------------

context_fold_302.cpp runs the same algorithm at radius 8 (a 17-cell window),
considering only pairs containing state 302. The closure has 3,129,859
control/window pairs. There are 192 control pairs and therefore

  192 * 2 * 2 * 2 * 194 = 297,984 trial row actions.

No quotient passed, and no pair was skipped by the row-pair combination guard.
The same 64-transition horizon and proof limitations apply.

Replay:

  g++ -O3 -std=c++17 search/structural/context_fold_302.cpp -o /tmp/pa194zr_context_302
  /tmp/pa194zr_context_302 machine/pa194zr.native.tm 8

5. Concrete rejected alternative: DEC6 returns
-----------------------------------------------

rejected_dec6.native.tm changes the two final PA194ZR rows (103,1) and
(2066,1) from (1,R,17), the DEC3 entry, to (1,R,21), the DEC6 entry. This
alternative has 194 states. Its attractive local source behavior does not
preserve the nonstandard blank initialization.

Starting at native state 74, head 0, on the entirely zero tape, it first enters
halt control 254 at literal transition 1,361. check_rejected_boot.py reproduces
this finite counterexample. Its receipt records the exact final head, every
one-cell on the complete tape, and a hash of the full transition trace.

Replay:

  python3 -B search/structural/check_rejected_boot.py

The checked result is rejected_dec6.receipt.json. This is a concrete startup
failure, stronger than the negative certification results of the search screens.
It does not apply to the accepted DEC3-based PA194ZR, whose complete 59,816-step
startup is checked separately in the main construction.
