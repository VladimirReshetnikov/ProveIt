FINITE LOCAL CONTRACTION SEARCHES FOR PA194 TABLES
Snapshot: ProveIt 1e1a41f799d4658b829cdd0eabae3775a0c8c4a0
Research session: 14 November 2026, Pacific date

RESULT
No contraction was found in any of the explicitly described finite search
families below. This is NOT a lower bound of 194 states, NOT a refutation of
other 193-state constructions, and NOT a proof of the Con(PA) calibration.

The principal inputs are the primary PA194 table and seven named incoming
candidate tables at the pinned commit. Their exact dense representations,
SHA-256 digests, initial state 0, terminal label 194, and provenance paths are
in input_manifest.json. No graph census or duplicate historical copy is used
to inflate the number of candidate designs considered here.

Three further inputs are clearly separated: PA194AX11QGH is the fresh source
construction from this research session, PA194AX11HR is a new physical-register
allocation [6,1,5,7,4,8,2,0,3], and PA194_appendzero is an exploratory one-row
edit of the primary table. The latter changes dense row
(0,0), i.e. native (74,0), from writing 1 to writing 0. No claim that this
exploratory table is calibrated to PA is made.

Every input has exactly 194 working states and 388 transition rows. The
Python replay checks completeness, domains, transition closure and exact
file digests before invoking the search code.

1. DIRECT CONTRACTIONS

For every ordered pair (a,b) of different working controls, remove a and
redirect all targets a to b. The start is redirected if necessary. Do not
change either outgoing row of b. There are 194*193 = 37,442 such pairs per
input table.

At a local entry into a, permit matching any of the first 64 original
machine steps by at most 128 candidate steps, with exact tape, head and
projected-control agreement. The tape window has radius 5, hence 11 cells.
No step may READ outside the window. An endpoint may have its head just
outside it if the last write was inside. These limits specify a finite
proof template, not a simulation time limit for the full machine.

All eleven specifically named inputs return zero survivors. The eight pinned
inputs account for 299,536 ordered pairs; the two new constructions and exploratory
edit are reported separately.

2. MERGERS WITH BOTH KEPT ROWS ARBITRARILY REWRITTEN

For every unordered pair {a,b}, retain b and remove a. Both outgoing rows of
b may be replaced by arbitrary binary writes, L/R moves, and a destination
among the 193 retained controls or the terminal label. Destinations a and b
are equivalent after redirection, so only b is enumerated. There are 18,721
state pairs and 776 choices for each kept row.

Both possible original entry states, a and b, are checked. Any of the first
8 original steps may be matched by at most 64 candidate steps, using the
same radius-5 whole-window equality condition. A partial assignment is
rejected only if it already fails without consulting its unassigned other
row. Encountering that unassigned row is treated as unknown and retains the
choice. All surviving pairs of row assignments are then checked with both
rows fixed. Thus the partial-program pruning does not omit a completion
that could satisfy this finite template.

Every one of the eleven named inputs has zero survivors. The exact row-trial,
full-assignment, and local-case totals differ by input and are recorded in
contraction_results.json and summary_table.txt. In particular, for the new
PA194AX11QGH table:

  18,721 unordered control pairs
  24,426,152 single-row assignments screened
  122,567 complete pairs of kept-row assignments screened
  90,501,864 local simulations
  zero survivors

The additional PA194AX11HR physical allocation also has no survivor:
24,241,464 single-row assignments, 120,856 complete pairs, and 86,710,550
local simulations over 80,255 abstract windows. Its distinct input digest
and both completed receipts are included in the same manifests.

3. NEUTRAL PRECONDITIONING, THEN DIRECT CONTRACTION

A further search alters one outgoing row of primary PA194, leaving all
other rows fixed. There are 388*(4*195-1) = 302,252 nonidentical row edits.
Using a radius-5 invariant, 1..8 original steps, and 1..64 altered steps,
422 edits satisfy the local relative-halting certificate. The original row
itself is excluded. Every accepted edit has a nonempty original context
set; no unused-row vacuity is needed for this list.

Each of these 422 altered tables is then tested for all 37,442 direct
contractions with the bounds of section 1, a further 15,800,524 ordered
pair checks. None succeeds. neutral_rows.jsonl contains the exact 422
preconditions, and neutral_merge_results.json records their negative
contraction screens. These preconditioned tables are search intermediates,
not proposed material new consistency designs.

4. WHY THE LOCAL CERTIFICATE IS SOUND

Let I_K be the least set of (control, window-bitstring) pairs containing the
blank initial window. To advance a pair, perform its literal write/move,
shift the window, and permit either value for the newly entering cell. Halt
has no outgoing edge. Induction on the number of original machine steps
shows that I_K includes the radius-K window of every actual original
blank-start configuration. It may also contain unreachable windows.

For a contraction, let pi identify a with b and fix every other state.
For each I_K window entering a changed original state, the checker requires
positive integers r and s within the stated bounds such that

  candidate^s(pi(control), head, tape)
      = (pi(original^r.control), original^r.head, original^r.tape).

The equality includes every window bit; both traces write only within that
window, so the entire infinite tape agrees too. Intermediate halt ends the
trace, so a matching nonhalting endpoint cannot hide a candidate halt. All
unchanged states match in one step. For the neutral-row search pi is the
identity and only the changed row needs a local obligation.

Repeated application gives a sequence of matching configurations whose
original times and candidate times each increase by at least one. If the
original machine halts after a finite number of steps, the positive original
increments reach its terminal configuration, which matches candidate halt.
If the original execution is infinite, positive candidate increments yield
an infinite candidate execution. This proves blank-start halting equivalence
for an ACCEPTED local certificate. The argument uses finite table checks,
primitive-recursive traces and induction; it is suitable for iPRA
internalization. No proof-assistant formalization of these C++ programs is
claimed here.

The two-row search treats both changed incoming states, so altering the
kept row is not silently assumed harmless. Reference goals may require
more than one original step; this is why the search is broader than tests
that demand exact simulation of a single original transition.

Negative results are limited to this certificate family. A valid merge
might fail because I_K is an overapproximation, because reconvergence needs
more time/space, because the tape representation must change, because other
rows must be changed simultaneously, or because a source-level change is
required. No inference of an absolute machine-state lower bound is valid.

5. REPRODUCTION

Requires Python 3 and a C++17 compiler called g++. From this directory:

  python3 replay.py

This rebuilds both search programs and checks the eleven input tables. It
writes replayed_results.json. To include the neutral-preconditioning search:

  python3 replay.py --neutral

For the faster direct screen plus neutral-preconditioning replay:

  python3 replay.py --direct-only --neutral

To target only the fresh new construction:

  python3 replay.py --only PA194AX11QGH

The complete two-row replay can take a few minutes. Results contain observed
counts rather than timeouts or extrapolations. Timing fields vary by host.

The direct and two-row programs can also be invoked separately, with
arguments TABLE RADIUS ORIGINAL_BOUND CANDIDATE_BOUND. They expect contiguous
dense working labels, start 0 and terminal label equal to the state count.
The supplied Python wrapper validates the production input tables first.

positive_control.tm is a synthetic four-state diagnostic, unrelated to PA
consistency. Its states 1 and 2 have identical rows and both occur in the
blank run. Both search implementations recover their merger at bounds 1/1;
positive_control_receipt.json records this nonvacuous positive control.
The diagnostic is not a proposed consistency machine.

6. FILES AND PROVENANCE

- inputs/: eleven exact dense input tables.
- input_manifest.json: input identities, groups, state counts and provenance.
- multistep_fold.cpp: direct-contraction enumerator.
- tworow_fold.cpp: arbitrary two-row merger enumerator.
- neutral_row.cpp: single neutral-row edit enumerator.
- replay.py: input validation, compilation and replay orchestration.
- contraction_results.json: twenty-two completed search receipts, two per input.
- neutral_rows.jsonl / neutral_row_search.log: exact precondition catalog.
- neutral_merge_results.json: 422 completed direct-contraction receipts.
- replayed_results.json / replay_direct_neutral.log: completed independent
  rerun of the final direct-search code on all eleven inputs and all 422
  preconditions, including reconstruction of the neutral catalog. The
  supplementary AX11HR rerun is in ax11hr_direct_replay.json/.log.
- positive_control* files: synthetic diagnostic and its observed results.

The numerical tables are inherited from the cited ProveIt packets, with
James Chang / earlier K-family runtime ancestry. Their original license
notices should accompany any distribution of this subdirectory within the
complete research archive. The new search implementations and the relative
simulation argument above were written in this research session.
