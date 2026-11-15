# Physical reduction research

This directory records additional searches for a blank-start binary machine with
at most 193 working states. None of the completed searches in this directory
produced such a machine. Its explicit 193-state tables are initialized runtime
cores; they are not proposed blank-start consistency machines. The enclosing
package supplies the new 194-state ForestX construction.

Repository inputs are pinned to ProveIt commit
`7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`. See `NOTICE.txt` and the retained
licenses. The ForestX inputs are the new construction in the enclosing package.

## Quick replay

Run Python 3.10+ without `-O` from this directory:

```sh
python3 -B verify.py
```

The verifier checks input hashes, reconstructs both 193-state runtime folds,
replays the primary and ForestX source contracts, and checks the finite
inductive interval certificate. The symbolic source contracts use the inherited
universal register-block interface. They are not a substitute for blank
initialization, logical calibration, or a complete Lean proof.

## Whole-instruction merge and bypass searches

The three Python synthesis searches preserve complete source-instruction
endpoints, allowing their intermediate control traces to change. This is a
broader endpoint condition than requiring each original transition to reappear
at its original successor control.

* `pair_whole.py` merges each eligible pair of controls and chooses each retained
  row from either old control:57,460 candidates, no hits.
* `merge_one_free.py` considers pairs sharing one row and chooses the other row
  arbitrarily from all binary write/move/remaining-control actions:111,168
  candidates over 144 pairs, no hits.
* `bypass_one.py` deletes a control with a single external incoming row and
  rewrites that incoming row arbitrarily:67,936 candidates, no hits.

Arithmetic-interface controls, the source-frame control, and the start control
are excluded from deletion. Symbolic runs have a 1500-step abstract fuel bound;
this is not a bound on literal arithmetic-block execution. A failure to close is
only a rejection within this proof/search procedure. These searches are not
lower bounds on arbitrary Turing machines.

The `inv_` variants use the independently checked source interval invariant
below. They repeat the same candidate domains and also find no hits. The
`forest_` variants run on the new ForestX machine. There the three counts are
57,460,104,992, and 67,936 respectively, again with no hits. The middle count
corresponds to 136 shared-row pairs.

Example full replays:

```sh
python3 -B pair_whole.py
python3 -B merge_one_free.py
python3 -B bypass_one.py
python3 -B forest_pair_whole.py
python3 -B forest_merge_one_free.py
python3 -B forest_bypass_one.py
```

The adaptive contract order merely moves a failing case to the front. Every
accepted candidate would have to pass every applicable source outcome.

## Inductive source intervals

`abstract_regs.py` computes an interval invariant for the primary 3673-site
register program, starting at site 25 with logical registers `(2,0,...,0)`.
The interval domain keeps lower bounds through 3 and upper bounds through 3;
upper sentinel 4 means infinity. `check_interval_certificate.py` independently
checks initial inclusion and every applicable transfer edge in the saved
certificate. There are 3670 inhabited abstract sites and 4774 checked edges.
Sites 8,3635, and 3636 are unreachable. Decrements at sites 7 and 3634 always
have their zero branch. The latter is the already known AX 11 no-push-MP
optimization; it is not counted as new research in this package.

The invariant is a statement about the abstract source computation. Transferring
it to physical configurations requires the source simulation. The executable
checker does not itself prove that transfer in iPRA or Lean.

## Runtime 193 neutral rewrites and blank initialization

`runtime193.native.tm` is the earlier core obtained from primary 194 by merging
native 301 into 88 and using the marker route through 122. The same transformation
of ForestX is frozen at `forest/runtime193.native.tm`. The changed marker is
valid on initialized register blocks because their delimiter is followed by 1:
`(16,1)` and `(122,1)` both perform `(0,L,1)`. Blank startup does not satisfy
that premise. This is why the runtime fold alone does not solve the problem.

`global_neutral_start.py` considers every single-row rewrite outside the
inherited arithmetic interface, against complete source outcomes. It filters
unaffected outcomes using the controls encountered by the original symbolic
traces: a single-row mutation cannot affect a trace which never reaches that
control. Every affected outcome must close. The primary core enumeration tests
262,141 rewrites and accepts 417 source-interface-preserving rewrites. None
produces an admissible blank-start source frame within the stated bound.

The union pool adds the prior rewrite `(10,1) -> (1,L,6)`, giving 418 entries.
This one is not recognized by the single-state run accelerator, but has a
three-step local proof. Every entry to 10 has a zero immediately to its left.
Starting at 10 on 1, the sequence 10,6,6,10 changes that 1 to 0, moves one cell
right, and restores the surrounding tape, exactly as the original row
`(10,1) -> (0,R,10)`. This explains the single prior neutral rewrite missing
from the 417 directly closed symbolic variants.

The 91 newly admitted rewrites extend the prior 327-entry pool. Combining
individually neutral rewrites can create new intermediate contexts. Therefore
multirow search hits would still require a fresh simultaneous source proof;
none was found in these completed screens.

The exact encounter-directed bootstrap DFS is `search_four.cpp`. Despite its
historical filename it supports up to five edits. It starts at native 74 on a
zero tape, excludes conflicting edits to one row, and deduplicates complete
edit sets. It detects exact repeated finite configurations and outward blank
rays. A finite cutoff remains unresolved. The acceptance condition is the
entire canonical source frame at any source site 25--44, with arbitrary nine
work-register values, a nonempty spare list, arbitrary translation, and padding
at least 48. Even a hit would still need admissible initial data and calibration.

With the 418-entry pool, the start 74 search through five edits processed
4,139,311 computations and 11,648,269,548 literal transitions. It found no
frames:67,442 cutoffs,2,329,743 outward rays,1,742,126 exact cycles, and no
halts. `search_all_starts.cpp` additionally ranges over all 193 existing start
controls. Through three edits it processed 624,753 computations and
3,358,299,396 transitions, with no frames:19,590 cutoffs,360,334 rays,
244,824 cycles, and five halts.

Reproduce from this directory:

```sh
g++ -std=c++17 -O3 search_four.cpp -o /tmp/pa193-startup
/tmp/pa193-startup runtime193.native.tm union_neutral.tsv startup_any_frame_templates.tsv 5 200000
g++ -std=c++17 -O3 search_all_starts.cpp -o /tmp/pa193-starts
/tmp/pa193-starts runtime193.native.tm union_neutral.tsv startup_any_frame_templates.tsv 3 200000 all
```

ForestX has its own freshly generated pool: 406 symbolically closed rewrites
plus the three-step detour, for 407 entries. Its start-74 search through five
edits processes 1,016,400 computations and 6,774,611,660 literal transitions,
with no frames (39,831 cutoffs, 416,121 rays, 560,448 cycles, no halts). Its
all-193-starts search through three edits processes 450,515 computations and
4,182,522,818 transitions, again with no frames (24,180 cutoffs, 240,706 rays,
185,624 cycles, five halts). The exact files are under `forest/`; its source
frame templates are regenerated from its own site addresses.

The machine-readable totals for all completed searches are in
`search_summary.json`. `quick_replay.json` records the successful bundled
verification, including all four source implementations.

## Fresh finite-window quotient screens on ForestX

The attributed collector includes every interior position of an accelerated
self-loop, not merely its endpoints. It freshly checks 4778 symbolic outcomes
and observes 6242 accelerated scans. It obtains 8392 source windows at radius 4
and 29554 at radius 6. Arithmetic windows remain the conservative blank-start
abstract propagation used by the inherited synthesizer.

The joint-return merger tests all 18,721 control pairs. For radius 4 it performs
23,474,976 row-action trials and 137,094 joint row pairs. For radius 6 these
counts are 25,436,628 and 173,925. Both searches find no quotient. Each candidate
must recover the original one-transition endpoint within 100 steps, without
leaving its finite window. This domain includes multi-step lookback detours,
but not arbitrary compiler changes.

```sh
python3 -B src/collect_source_contexts.py forest/machine.native.tm forest/sites.json forest/instructions.json forest/contexts4.txt 4
g++ -std=c++17 -O3 src/joint_return_merge.cpp -o /tmp/pa194-quotient
/tmp/pa194-quotient forest/machine.native.tm 4 100 forest/contexts4.txt
```

Use 6 in both radius positions to replay the radius 6 screen.

## General two-row instruction-endpoint discovery

The C++ `full_endpoint_merge*` programs implement a deliberately finite discovery
screen: fixed padding 48 (gap parameter zero), exact bit prefixes, and the
arbitrary-register box interface. Both rows of a retained control are
synthesized. Partial unknown rows are deferred; every final hit would have to
pass all source outcomes and then undergo the independent universal symbolic
and physical checks. No hit was obtained.

The complementary-ingress reader screen covers 340 pairs,524,960 partial
row-actions, and 11,948,396 joint row pairs. Its control/head/tape/state cycle
check is exact. The broader reader-only screen uses all 60 surviving AX reader
controls: 1770 pairs, 2,732,880 partial row-actions, and 45,184,860 joint row
pairs, with no hits. The earlier physical
pilot tested only the first 200 eligible pairs, although its final index counter
continues over the full list; do not interpret that index as the number tested.
Runs are bounded at 2048 transitions, stay left of the abstract register-file
boundary, and have a finite left window. Negative results in this discovery
screen establish no universal impossibility claim.

```sh
g++ -std=c++17 -O3 full_endpoint_merge_sample.cpp -o /tmp/pa194-full-merge
/tmp/pa194-full-merge primary.native.tm contracts.tsv eligible_readers.txt
```

All source data, search inputs, completed receipts, licenses, and hashes are
included. The enclosing report gives the new construction and the exact status
of the iPRA consistency equivalence.
