# Targeted marker and continuation experiments

These are additional experiments after the original source packet was frozen. They do not establish a 214-state candidate.

## Input

The exact experimental 215-state input table is `q13_normal215.native.tm`. It uses the CB1 enumeration scheduler described elsewhere in the report. State 13 has been partially evaluated to

```text
13 0 0 R 49
13 1 0 R 60
```

Its old three-step behavior is identical when the preceding tape bit is zero. The finite backward-history checker can prove this predecessor marker without sampling: enumerate every length-d incoming transition path, impose all read/write constraints, and intersect its possible final cells. This proves an invariant for all executions with at least d predecessor steps. Earlier initial prefixes must be checked separately when using the fact as a whole-machine theorem.

## Exact marker facts

Run `python3 summarize_markers.py` to reconstruct the receipt from the table itself. At history depth 8:

- State 13, either read bit: the predecessor bits at offsets -2,-1 are 1,0.
- State 161, either read bit: offsets -3,-2,-1 are 1,1,0.
- State 91, read bit 1: offsets -2,-1 are 1,0.
- State 73, read bit 1: offset -1 is 1.
- State 123: neither read bit has a universal adjacent predecessor marker.

States 91 and 73 share their zero branch, `0 R 82`, and differ only in their one branches, `1 R 81` and `1 R 83`. Their read-one entry markers are disjoint, giving a useful precise selector target.

The local continuation search tried all 856 possible replacements for the merged one row, using existing state destinations, both write bits, and both directions. It simulated the modified table, including the proposed fold, so self-reference was not silently ignored. No replacement reached an old continuation configuration within the 100-step bound on all 44 raw marker contexts tested. A companion search for the shared zero action retained only the existing `0 R 82`. These are finite filters, not universal nonexistence results. The machine team's broader full-primitive search is reported separately.

## Why the proposed state123 route fails as stated

State 123 has two entry types. Entry from `63/0` leaves a zero to its right; entry from `104/0` leaves a zero to its left. The latter also forces the second predecessor bit to zero. Thus a single uniform predecessor discriminator does not cover all state123 entries.

Replacing its zero branch by `0 R 49` failed the concrete primitive gate at basic case 13, the zero branch of source site 10, CD8. This is a failed bounded validation result.

There is also a structural self-reference issue. State123/1 is the only literal `1 R 73` row in the table. The proposed selector path through 81,111,104,123/1 ceases to implement that action when 123/1 itself is replaced by the selector; the path loops back into the replacement. A provider must always be evaluated in the modified table.

## Deliberately rewritten incoming marker

A distinct experiment changes the two incoming state13 rows, (38,0) and (42,0), to `1 R 82`, removes state13, and asks state82 to distinguish the new left marker 1 from its original left marker 0. A successful shared zero branch must restore the deliberately changed marker as well as perform the original `0 R 49` action.

We collected 3,794 distinct whole-tape state13/state82 entry configurations from all 6,177 basic concrete primitive cases. The corpus is `contexts13_82.tsv`. With the one branch of state82 held at its original `0 R 33`, all 856 zero-row replacements fail the continuation filter, even with a 1,000-step old/new prefix bound. That conditional result does not exclude mutually dependent replacements of both rows. The machine team's separate two-row search then enumerated all 856 squared = 732,736 pairs of replacement actions. Every table failed the sample gate, which uses at most 32 affected primitive frames and bounded execution. The unchanged 215-state input passed all 6,177 concrete primitive cases as a positive control. The receipt is `tagged13_82.log`; source and frame corpus are included. These results rule out acceptance by this finite filter, not every possible long-running realization or every globally invariant encoding.

Scripts and the exact input table are included. The input-path references in receipts are provenance labels; the portable scripts use local paths.


## Replay the two-row finite search

From this directory, build and run:

```sh
c++ -O3 -std=c++17 tagged13_82.cpp -o /tmp/tagged13_82
/tmp/tagged13_82 q13_normal215.native.tm q13_cb.cases.tsv
```

The expected final line is `PAIRS 732736 SAMPLE_PASS 0 FULL_PASS 0`. The program first checks the positive-control table on the entire supplied frame corpus; it aborts if this baseline check fails. It then tests every replacement pair on the selected sample and tests all affected frames only for sample survivors. There were no sample survivors.
