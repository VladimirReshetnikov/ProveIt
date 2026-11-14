# Two context folds sharing one new helper

**Result: no candidate survived this explicitly bounded family.** The search
examined 13,660,768 patches of the pinned 196-state PA196 table. A successful
patch would have removed two old states and added one helper, leaving 195
working states. No successful patch or state-count improvement is claimed.

One broader follow-up also finished: permitting independent write bits and
move directions for both helper rows gives sixteen action patterns and
218,572,288 combined patches. It likewise found no survivor. The other
conditions, including the two-cell footprint and 64-step block cap, remain
the same. `search_general.cpp` and `general_receipt.json` preserve this
separate search; the original receipt remains unchanged.

## Exact input and reproduction

The unmodified table is `inputs/pa196.tm`, from
`jamesyc/BusyBeaver@407cdc356f6b586635e71ac92be394255f4bfea4`.
Its SHA-256 is
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
Working states are 0 through 195, the start is 0, and 196 is the halt label.
Upstream's license is retained as `inputs/LICENSE`.

Run the pinned-input wrapper with Python 3 and a C++20 compiler:

```sh
python3 replay.py --output fresh_receipt.json
```

For the broader helper-row family, run:

```sh
python3 replay.py --general --output fresh_general_receipt.json
```

Or compile and run the search directly from this directory:

```sh
c++ -std=c++20 -O3 search.cpp -o shared_helper_search
./shared_helper_search inputs/pa196.tm fresh_receipt.json
```

The source uses explicit input checks; it has no `assert` statements and
does not depend on `NDEBUG`. The wrapper checks the complete table hash,
compiles into a temporary directory, and verifies the exact search counts
and empty survivor list. Runtime seconds may vary between executions.

## Enumerated family

A noninitial state receives a predecessor tag if every incoming transition
moves right and writes the same bit. This fact forces the immediately-left
tape cell on every entry to that state in every computation from state 0,
on any initial tape.

The reference table has 14 opposite-tag pairs `(q0,q1,b)` whose read `1-b`
actions agree and whose read `b` actions differ. The search selects two
disjoint pairs; there are 88 such choices. It independently chooses which
state of each pair to retain, giving four orientations per pair choice.
The two differing read symbols may be different.

For each pair, the retained state's changed row writes the read bit and
moves left to the new helper. Every target of a deleted state is redirected
to its representative. The shared helper's rows preserve the bit read and
move right to independently selected targets. Each target ranges over all
196 original working states and the helper itself: 197 choices each. The
search therefore examines exactly

`88 * 4 * 197 * 197 = 13,660,768`

combined patches. It checks the combined patch directly; it does not require
either individual fold to work in isolation. This permits internal visits
to the second changed pair or to the helper itself.

Each affected old state/read case begins with only two specified cells:
the forced predecessor bit and the currently read bit. A candidate must
reach the exact old-step head, state-quotient, and entire two-cell tape
endpoint after a positive number of at most 64 transitions. Reading an
unspecified exterior cell or halting inside the block rejects the case.
The other rows commute with the quotient by construction. These checks
would establish a positive bounded-stuttering halting equivalence for a
survivor, independent of a finite sample of register values.

## Limits

This is not an exhaustive search of all 195-state machines. It restricts
entry predicates to one-step predecessor tags, retains an identical second
row per pair, uses a two-cell footprint, and fixes both helper moves to the
right with bit-preserving writes. More general helpers, larger history
predicates, additional changed rows, longer sufficient blocks, different
source programs, or different encodings are outside its scope. The negative
result is not a lower bound on state complexity or a claim about arbitrary
blank-tape equivalences.

The broader follow-up removes only the restrictions on the helper's two
write bits and move directions; all the other limitations just listed still
apply. It enumerates `88 * 4 * 197 * 197 * 16 = 218,572,288` patches and
does not use its negative result as a global lower bound.
