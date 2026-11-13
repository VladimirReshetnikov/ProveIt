# A changed helper row in a PA196 state fold

This screen extends the [keeper-row screen](../README.md): after identifying
one pair of PA196 states, it permits changing **one row at any retained
state**, including a third helper. It finds no fold satisfying its five-cell,
16-child-step, one-parent-step simulation template under the radius-six
blank-start window overapproximation. A noteworthy near miss is described
below. This is not a lower bound for arbitrary 195-state machines.

From the repository root, with Python 3.10+ and a C++17 `g++`:

```sh
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/helper-row/replay.py --output /tmp/pa196-helper.json
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/helper-row/adverse.py --output /tmp/pa196-helper-adverse.json
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/helper-row/blank_prefix.py --steps 100000000 --output /tmp/pa196-helper-prefix.json
```

The outputs match [receipt.json](receipt.json),
[adverse-receipt.json](adverse-receipt.json), and
[blank-prefix-receipt.json](blank-prefix-receipt.json), respectively. All
three commands pin the literal PA196 input by SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
They compile their C++ helpers in temporary directories and leave this
research tree unchanged. The last command checks a **finite** run prefix; it
must not be treated as a nonhalting or consistency proof.

## Exhaustive screen within the template

There are 38,220 ordered choices of deleted and retained states. For each,
every one of the 390 rows at the 195 retained working states is eligible for
replacement by any bit, direction, and retained-or-halt destination, with
784 possible triples. The 11,686,147,200 raw `(pair, row, replacement)`
choices include deleting the initial state, whose image becomes the new start.
All unpatched rows are preserved except that targets of the deleted state
are redirected to the keeper.

The table and context model are those of the existing [one-row
screen](../README.md): the 270,067 radius-six abstract windows project to
2,774 five-cell state/windows. For the deleted and retained parent states,
the child must match each parent step by a positive block of at most 16 steps,
reading only within the five-cell window and preserving the entire tape at
block end. A patched third state is checked as a parent state too; all other
parent states commute in one step.

For each pair, execute the *unpatched* child on every merged-state context.
For any failing context, a patch capable of changing that outcome must touch
one of the `(state, read)` rows visited **before** this failed block terminates
or leaves the window. Intersecting these visited-row sets across all failing
contexts is a necessary condition for one-row repair. This discards no repair
within the stated template. There are no unpatched folds; the intersection
leaves 2,121 possible row locations, 796 at a state other than the keeper.
The engine tests all 1,662,864 replacement triples at those locations; five
pass one representative window for each affected parent state/read, and none
passes every context. Independent Python block execution checks a rejecting
window for each of the five.

The positive controls exercise both cases: the C++ screen recovers the known
U209-to-U208 fold, whose modified row is at the keeper, and a separate small
synthetic four-state table has a valid fold requiring a modified row at a
third helper state. The Python block checker independently validates both
survivors on all their supplied windows.

## A near miss and its boundary

One representative-pass candidate deletes state 45, retains 160, redirects
all targets of 45 to 160, and changes helper row `184/1` from `1 R 78` to
`1 L 75`. The edited table has 195 working states plus halt. It matches all
admitted five-cell contexts at parent states 45 and 160, and all admitted
state-184/read-zero contexts. It fails the bounded check on ten
state-184/read-one contexts, including five-bit mask 6.

The adverse context is not removed by increasing the blank-start window
closure. Radius seven has 910,501 windows and radius eight has 3,131,937;
both project to the same 2,774 five-cell state/windows as radius six and admit
state 184/mask 6. The radius-eight closure contains the exact 17-bit window
mask 410. Extend that window by zeros: its one-cells relative to the head
are `{-7,-5,-4,-1,0}`. On that full tape, the original `184/1` step ends in
state 78 at head offset +1. The candidate reaches state 35 at offset +2 in
10 steps with only zeros at and to the right of its head; the checked row
`35/0 = 1 R 35` then runs right forever. The recorded ten-step trace and a
simple induction therefore show that this full tape cannot match the parent
endpoint. The window is *abstractly admitted*, but neither that window nor
its zero extension is known to occur on the actual blank run. It is a
counterexample to the local proof over this overapproximation, not an actual
blank-input divergence.

In the first 100,000,000 original blank-run steps, the finite full-tape block
checker confirms projected matching at every parent boundary; state 45 occurs
4,021 times, state 160 and state 184 do not occur, and each affected visit
uses five child steps. The corresponding child prefix has 100,016,084 steps.
This does not prove that state 184 or its adverse window is unreachable later,
that the infinite runs agree, or that the machine has the required PA
consistency equivalence. A sharper source-site/decoder invariant or a different
simulation may still decide this candidate.

The screen allows only one changed row total, not two changed helper rows,
multistep parent matching, a different tape/head representation, or state
reallocation. Escaping a five-cell window is treated as failure of this
particular certificate template, not as a general machine counterexample.
