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
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/helper-row/source_witness.py --output /tmp/pa196-helper-source.json
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/helper-row/source_actual_witness.py --output /tmp/pa196-helper-source-actual.json
python3 -B Computability/BusyBeaver/Research/PA/pa196-vs-u208/search/helper-row/accelerated_blank.py --output /tmp/pa196-helper-accelerated.json
```

The outputs match [receipt.json](receipt.json),
[adverse-receipt.json](adverse-receipt.json),
[blank-prefix-receipt.json](blank-prefix-receipt.json),
[source-witness-receipt.json](source-witness-receipt.json), and
[source-actual-witness-receipt.json](source-actual-witness-receipt.json), and
[accelerated-blank-receipt.json](accelerated-blank-receipt.json),
respectively. All six commands pin the literal PA196 input by SHA-256
`e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`.
The first three and the sixth compile C++ helpers in temporary directories,
and all leave this research tree unchanged. The third command checks a **finite** run prefix;
it must not be treated as a nonhalting or consistency proof.

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
consistency equivalence.

### An invariant-admitted source-frame witness

[source_witness.py](source_witness.py) checks an exact, well-formed source
frame at site 604. Its path is `1010100110010010100101100011000`, the head
is at position 0 in state 75, the left marker is at -1, and the right marker
is at 48; all positions between the end of the path and the right marker are
zero. The unary physical file is `[1,0,1,0,0,0,1,0,0]` followed by 26 ones,
encoded as `0 1^(v+1)` for each entry `v`. Cells outside the finite frame are
zero. The site's logical-register positivity mask is 7. The separate
[joint-mask invariant](../../source-search/JOINT-MASK.md) admits this
site/mask pair, although that abstract admission does **not** establish that
this exact frame occurs in the actual blank run.

From this frame, both machines reach state 184 reading 1 with five-cell mask
6 at step 31. In 414 steps, the original reaches the exact frame for site
605 with right marker 49 and file `[0,0,1,0,0,0,1,0,0]` followed by 26
ones. This is the expected positive branch of site 604's decrement of logical
register 2. In 664 steps the candidate instead reaches an exact frame for
site 615, with right marker 48 and file `[1,0,1,0,0,0,1,0,1]` followed by
27 ones. The candidate does not reach the original's exact endpoint during
those 664 steps. A return to state 75 at head position 0 alone is not a
source-frame endpoint: intermediate tapes can still have a dirty path.

The script reconstructs the joint-mask fixed point, checks its closure and
the mask's membership, and compares entire finite-support tapes, head, and
state for both endpoints. The deterministic
[source-witness receipt](source-witness-receipt.json) gives both complete
endpoint tapes, affected-state visits, source paths, and hashes of the full
traces. This is a counterexample to a general source-cycle preservation
argument for the candidate; it is not an actual blank-run counterexample and
does not rule out a later rejoining or a different proof of equivalence.

### A source-reached frame

[source_actual_witness.py](source_actual_witness.py) independently resolves
the source graph in two ways and executes it exactly from site 25 with logical
registers `[2,0,0,0,0,0,0,0,0]`. At source step 32,037 it reaches site 604
with registers `[4,1,75,0,0,0,0,0,0]`. This is an exact source execution,
not an abstract reachability claim. During that prefix there are 10,544
increments and 10,466 positive decrements.

The corresponding original-machine frame has marker at position 10,514 and
physical file `[75,0,1,0,0,0,4,0,0]` followed by 10,570 ones. From this
frame the original reaches the site-605 frame in 84,142 steps, while the
candidate reaches a different site-615 frame in 147,964 steps without
visiting that exact original endpoint in the checked prefix. The script
compares the entire tapes, state, and head, and records transition-trace
hashes in [source-actual-witness-receipt.json](source-actual-witness-receipt.json).

The frame accounting follows the imported
[startup and clean-frame connection](../../../jamesyc-upstream/pa196/PA196/PhysicalEndpoint.lean),
[coverage checks](../../../jamesyc-upstream/pa196/PA196/CheckCoverage.lean), and
[checked progress lemma](../../../jamesyc-upstream/pa196/PA196/PrimitiveSimulation.lean):
increment leaves the gap unchanged and appends a spare 1; positive decrement
increases the gap by one; zero decrement and jump leave the gap and file
unchanged. The startup file has 26 trailing ones. Together with the imported
coverage proofs, the exact source trace supplies a route to the original
physical frame; this composition has not itself been formalized here or
replayed as one literal blank-input trace in that script.

### Accelerated blank-start comparison

[accelerated_blank.py](accelerated_blank.py) independently follows the
literal blank-start runs to the source-reached adverse entry. It matches each
parent step at states 45, 160, and 184 against a positive candidate block,
checking the complete tape and head at the endpoint. At every other state,
the projected transitions commute in one step. A deterministic self-loop
sweep accelerates each maximal consecutive run of the symbol read by that
loop: every cell in the run receives the loop's write bit, the head moves by
the run length, and the state remains unchanged. The sweep stops before the
first opposite bit or the execution bound. It does not extrapolate past the
observed finite run.

The first failure of the *512-step block check* is at parent step
1,223,335,721 and candidate step 1,223,363,605: both configurations have
state 184, head position 25, read bit 1, and five-cell mask 6. At the next
individual step the original moves right into state 78, while the candidate
moves left into state 75. The complete tape at that boundary has 21,244
one-cells and equals the source site-604 frame above after 31 steps, with the
frame's root head at absolute position -2. A Python splice checks the complete
subsequent tapes: the original reaches site 605 at blank-run step
1,223,419,832, and the candidate reaches site 615 at blank-run step
1,223,511,538. These are separate step counts for the two machines.

The replay tests 10,000 randomized sweeps and 480 forced long sweeps crossing
word boundaries against a naive implementation. It also compares complete
blank-run tapes against a separate step-at-a-time simulator for both machines
at the 100-million-parent-step boundary, and for the original at one billion
steps. The final failure tape is independently reconstructed from the exact
source frame. The result is a finite computational witness, recorded in
[accelerated-blank-receipt.json](accelerated-blank-receipt.json); it has not
been formalized in Lean. A failed bounded block does not rule out later
rejoining, and the witness does not prove different halting behavior or a
consistency equivalence for the candidate.

The screen allows only one changed row total, not two changed helper rows,
multistep parent matching, a different tape/head representation, or state
reallocation. Escaping a five-cell window is treated as failure of this
particular certificate template, not as a general machine counterexample.
