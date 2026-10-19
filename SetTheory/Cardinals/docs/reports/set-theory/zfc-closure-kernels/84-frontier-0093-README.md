# Two new arithmetic experiments at the 246-state frontier

No machine with fewer than 246 working states and the required blank-tape
consistency equivalence is established by this packet. All state numbers
below are the frozen reference's original labels; halt 254 is separate.
The reference SHA256 is
`303911c554284c49ce09042d8127feba4da260baae766e32260034aa3bdb82ee`.

## Positive-offset representation

`offset246_old.tm` changes four rows and retains 246 working states:

| State/read | Write/move/next |
|---|---|
|75/0|1,L,131|
|75/1|1,R,255|
|255/0|0,L,112|
|255/1|1,L,63|

Every primary logical value n is represented by physical unary value n+1.
Increment appends a value-zero spare. The checker proves three local
contracts for arbitrary natural values and arbitrary finite lists by literal
steps, unary-loop induction, and structural block-list induction. Zero
requires only a zero cell after the selected physical value-one block; that
cell can be the following separator or the blank exterior. This representation
therefore admits zero-valued spares as an invariant. No blank initializer for
this representation is claimed.

The new core passed all 8,391 original guarded instruction fixtures under the
new physical representation. Two complete pair-merge screens, each of 120,540
row-provider recipes, had no survivor: one with spare values[0,2], the other
with[0,0]. A further 135,240 recipes deleting a state with one external incoming
row and changing that incoming action, with its target among the retained working states, also had no survivor on the zero-spare
suite. All searches use a 20,000-step limit and a 512-cell tape window. Their
negative outcomes are finite diagnostic results, not semantic impossibility.

## Prefix-left increment: a new 245-state local core, with a controller failure

`partial_prefix_left245_old.tm` deletes state255 and changes only:

| State/read | Write/move/next |
|---|---|
|75/0|0,L,112|
|83/0|1,L,112|

The first change is the previously identified decrement-preserving deletion.
The second sends increment through the reverse carry, increasing the selected
register by moving the register prefix left. This avoids the right-end pulse.
The word/list theorem in `runtime-verification.json` proves the exact local
operation, including the entire temporary one-run to the left of the file.
That one-run is shifted too. Its left edge gains a one, which changes the
controller's branch.

An exact original CI8 fixture has path 01010, header distance 181, physical
registers [1,4,2,0,3,1,4,2,0], spares [1,1], and head 0. The reference returns after
1,618 moves to path 01011. The 245-state mutant's first dispatch after its
increment arrives after 1,540 moves at path 011. The register increment and
one-cell left shift of the file are correct, but the program counter is wrong.
This is a prepared-frame counterexample, not a blank-run halt claim.

All 980 actions with a retained working-state target for the unique external
increment-entry row 57/1 were then
screened against that one exact fixture, accepting an exact desired endpoint
at any tick through 20,000. None passes. The complete action ledger is retained.
Other edits, larger bounds and different representations are outside this
search.

Even a repair of this controller defect would leave a space obligation: in
an intended variant with no added spare blocks, each INC decreases the
marker-to-file distance by one, each positive DEC increases it by one, and a
leftward program-counter overflow increases it by one. Thus, as long as the
intended frame relation is maintained, distance plus the sum of primary
registers equals its initial value plus the number of such overflows. This
identity alone is not a proof that the actual program exhausts its gap.

## Reproduce the new checks

With Python 3.10 or newer, assertions enabled:

```sh
python3 -B check_runtime_variants.py --search-entry --output /tmp/runtime-verification.json
```

This freshly proves the six local contracts, checks both literal traces and
whole tapes, and repeats the 980-action entry experiment. Omitting
`--search-entry` omits that optional finite search. The checker is an ordinary
mathematical induction checker; it is not a proof-assistant certificate.

To reproduce the offset pair/entry screens in separate output directories:

```sh
python3 -B make_offset_cases.py \
  --program /path/to/ProveIt/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/tm/Prog254.v \
  --spares 0,2 --output /tmp/offset-arbitrary.txt
g++ -O3 -std=c++17 pair_merge_search.cpp -o /tmp/offset-pairs
mkdir /tmp/offset-pair-arbitrary
cd /tmp/offset-pair-arbitrary
/tmp/offset-pairs /tmp/offset-arbitrary.txt
```

Repeat with spares 0,0 and a new directory. Compile `one_action_search.cpp` and
pass the zero-spare fixture file to repeat the 135,240-action experiment.
The original run summaries are retained. The larger program source is read
from the supplied repository path rather than duplicated in this small packet.

## Attribution and limits

Mira-Cult designed the compact calculus and original machine; Jeff Ketchersid
provided verification and symbolic machinery; Andrew James Wade provided the
compiler framework; mira-emmy supplied the public253 reduction. ProveIt and
the context246/prefix250 authors retain their register permutation, carry,
contextual-fold and calibration contributions. `word_induction.py` is adapted
from the generic symbolic induction checker in the prior context246 research
packet, with eager reference-table loading and unused clients removed.
`literal_reference.py` and the pair-merge search come from the attributed
beyond246 packet. The new work here is the offset representation, its row
patch and proofs, the reverse-prefix increment experiment, and the new
fixtures, searches, and exact controller obstruction. Original licenses and
notices retain their scope.

## Stronger source-reachable witness

`check_reachable_prefix_left.py --search-entry` replays the reference from its
blank tape, checks the first two logical instructions, and reaches the same
CI8 phase at stored path 0101 (consumed path 01010), head -5, span 182, physical
registers [0,0,0,3,0,0,2,0,0], and 167 value-one spares. Here the reference
increment returns after 2,590 moves to 01011, whereas the mutant returns after
1,544 moves to 011. All 980 working-target row 57/1 actions also fail on this reached source
frame within 20,000 moves. The mutant's own blank initializer is still unproved.

The complete whole-tape reachability and counterexample evidence is in
`reachable-prefix-left-verification.json`. The original arbitrary-register
fixture remains in `runtime-verification.json` to retain the full research
sequence. `runtime-note.tex` is an editable section source for the main report.
