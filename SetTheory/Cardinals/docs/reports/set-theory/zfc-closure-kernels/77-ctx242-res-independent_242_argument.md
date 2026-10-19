# Independent audit of the 242-state contextual fold

The exact inherited Combined243 input has SHA-256
`4207fc3d1bb16f3c64c3cff0980eaa1486160c3f467aee7685740a39e3df7300`.
All labels below refer to this input; start is95 and terminal is254.

Delete state27, redirect the targets of rows18/0,47/0,65/0 from27 to15,
and replace row15/0 by `(0,L,32)`. There are242 remaining working states,
484 total binary rows, and exactly four changed retained rows.

## The old-machine invariant

For each state in `{15,18,47,65}`, every incoming old transition writes0
and moves right. Thus at each reachable occurrence of any of those states,
the cell immediately to the left of the head is0. The start95 satisfies
the implication vacuously. This invariant holds from every initial tape
and head, by ordinary induction on the number of old transitions. It makes
no consistency assumption and needs no register-frame interpretation.

## Matching complete configurations

Paired endpoints have identical head, tape, and inherited control label,
and their label is not27. The invariant is required only on the old side.

* At old15 reading0, the old transition reaches21 one cell right in one
  step. The new machine follows15→32→45→21 in three steps. Its first move
  visits the invariant's zero immediately to the left; its next move
  returns to the unchanged current zero. The endpoint has exactly the same
  head and entire tape as the old one-step endpoint.
* At old18,47,or65 reading0, the old machine follows caller→27→32 in two
  steps. The invariant makes the read at27 equal0. The new machine follows
  caller→15→32, also in two steps. Both write0 to the same two zero cells
  and end two cells left at32. The new intermediate occurrence of15 need
  not satisfy the old-side invariant; no proof premise requires that.
* Every other retained row agrees literally. None of these ordinary rows
  targets27, because the three treated caller rows are its only incoming
  rows. No matching block passes through the halt state internally.

Both clocks are strictly positive and bounded by3. Hence concatenating
blocks gives arbitrarily long matching trajectories for either infinite
run. A finite halt is attained on one side if and only if it is attained
on the other, since no block hides a halt in its interior and terminal
endpoints match. Equivalently, strong induction on the remaining length
of a finite halting run proves both implications. Therefore this242-state
table and Combined243 have identical halting behavior from95 on every
binary tape and every head position.

The theorem is an ordinary finite combinatorial proof, formalizable in PA.
It is a relative machine theorem: the connection to `Con(ZFC)` is supplied
by the baseline's separately established ordinary calibration. No claim
is made here that the finite checker is a kernel proof.

## Independent executable audit

`independent_242_audit.py` reparses the SHA-bound input, creates the four-row
patch independently, checks every invariant incoming row and all480
ordinary equal rows, and verifies the four block identities on every
five-cell local assignment satisfying the guard. Every executed read lies
inside the represented window, while the arbitrary exterior is untouched.
These finite enumerations check the universal local premises; they are
not samples of an actual blank computation.

## Separate source-encoding observation

The source tree has another transfer-plus-one block, physical register8
into7 (logical6 into1), at four prefixes:

`11101001001011000011`, `1110100100101110011`,
`1110100101100011`, and `111110011`.

Each has the form `(while R8>0: R8--; R7++); R7++` and may be rotated to
`R7++; while R8>0: R8--; R7++`. Its physical root is inherited142.
The natural right-associated rotated decoder can reuse17, with
142/0→72 and142/1→17. This observation alone saves no state: old37
and55 implement transfer bodies needed by other source contexts. It was
not used in the242-state construction and was not promoted to a calibrated
new table. The source change would need a complete context check, runtime
check and separate exact bootstrap before any combined optimization claim.
