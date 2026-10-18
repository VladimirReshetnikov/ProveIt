# Decoder reassociation: exact instance and context obstruction

## Status

This directory contains a reproducible search frontier, one universally checked
runtime reassociation at 246 states, and rejected 245-state decoder candidates.
It does **not** contain a validated machine with fewer than 246 working states.

`export_grammar.py` exports the literal context246 table and frozen `Prog254.v`
into `closed-sequence-grammar.json`. The table and source SHA-256 values are
included. The export has 127 pure sequence states, 24 entry roots referenced
from outside that set, 35 physical atomic states, 44 observed semantic atomic
variants, and a 226-node hash-consed representation of the full source AST.
The largest required word has 702 atomic occurrences. The required root words
have 921 occurrences in total.

The 127 states are selected from the decoder states reached through an
unchanged bit-preserving right-moving prefix of the actual binary machine.
Each has one observed source subtree and two closed child subprograms. The
closedness calculation checks that no break or continue escapes the subtree;
it does not assert termination for all register values. The unchanged
ordering of closed partial subprograms permits ordinary sequence
reassociation.

The physical and semantic word exports serve different purposes. A physical
word identifies each atomic occurrence only by its binary state. A semantic
word distinguishes different observed source expansions of the same physical
state. Even an atom with only one observed semantic expansion can depend on
its preceding bits: state 81 is a useful example. Consequently neither word
export alone is a complete binary-machine compiler.

With 119 working states outside the selected sequence grammar, the optimistic
cost is `119 + K + U - S`, where `K` is the new number of sequence states, `U`
counts additional states needed to unfold context dependencies, and `S` counts
scanner states actually removed with a valid phase invariant. Improvement
requires `K + U - S <= 126`. A successful 127-rule grammar with maximum source
zero run reduced from seven to six is therefore also potentially useful, if
the complete scanner phases permit the one-state scanner deletion.

## A successful runtime reassociation with unchanged state count

The old transitions implement

```
226 = (193, 231)
193 = (190, 213)
207 = (213, 231)
```

Changing 226 to `(190,207)` reuses the already present right-associated pair.
The complete corresponding source substitution has a 2,980-entry register
program bisimulation. Its literal all-site checker passes all 8,391 guarded
cases, with at least 13 literal steps in every case and unchanged maximum
zero-run length seven. The supporting script and result are `rotation226.py`
and `rotation226_result.json`.

State 193 still has another incoming edge from 162 on bit one. It therefore
cannot be removed, and the resulting table still has 246 working states.
The result establishes a whole-frame runtime transformation. A separate
blank-start proof for this variant was not part of this experiment.

## The attractive 178/208 saving

The original grammar contains

```
178 = (23, 208)
208 = (24, 206)
 16 = (23, 24)
```

All three component subprograms are closed. Replacing 178 by `(16,206)` and
deleting 208, whose only physical incoming edge is `178/1`, yields a literal
245-working-state table. The intended source is the global exact-subtree
replacement `(23,(24,206)) -> ((23,24),206)`. Its maximum leaf depth remains
34 and its maximum zero run remains seven. Its register program has a valid
bisimulation with the original program: 2,985 pairs, 5,968 outgoing edges, and
one halt pair.

`rotation178_bisimulation.json` serializes that certificate. The independent
edge rechecker `check_bisimulation_certificate.py` checks both initial
increment segments, every paired decrement register, the increment counts
between tests, every successor pair, and halt agreement. These facts concern
the two **register programs**. They do not certify the candidate binary table.

The first binary failure is a folded partial entry, not excessive depth. At
source site 894, address `11101001001010100111000000`, the original decoder
executes the following bit-preserving detour:

```
218 at position 23, read 0: move left to 154
154 at position 22, read 0: move right to 178
178 at position 23, read 0: move right to 23
```

The final zero has already been tested by state 218. It is a fixed-prefix
entry into 178, not a new unrestricted entry at the root of that source
subtree. Changing `178/0` to state 16 adds the state-24 subprogram to this
partial entry. The intended source replacement does not include that extra
behavior. The all-site symbolic checker accordingly encounters a mark on
physical register zero where physical register two is required.

The one-row repair `218/0 -> (0,L,178)` restores the old three-step destination
when the preceding bit is zero. It fails when that bit is one. The original
one-context detour is `218 -> 154 -> 179 -> 105`; the repaired detour is
`218 -> 178 -> 206 -> 23`. A bounded literal witness is recorded by the machine
search at address `11101001001010100010110000`, original source site 539.
The interval certificate admits its zero branch and arbitrary values of the
other registers except the already positive enumeration counter. Thus the
new interval analysis does not exclude this failing fixture.

The one-row repaired table agrees with the baseline's finite blank bootstrap,
including the 410,735-step endpoint. That agreement and register-program
bisimulation still leave a failed table-to-program link. None of these
diagnostic tables is asserted to meet the requested consistency equivalence.

## Fixed-prefix constraints

The state-218 detour imposes more than a requirement to preserve the complete
word represented by state 154. If its decoder is regrouped while this atomic
shortcut is retained, the following descendant words must also be preserved:

```
154 / 00 = word(23)
154 / 10 = word(105)
```

The export contains conservative fixed-prefix constraints obtained from
left-moving entry rows. Its first version contained 18 constraints from nine
direct left-moving entries into mutable sequence roots. The subsequent
version also includes four constraints for shortcuts crossing the unchanged
pure state 177 before reaching a mutable root:

```
175 / 0 = word(113)       175 / 1 = word(105)
207 / 0 = word(213)       207 / 1 = word(231)
```

The final instance therefore has 22 constraints. Where a projection reaches
an atomic word before all fixed bits have been consumed, the export stops
early and preserves that atomic boundary. This is deliberately conservative,
and the constraints are not advertised as a complete proof of every context
dependency. The bounded grammar searches performed by the other search agent
used their frozen **18-constraint** snapshot; the later 22-constraint instance
must not be substituted when describing those executed searches.

Any favorable grammar result must still be reconstructed as a literal binary
table, related to its exact new source addresses, checked against complete
unbounded frame contracts, and given a blank bootstrap proof. In particular,
longest source zero run and maximum decoder depth must be re-evaluated after
regrouping; the unconstrained semantic 126-rule result had values 12 and 46,
which exceed the baseline scanner and the inherited `d >= 40` frame interface.
Depth 46 by itself is not a state-count obstruction: the actual blank frame
has distance 181, and the existing frame transformations never decrease that
distance. A stronger minimum-gap premise could accommodate a deeper decoder
without extra states. The zero-run growth and actual folded-entry failures
remain separate problems. Consequently a depth-at-most-40 search guard is a
conservative limit of that search family, not a necessary bound on machines.

## Independent commutation enumeration

`commuting_rotations.py` examines both association shapes at all selected
closed sequence states, requiring a physically private inner sequence node.
For each of the 80 such shapes, it considers the five nonidentity
permutations of the three subprograms. Every reversed pair must have disjoint
increment/decrement register support, and neither member of a reversed pair
may contain a halt. This sufficient condition permits exchanging their
possibly partial computations without changing the program's result or
termination behavior. Break/continue closedness is inherited from the
selected sequence children.

Of the resulting 400 proposals, one satisfies the commutation condition, and
none admits the needed reused pair among the 162 observed pure source
decoder states. `commuting-rotations-result.json` records the exact family and
counts. This is a finite negative structural result, not a lower bound for
arbitrary program grammars, reachable-state specializations, or machine
representations.
