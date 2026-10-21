# Two additional predecessor-marker transformations of K215

Base: the exact native K215 table at ProveIt commit
`b6fb232916d008383e7cf2990d68ddb30fded7db`, SHA-256
`9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2`.
The accepted base has 215 working states and start state 0.

These transformations preserve the number of working states. They expose
two previously separate decoder roles as one boundary role plus an internal
selector, potentially providing different opportunities for later sharing.
They are not themselves reductions to 214 states. The local simulation adds
two steps whenever its exceptional branch executes; no speed advantage is
claimed.

## Transformation M124

In the base table, states 124 and 127 both have read-one row `1 R 138`.
Their read-zero rows are respectively `0 R 62` and `0 R 14`.
The sole incoming transition to 124 is `104/1: 1 R 124`, while the sole
incoming transition to 127 is `110/0: 0 R 127`. Therefore the cell immediately
left of the head is 1 at every entry to 124 and 0 at every entry to 127.
Neither state is the start state.

Map the old role 127 to role 124, redirecting the incoming `110/0` row.
Reuse physical state 127 as the marker selector. The four changed rows are:

| Row | Old | New |
|---|---|---|
| 110/0 | 0 R 127 | 0 R 124 |
| 124/0 | 0 R 62 | 0 L 127 |
| 127/0 | 0 R 14 | 0 R 8 |
| 127/1 | 1 R 138 | 1 R 59 |

Provider state 8 has read-zero row `0 R 14`; provider state 59 has
read-zero row `0 R 62`. Thus, when the current cell is zero, the new
machine takes three steps: left to the selector, right to the provider
chosen by the unchanged marker, and right to the correct old target.
The complete tape is unchanged, and the final head is one cell right of
its initial position, exactly as after the old single step. When the current
cell is one, the common old row is retained.

States 109 or 125 can replace provider 59 because their read-zero rows are
also `0 R 62`. The main artifact chooses 59 deterministically.

## Transformation M160

States 160 and 190 both have read-zero row `0 R 99`. Their read-one rows
are respectively `1 R 99` and `1 R 52`. Their only incoming rows are
`139/0: 0 R 160` and `165/1: 1 R 190`. Consequently the predecessor marker
is 0 at old role 160 and 1 at old role 190, for every initial binary tape.

Map old role 190 to 160, and reuse physical state 190 as a selector:

| Row | Old | New |
|---|---|---|
| 160/1 | 1 R 99 | 1 L 190 |
| 165/1 | 1 R 190 | 1 R 160 |
| 190/0 | 0 R 99 | 0 R 86 |
| 190/1 | 1 R 52 | 1 R 193 |

The provider rows `86/1: 1 R 99` and `193/1: 1 R 52` finish the
three-step simulation. The exceptional current symbol is one here, whereas
M124 discriminates on current zero.

## Composition and all-tape theorem

The modified rows of M124 and M160 are disjoint. Neither uses a changed
provider row of the other. Their maps commute, yielding a table with eight
changed rows and simulation map `127 -> 124`, `190 -> 160`.

The repository's earlier CM215 transformation (`176 -> 52`, with physical
176 reused as selector) also composes. The resulting table has 14 changed
rows. Its exceptional path through `189/1` and `156/1` forces current symbol
one at old 176 and therefore does not invoke that transformation's current-zero
discriminator. The complete finite incoming-edge check appears in the builder.

For any of the shipped variants let phi be its map on old control states,
with identity elsewhere. Starting from old and new state 0 on the same
arbitrary binary tape at the same integer head position, induction on old
time establishes configurations at new times t(n) with exact tape and head
equality and new control phi(old control). If the next old transition is an
exceptional discriminator, set t(n+1)=t(n)+3; otherwise set t(n+1)=t(n)+1.
The local three-step computations above verify the exceptional cases;
all remaining rows are literal phi-mapped copies. Marker conditions follow
from the complete predecessor enumeration, with the stated two-step
exception for the inherited CM215 pair.

Thus n <= t(n) <= 3n. All internal states of each three-step block are
working states. A halting transition is preserved at a corresponding boundary,
and the new machine cannot halt inside an exceptional block. It follows that
old and new machines halt together on every initial tape from state 0. This
is stronger than the blank-tape consequence needed here. It does not assert
equivalence when either machine starts arbitrarily inside a replaced role.

Combining this all-tape theorem with the accepted exact K215 calibration gives
in ZFC the ordinary mathematical theorem

    not Halt(M, blank) <-> Con(ZFC).

The proof above is finitary and formalizable in very weak arithmetic; no new
Lean/Rocq endpoint is claimed for these tables. `build_marker_family.py`
constructs each literal table and checks every finite premise of this proof.

## Novelty check and limitations

At the pinned snapshot, `compare_marker_family.py` examines 321 parseable
215-state `.tm` occurrences under Research/ZFC, representing 84 distinct
rooted transition graphs. All four shipped variants differ from every one
of those graphs, also after global tape reflection. The comparison is an
exact graph-isomorphism test for that bounded corpus, not a claim of global
historical novelty or behavioral inequivalence (the variants are deliberately
behaviorally equivalent).

These selectors apply the already published CM215 general idea to different
source roles; the new contributions are the two concrete role choices, their
simple unconditional marker invariants, their jointly valid composition, and
the exact checked tables. Attribution for the underlying calculus, K215
machine, compiler and original conditional-marker technique remains with the
ProveIt authors and the authors recorded in the repository notices.
