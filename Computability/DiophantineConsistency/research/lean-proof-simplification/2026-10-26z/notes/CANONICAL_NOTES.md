# P4 — Recognize every actual operating row as the existing canonical row

## Status and novelty boundary

This is the sole retained proposal from the syntax/Wang-row review. The refreshed
exclusion packets already propose centered integer induction, shared edge-row
construction, the minimum-of-two-heads pulse, exact construction bridges, and
related trace-bound simplifications. **Assume all of those are installed and give
them zero novelty credit here.** The new invariant runs in the other direction:
an arbitrary allowed row in the derived strip is forced to equal that canonical
constructed row. The refreshed reports and evidence were screened for this
recognition invariant and for its optional local determinism lemma; no matching
proposal was found by the novelty auditor.

The most conservative implementation is the complete but **unvalidated Lean
candidate** in `CanonicalOperatingRow.lean`. It strengthens an existing receiver
lemma, retains the existing far-cell proof, and derives the old soundness statement
from whole-tile equality. `EdgeRecognition.lean` is a second **unvalidated Lean
candidate** for a stronger implementation that consolidates the mirrored edge
analyses. The local finite determinism property supporting that stronger route
has been checked against all 942 literal tuples by `check_tile_determinism.py`;
this is explicitly a Python data check, **not a Lean proof**. No integrated patch,
whole-project compilation, net LOC reduction, or runtime improvement is claimed.

Source evidence was read from commit
`553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`; the parent report tracks the later
exclusion-corpus refresh. The data audit records exact Core/Data SHA-256 hashes.
All source paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## The existing duplication

`WangTiles942RowStep.lean` proves soundness of an arbitrary allowed strip row:

- `far_west_zero`, lines38–71, examines the previous cell: left wall, old head,
  or ordinary input. The old-head case splits the action direction.
- `far_east_zero`, lines73–103, performs the corresponding analysis of the next
  cell, with a different wall bound and reversed active direction.
- `far_pass`, lines107–121, combines the two edge facts with the independently
  proved absence of south438, obtaining the whole literal pass tile.
- `receiver_south`, lines126–162, obtains the whole receiving-tile equality in
  each direction and immediately projects its south field.
- `south_step`, lines166–186, splits old head, moved head, and other cells and
  translates each result into the actual machine's color semantics.

`WangTiles942StepConstruction.lean` already constructs that same old-head /
receiver / pass row. Its north and south semantics appear at lines85–114; they
already include the write-and-move transition that enters halt. The preceding
shared-edge proposals strengthen this construction further. Recognition should
reuse that installed semantics instead of restating it for each arbitrary-row
cell role.

## Minimal route: retain the equalities the proof already has

Strengthen `receiver_south` to

    receiver_tile ... : T x t = receiveTile cfg q x.

The existing left and right proofs invoke
`WangTiles942Signals.left_transition_receiver` (line90) and
`right_transition_receiver` (line74). Both return equality of the entire Tile
record. Their final `congrArg Tile.south` is therefore where useful information is
lost. Keep the equality and simplify the literal receive constructor once.

Now combine three existing local facts:

| Cell role | Equality already available |
| --- | --- |
| x = old head | `head_transition`, HeadBounds line30 |
| x = moved head | strengthened `receiver_tile` |
| all other interior x | `far_pass` |

The resulting recognition invariant is

    row_eq_stepTile ... : T x t = stepTile cfg q x.

The prototype's old `south_step` statement becomes

    rw [row_eq_stepTile hA hH hTime hs hrow q hq x hl hr]
    exact stepTile_south cfg q hq x

When the prior edge construction has made the south field definitionally the
machine-step color, even the final construction theorem is just that inherited
projection. This recognition fact additionally gives uniqueness of the entire
interior row: two valid realizations of the same configuration both equal the
same `stepTile` at every interior position.

This minimal version still has a three-way position split. It improves the
invariant and consolidates semantic interpretation; it does not by itself prove
fewer partitions or a net line-count reduction. Keeping `head_south` and
`receiver_south` as compatibility wrappers adds their signatures to the cost.
Their only current consumers are RowStep and its Checks file, so an integrated
review can decide whether to retain wrappers or update those local checks.

## Stronger route: determine edges once, then use local tile determinism

The existing proofs treat a common horizontal edge twice, once as the right
field of its left tile and once as the left field of its right tile. The prior
work fixes that redundancy for constructed rows. The new recognition route
proves the analogous invariant for **arbitrary allowed strip rows**, using the
actual wall and row-encoding hypotheses.

### A. One zero-edge lemma for a pair without the head

Let l=-L and r=R. For an edge x→x+1 with l≤x and x+1≤r, assume neither endpoint
is the encoded head. Then prove `(T x t).east=0` by one boundary analysis:

1. If x=l, the left wall's east color is at most2. Matching transfers that bound
   to the plain right endpoint; `plain_west_small_eq_zero` (Signals line53)
   forces zero.
2. If x+1=r, the right wall's west color is at most4. Matching transfers the
   bound to the plain left endpoint; `plain_east_small_eq_zero` (Signals line44)
   forces zero.
3. Otherwise both endpoints are interior plain inputs;
   `plain_pair_edge_zero` (Signals line62) forces zero directly.

The unequal wall bounds are preserved. There is no symmetry assumption on the
rails or walls. `RowEncodes.head_left/head_right` already ensure that an integer
head lies strictly between the walls, so the two walls cannot be adjacent; no
additional strip-width premise is needed. The candidate `nonhead_edge_zero` in
`EdgeRecognition.lean` has no operating-state, time-matching, or direction
hypothesis.

### B. The head tile determines every internal edge

The preceding lemma gives a particularly simple exact formula:

    (T x t).east =
      if x = cfg.head then (T cfg.head t).east
      else if x+1 = cfg.head then (T cfg.head t).west
      else 0.

At the left endpoint equal to the head, this is substitution. At the right
endpoint equal to the head, it is horizontal matching. Elsewhere it is the
zero-edge lemma. Thus there is no action-direction split and no moved-head
arithmetic in `edge_shape`. Apply this formula to the arbitrary row, use
`head_transition`, and compare with the **already installed** canonical
construction's edge field. Equality of east colors follows; equality of west
colors follows from horizontal matching at x−1.

This is recognition/uniqueness of the boundary values in an arbitrary constrained
row. It neither reintroduces shared-edge construction as a new suggestion nor
assumes row/step equivalence.

### C. Use the correct partial determinism of the literal tile language

A completely unguarded statement that west/north/east determine the tile is
false. The exact finite audit found only these ambiguous input triples:

| (west,north,east) | Indexed rows | Possible south values |
| --- | --- | --- |
| (0,0,0) | 433,923 | 0,438 |
| (0,1,0) | 434,924 | 1,438 |
| (0,432,0) | 431,925 | 432,438 |
| (0,433,0) | 432,926 | 433,438 |
| (1,438,1) | 930,931,932 | 434,435,436 |

The first four are precisely pass/finish pairs. The last is the three reset
outputs. There are 5 ambiguous keys and 7 unequal unordered collision pairs
before the guards are imposed. Initializer and seam tiles produce no additional
exceptions.

The broad local property is therefore:

    Allowed a -> Allowed b ->
    a.north != 438 -> a.south != 438 -> b.south != 438 ->
    a.west = b.west -> a.north = b.north -> a.east = b.east -> a = b.

After excluding input438 and output438, the audit contains 935 tiles and 935
distinct (W,N,E) keys. For the intended consumer, prefer the narrower hypothesis
`a.north <= 433`, already supplied by `RowEncodes.color_bound` (RowEncoding
line28). With output438 excluded, exactly922 tiles satisfy this guard and all
922 keys are unique. This avoids proving irrelevant initializer/seam cases in
the Lean helper.

A proposed Lean interface is:

```lean
theorem normal_tile_ext {a b : Tile}
    (ha : Allowed a) (hb : Allowed b)
    (hnorth : a.north ≤ 433)
    (hsa : a.south ≠ 438) (hsb : b.south ≠ 438)
    (hw : a.west = b.west) (hn : a.north = b.north)
    (he : a.east = b.east) : a = b
```

This is a proposed signature, not an already verified theorem. It can be proved
using the installed constructor-view/classification APIs: operating north
colors force their transition, halted north colors give pass/finish, plain
north colors give pass/finish/receive, and actual rail injectivity distinguishes
targets in the receive case. Count the helper proof as a real cost. Generic
constructor views, finite dispatch, and a finite-certificate technique are prior
work and are not claimed as additional ideas.

For an actual interior cell, supply this helper with:

- actual/canonical Allowed proofs;
- the original `hrow.north` and inherited canonical north projection;
- the two edge equalities from B;
- `RowEncodes.color_bound`;
- the existing `no_south438` theorem for the arbitrary row;
- the canonical south projection and `WangMachineEncoding.color_le_433` for the
  constructed row.

Then the whole-tile recognition theorem follows uniformly, without a separate
receiver case or a separate far-pass case. Its south projection is the existing
soundness theorem. This is the route that can remove the duplicated directional
and local-role analyses, provided the supporting lemma and wrapper costs remain
reasonable when implemented.

## Soundness and dependency checks

`WangTiles942StepConstruction` imports WangMachineAction and WangMachineStep,
not RowStep. Reusing construction semantics in recognition creates no import
cycle. The `no_south438` theorem is in `WangTiles942OperatingRow.lean`, line43;
it derives no-finish independently of `south_step`. Reusing it in `far_pass` or
`normal_tile_ext` is therefore noncircular.

Preserve the original premises `hA`, `hH`, `hTime`, `PersistentStrip`,
`RowEncodes`, the same open-interval bounds, and `cfg.state=some q`. In the
stronger implementation only the *intermediate edge-shape* theorem needs fewer
premises; the final recognition theorem retains the original requirements.
Never turn no-finish into an external assumption.

Target215 is preserved. The finite audit includes receive tiles831 and832,
whose south colors are432 and433. A live action entering halt still writes and
moves, and the destination reads its old tape bit. The inherited construction
semantics already proves this; neither recognition route replaces it with the
stationary behavior of an already halted configuration. Arbitrary reset rows
remain outside local determinism, and finish ambiguity is removed only through
the existing independently derived theorem.

## What is established, and what remains

Established by source review and the finite Python audit: the target theorem
signatures, noncircular dependencies, exact collision exceptions, all942 row
indices, target counts45/199, all432 rail-cache entries against their defining
cardinality formula, 935/935 guarded keys, and 922/922 operational keys.

Not established in Lean for this proposal: `normal_tile_ext`, compilation of the
candidate edge/receiver/recognition files, replacement of production bodies,
compatibility-wrapper cost, and any measured net size or speed improvement. The
complete file artifacts make these next steps concrete without overstating the
validation. The conservative receiver-strengthening prototype offers a smaller
first integration; the edge-shape/local-determinism route offers the larger
potential reduction in repeated case analysis.
