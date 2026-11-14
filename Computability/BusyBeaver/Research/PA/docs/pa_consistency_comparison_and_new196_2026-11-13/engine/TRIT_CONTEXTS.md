# Source-reachable local contexts for the diagonal 196-state machine

This experiment strengthens the arbitrary-register frame contracts used by the
previous local-fold searches. It does not assume the consistency of PA.

## Audited finite source invariant

The source program has 3,700 instruction sites. Its initial clean frame is site
25 with logical registers `(2,0,0,0,0,0,0,0,0)`. The abstraction maps each natural
register value to `0`, `1`, or `2` (the last means at least two). Increment is
saturating. A positive decrement of trit two admits either trit one or trit two.
All other source operations have their actual control successors. Thus every
concrete transition has an admitted abstract transition.

`joint_trits.cpp` computes a finite least fixed point and then independently
checks its seed and every abstract successor. For the new diagonal source it
contains 4,319,427 site/vector pairs and 4,848,294 abstract edges. The explicit
halt instruction, site 10, is abstractly reachable. This invariant is therefore
not a certificate of nonhalting. Sites 8, 3662, and 3663 are unreachable; tests
7 and 3661 take only their zero branches. Site 8 is a continue instruction, not
the halt instruction.

The source CFG is independently reconstructed from leaf paths and compared to
the axiom compiler's CFG. The fixed-point bitset has SHA-256
`cf135dfb69ff7eddd84685dcbab151d77a225e4ebe1ab17b7cd2a441bf2d9447`.

## Affine marginal refinement

At each source site, project the fixed point onto each of the nine register
coordinates. The Cartesian product of these nine projections is an
**overapproximation**, so no correlation assumption is required. Each possible
coordinate set is represented as an exact finite union of affine ranges:

| Trit mask | Concrete set | Symbolic cases |
|---|---|---|
| 1 | `{0}` | `0` |
| 2 | `{1}` | `1` |
| 3 | `{0,1}` | `0`, `1` |
| 4 | `{2,3,...}` | `2+x` |
| 5 | `{0,2,3,...}` | `0`, `2+x` |
| 6 | `{1,2,3,...}` | `1+x` |
| 7 | all naturals | `x` |

The variable `x` ranges over all naturals independently. Decrement cases also
intersect the tested coordinate with the selected zero or positive branch.
The full symbolic tape executor then checks each restricted frame contract.
No finite register-value sampling is used. The ordinary affine-run window
collector covers every boundary distance up to the observation radius and the
saturated run interior. The actual 58,154-step blank startup is included
separately.

`trit_contexts.py` retains the prior conservative treatment of only the four
generic list-traversal routines. `trit_ones_contexts.py` uses the stronger spare
invariant described next.

## All spare registers have value one

The explicit clean startup frame has 26 spare blocks, each of value one. Each
source primitive preserves the existing spare sequence; an increment appends
one additional spare block of value one. Therefore every reachable clean
frame has an all-one spare sequence of length at least 26. This is a separate
elementary induction, compatible with the trit invariant on the nine primary
registers.

In the full affine executor, the distinguished first spare is instantiated as
one, and the remaining spare-list variable denotes at least 25 one-valued
blocks. A block is `B(1)=011`; its temporary traversal representation is
`C(1)=101`. The four generic list lemmas are independently rederived from the
literal transition table. Their concrete value-one instances traverse one
three-cell block monotonically, return to the same traversal control, and
produce the stated output block.

For each symbolic list call, `trit_ones_contexts.py` explicitly simulates all
75 transitions across 25 one-valued blocks, for every admitted prefix on each
exterior side. It checks the endpoint control, displacement, and every output
cell. For an observation radius of at most four, all longer lists have exactly
the same possible interior local windows: a window sees either the first few
blocks and the entry boundary, the last few blocks and the exit boundary, or a
periodic interior whose phase has already occurred in the 25-block execution.
This follows directly by shifting whole three-cell blocks. No coarse engine
state fill is needed in this variant.

## What a surviving fold would establish

The output contexts contain every reachable literal state/window, using the
source invariant, source primitive simulation, and exact startup. A local
fold may replace each parent literal transition by a positive bounded number
of child transitions with the same whole-tape effect, head position, and
projected next control. Such a certificate yields a stuttering simulation by
induction, and preserves blank halting and nonhalting. This is an executable
mathematical argument; no Lean kernel verification is claimed.

The finite fixed-point invariant itself does not establish the new axiom
emitter's arithmetic completeness, nor the final PA-internal equivalence with
consistency. Those are separate obligations in the mathematical report.

## Four zero-closing variants

The closing variants replace the final AX break at site3580 by a decrement of
logical register3,4,5, or6. Each tested register is zero at that site according
to the separately recomputed finite source invariant. The zero branch has the
same source effect and successor as the original break. The literal tables
differ from the base only in row `(2067,1)`; their native-label lists agree.

`closing_diff.py` checks all4,815 unrestricted base primitive contracts and
records every source site that can visit control2067. Only sites3550 through
3580 occur, encompassing45 primitive branches. Every other primitive execution
is unchanged: a first differing transition would have to visit the changed
control, which its verified base execution never does.

The collector retains the entire base enclosure, checks the69 restricted
affine cases for those31 affected sites in each variant, and rechecks the
complete blank startup. The union has2,181 windows per variant. Retaining old
contexts can cause conservative rejection; it cannot discard a newly reachable
window. The collector reruns the differential case-selection checker when
these subset options are used, binds machine/source/label/base-context digests,
and still enforces the full source-CFG/fixed-point closure digest chain.

The portable wrapper independently resolves and audits all five source graphs
and fixed points before checking these differential receipts. All four refined
five-cell,16-step,two-row screens covered38,220 ordered identifications with
no survivor. Their exact counts are retained alongside each dataset.
