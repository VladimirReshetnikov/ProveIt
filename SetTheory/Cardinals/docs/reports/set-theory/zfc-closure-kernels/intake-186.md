# Intake 186: clean equality sharing gives a 219-state machine

Placement `24c7e68de7` imports **Source 140**,
`K219_Construction_2026-10-20.zip`, from arrival
`26d5de6d21fa354d50e0b84fe851c289925b8d72`, and retires its ZIP.
The host now reconciles **140 sources**; the collection remains **290 reports**.
Its reviewed snapshot is `5c5d7611a93bf043402d5f740af24f2f00f2edee`, with the
exact Source 138 K220 package as parent; it also inspected the alternatives
at `bf01dd349a`. This is new source/compiler work, so the package is imported.

The [placement map](data/intake186-placement.json) accounts for all **110
members**: 93 new ancillary files (5 root, 28 code, 60 data), two existing
aliases, six within-batch aliases, one historical parent-ZIP alias and eight
archive-only main manuscript/input/PDF/delivery files. Fresh extraction,
staging and independent original-placement-tree checks pass. Delivered files
are unchanged. Historical build auxiliaries supplied by the author are
retained as data, distinct from newly generated catalogue build files.
[Recovery instructions](intake-186-reproduction.md) restore all 110 members.

## The new source idea and its proof

The [published 219-state machine](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/README.md)
changes the generic equality implementation while preserving the calculus.
The old routine computes an absolute difference and then clears it. The new
routine shares an **open subtree** between cancellation and cleanup: its
continue instruction serves different enclosing loops at the two occurrences.
It therefore lies outside a search restricted to sharing closed routines or
reassociating a fixed primitive word.

Write Dᵢ = CD(i), Cⱼ = CC(j), B = CB(1), and `(X,Y)` for an ordered source pair:

```text
P = (D₆, C₂)       U = (P, B)
A = (D₅, U)        L = (A, D₆)
Z = (D₅, C₁)       R = (Z, U)
E = (L, R)
```

For a left child, a one-level break is consumed and skips the right child;
continues propagate. From a right child, a one-level continue repeats the
pair; breaks propagate. Larger control indices are decremented at the
corresponding edge. These are the inherited address-based source semantics.

The all-natural argument is short but stronger than a finite input screen:

1. A cancels both counters. On input `(a,b)` it terminates normally at
   `(0,b−a)` if `a≤b`; otherwise it returns one break at `(a−b−1,0)`.
   Each repeated cancellation decreases both counters.
2. L returns one break with both counters zero exactly on equality. On
   inequality it returns normally with the positive difference reduced by one.
3. R clears register 5 and then register 6, returning one break. Repetitions
   strictly decrease the remaining counter; all other registers are preserved.
4. E consumes L's break on equality and skips cleanup. Otherwise R executes.
   Thus E always terminates, clears registers 5 and 6, preserves every other
   register, and returns normally iff the original values were equal.

The report separately proves the same complete contract for the literal old
routine: its transfer phase terminates at `(x+y+1,0)`, its difference phase at
`(|a−b|,0)`, and its final test clears and branches. Neither routine lets a
continue escape. This proves contextual substitution in both directions,
without any scratch-zero or reachability premise. All four occurrences—the
modus-ponens test, sentinel test and two freshness comparisons—are replaced
literally. Every invocation terminates and no halt occurs inside either
routine, so matching entries/exits preserves finite halting and divergence.

The full source drops from **208 to 206 distinct subtrees** and from 185 to
183 distinct internal nodes, while retaining **4,744 primitive occurrences**,
depth 38 and zero run six. The literal builder verifies four replacements
and these counts; it does not kernel-check the mathematical macro theorem.
The leaf word and internal control flow change, unlike the 220's rotations.

## Why the source saving compiles to one binary state

Delete native states 102, 120 and 121, add 301 and 302, and change eight rows:

| Native row | K220 | K219 |
| --- | --- | --- |
| 87/0 | 0 R 21 | 0 R 301 |
| 87/1 | 1 R 102 | 1 R 21 |
| 88/0 | 0 R 45 | 0 R 122 |
| 103/0 | 0 R 122 | 0 R 108 |
| 103/1 | 0 L 162 | 0 L 302 |
| 108/1 | 0 L 40 | 0 L 10 |
| 113/0 | 0 L 40 | 0 L 302 |
| 198/0 | 1 L 198 | 1 L 40 |
| 301/0, 301/1 | absent | 0 R 45; 1 R 103 |
| 302/0, 302/1 | absent | 0 L 4; 0 L 302 |

The new right-child decrement uses the existing direct entry 21. State 108
shares 86 old `(D₆,B)` occurrences with eight new `(D₆,C₂)` occurrences.
Their complete read-one leaf codes end in `001` and `101`. The new row clears
the final one, crosses the intervening zero, and toggles the earlier bit:
`0→1` supplies a break; `1→0` supplies the two-level continue. All 94 roles
and suffixes are independently checked from the exact source and table.

State 302 supplies the generalized zero-decrement and break return. It clears
a terminal run of ones and uses state 4 to increment the remaining prefix.
Changing `113/0` alone would corrupt increment returns. The `198/0` change
bypasses that row by an exact three-transition identity on the required `010`
local context, retaining the original spare-one convention. The new return,
contextual sharing and increment bypass are all covered by the complete final
runtime, including uses outside these new decoder roles.

The count is **220 − 3 + 2 = 219**, including initialization. Source allocation
has 169 physical decoder states, 184 roles (183 distinct internal nodes, one
duplicated role), 15 extra shared roles and 50 nondecoder states. Counts of
logical roles are not interchangeable with counts of machine states.

## Fresh verification and proof scope

Seven selected jobs ran on disposable copies and passed. The
[core record](data/intake186-fresh-replay/actual.json),
[decoder audit record](data/intake186-fresh-supplemental/actual.json), and
[finite-algebra record](data/intake186-fresh-theory-replay/actual.json)
retain exact commands, exit codes, elapsed times and outputs.

| Check | Fresh result |
| --- | --- |
| Source reconstruction | Four literal replacements; exact delivered source bytes |
| Native construction/allocation | 219 states, 438 rows; exact delivered native bytes |
| Canonicalization and sparse/dense startup | Exact delivered canonical bytes; entire tape after 312,617 steps |
| Complete symbolic runtime | 6,167 cases; 1,515,040 rules; all 438 rows; minimum duration 13 |
| Independent runtime audit | Exact ordered coverage and independently rederived unary/list schemas |
| Independent literal audit | 86 CB1 / 8 CC2 roles at state 108; complete startup |
| Restricted-calculus algebra | 320 restricted-schema instances and 4,368 finite normality-vector checks |

The runtime quantifies arbitrary natural primary registers, gap, first spare
value and finite spare tail. Its 4,000-rule proof-construction limit does not
bound the represented machine's run time or inputs. The stored cases are
compact guard/duration/rule-count receipts; the fresh run regenerates the
symbolic derivations. Finite numerical discovery was not used as its proof.

The canonical machine starts at 0, dispatches at 23 and halts at separate
label 219. Native labels are 0/84/254. The complete blank entry is at head −5,
header 139, gap 80, logical registers `[3,0,0,0,3,0,0,0,0]`, and 130 value-one
spares, with exactly 277 one-cells and zero elsewhere. This differs physically
from K220's entry but represents the same source seed. Both are covered by
their universal frame invariants. Graph reachability and symbolic row usage
are not claims about visiting every state on the one blank run.

Canonical SHA-256 is
`02079501e6255951cbc1c31d2c3cab076574d3d61c892f0e5a541cd1789442ec`;
native SHA-256 is
`b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26`;
source SHA-256 is
`0f6d9d991e36dda1a7449edab72a799bb2d8c3de3ff853a26178b89bd1bc8789`.

Contextual equality substitution, positive whole-frame simulation and exact
startup transport the unchanged parent's finite-refutation calibration.
The result is an ordinary proof, formalizable in ZFC, of blank nonhalting iff
Con(ZFC). **No exact-219 Lean or internal PA endpoint is supplied.** The
[240-state PA theorem](../../../../../../Computability/BusyBeaver/Research/ZFC/rotation240_binary.md)
and earlier K221 formal status remain separate. The intake did not execute a
proof assistant, supplied manifest wrapper, recursive ancestor suite or
exhaustive discovery search. It makes no unconditional nonhalting, absolute
consistency, priority or minimality claim.

## Which earlier ideas stack

The row103 alternative from Sources 137/139 conflicts with this construction's
required `103/1 → 302` return. It cannot simply be applied. The row157 alternative
uses five helper rows unchanged by K219, and **does stack**. The intake's
[variant](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/variant-row157/k219-row157.tm)
changes only `157/1: 1 L 148 → 1 L 187`.

An unchanged independent checker proves the variant's all-initial-tape halting
equivalence from state 0 using 92,895 radius-five contexts and positive blocks
of at most two old/three new steps. Its immediate-halt negative control is
rejected. Independent sparse/dense startup reaches the identical complete
frame after 312,617 steps; the changed row is unused in this prefix. The
canonical alternative hash is
`d4684a6f6cc688a5d6de2b25ea43027c70f37d518e22a2cd6b9a5510191c1ef1`.
It still has 219 states, so this composition gives **no 218-state result**.
The all-tape proof transports the baseline's calibration; it does not claim
unchanged instruction durations or a new full primitive replay.

The stack script's first author-side preflight had two mistaken direction
expectations for unchanged helpers and stopped before constructing output or
running the checker. The corrected script matches the literal rows; the failed preflight remains under the variant's `history/`, and the
corrected reconstruction script is published beside the tables.
This was a tooling mistake, not a rejected 219 machine. See the
[result and exact proof scope](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/variant-row157/result.json).

## Retained theory and encoding research

The [full countermodel](140-k219-res-theory-restricted_rho8_strong_countermodel.md)
blocks a tempting simplification of the four-parameter propositional row.
Its four-valued matrix designates only value 3 and interprets falsity as 0.
It validates all five restrictions `U ∈ {F, truth, A, B, C}` simultaneously,
even with identity, ex-falso and the K combinator added, while refuting the
unrestricted row. These semantic values are not native formula-code tags.

Crucially, this is more than a logical-fragment obstruction. Over the set HC
of hereditarily countable sets, designated membership is actual membership;
colored nondesignated nonmembership makes the native subset test designated
exactly on equality of objects. An antichain encoding and uncountable coloring
fibers supply the separating nonmember. The full native seed-K bundle,
**including its support clause**, becomes countable closure under a chosen
witness function, and the resulting container remains in HC. The proof handles
coincident public labels and the actual private matrix-code freshness bound.
All other retained logical rows, MP and GEN are valid. Soundness induction
therefore lets ZFC prove consistency of this exact weakened calculus.
Assuming ZFC consistent, it cannot also have the requested ZFC-provable
consistency equivalence. Allowing junk formula codes does not avoid this
obstruction. The fresh finite checker validates matrix facts only; HC closure
and full native soundness are independently reviewed written mathematics.
Other three-parameter bases and the rho6-to-T route remain open.


The [calculus/codec findings](140-k219-res-theory-calculus_codec_findings.md)
and [experiment guide](140-k219-res-exp-README.md) also preserve the following
results. These measurements are delivered historical evidence, not newly
rerun searches:

| Family | Contribution and limit |
| --- | --- |
| Existence/G fusion | A quantified conjunction is interderivable with the two rows under the retained logic, without circular specialization. Its 72 tested implementations emit nine rather than ten AX outputs but have at least 229 subtrees and 4,826 leaves. |
| Nested fourth parameter | Pairing the fourth value into an existing AX field preserves four independent values and the axiom families, not literal AX batches. Six layouts have 211–215 subtrees; every raw compile has binding errors. |
| Three-row propositional bases | K/S/Peirce, K/transitivity/Peirce, K/S/DNE each have 3,888 tested implementations; minimum subtrees 216/214/216. Retained best candidates fail decoder binding; no smaller correct machine is obtained. |
| Binder arithmetic | The safe binder a+b+1 saves 46 leaves in four implementations but gives 210 subtrees and raw 223 states. Sixteen constructor and 120 scaled-Cantor/tag/order/shape choices reach raw 220 at best, without a verified reduction. |
| Constructor tags | Thirty-six implementations keep membership tag 1 and permute I/Q/E tags 0,2,3 consistently at all 81 constructor sites. The original is best; the nearest nonidentity 209-node source has zero run ten and fails the decoder constraint. |
| Nonlocal reassociation | Two codec families examine 127,488 and 133,257 candidates over selected closed frontiers. One 209-node/zero-run-six source remains, but its raw table fails a primitive interface. Neither family is an exhaustive grammar lower bound. |
| Protected compiler | Conservatively protecting 82 observed helper states produces a larger 232-state table passing 6,183 finite interfaces. The protection set came from finite frames, and neither result proves unbounded compiler correctness. |
| Cantor orientations | Sixteen independent argument orientations have nonidentity minimum 212 subtrees; 320 seeded reparses reach 216. The complete specialized constructor/GEN/MP changes are included; no verified improvement follows. |

The [equality discovery record](140-k219-res-enc-README.md) contains 16 finite
signature hits, including the proved seven-internal-node replacement. Its
98,869,363-composition discovery run uses finite signatures with unknown markers
for overflow or loops, rejects unknown outcomes on its finite goal grid, and
omits the cost-six layer and hence the `0+6`/`6+0`
root splits. A separate diagnostic tests 1,750 pairs per hit, including all
counter pairs through 40, selected larger values through 10,000 and nonzero
unrelated registers. These are discovery diagnostics, not a global optimum
or the all-natural proof. The accepted source uses that separate written proof.

Rejected shortcuts remain explicit: residual scratch values break the axiom
guards; a naive right-child decrement fixes the positive guard but fails zero;
a spare-zero increment repair can pass generalized interfaces yet fail blank
initialization. The final construction clears both scratch counters, handles
both guards and preserves spare one. Unchanged decoder roles can also serve
arithmetic; source binding alone never licenses overwriting their helper rows.

## Attribution and further work

The new equality routine, source proof, compiler repairs and HC/codec research
are Source 140's contributions; its [attribution](140-k219-ATTRIBUTION.md)
records ChatGPT-assisted development and predecessor licensing. The exact K220
parent retains its recursive credits, including Elliot Glazer's K calculus,
Mira, Jeff's development, Andrew James Wade, BusyCoq, the Coq Library of
Undecidability and ProveIt's preceding reductions. The row157 composition is
an intake finding using the earlier alternative's unchanged checker. No new
priority or relicensing is asserted.

The useful new search direction is sharing an open fragment under two proved
continuation contracts, combined with direct repairs of affected primitive
returns. Searching only closed fragments would miss this example. The source
proof and complete binary runtime remain separate acceptance conditions.
Simpler artificial calculi are still in scope, but their sole-falsity
consistency must be calibrated; a smaller raw compiler count does not replace
that obligation. Further reduction below 219 remains open.
