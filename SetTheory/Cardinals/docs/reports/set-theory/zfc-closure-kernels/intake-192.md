# Batch 192: the primary 217-state construction

Source 152, from `8a1796545e`, is accepted as the new
[**primary 217-state machine**](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/README.md).
All five selected fresh checks passed. Its ordinary mathematical proof gives,
formalizably in ZFC, `¬Halt(M,blank) ↔ Con(ZFC)`. The exact table has no newly
compiled Lean or internal PA endpoint. The active minimization target is now
**216 working states or fewer**.

## Intake and provenance

`K217_Dominated_Continuation_2026-10-20.zip` arrived in commit `8a1796545e`.
The submission's inspected repository pin is
`704b87442afbd571833a628cd558f1d207fd8b2f`. Its immediate parent is precisely
Source 149's dominated-rho8 218 archive, delivered at `7071e5041e` and
reviewed in [batch 191](intake-191.md). It is not a single-row patch of the
former primary K218 source.

Placement **`bf087d590f`** accounts for all **39 members**: 26 new files
(three root records, four code files and 19 data files), three existing
aliases, one exact historical parent-archive alias and nine archive-only
article/input/PDF/delivery members. Maximum Windows-prefixed placed path
length is 123. The [placement map](data/intake192-placement.json) identifies
each original and alias introduction. The ZIP is retired; the full original
layout remains recoverable. The host now has **152 sources**, while the
collection remains **290 reports**. The two research archives at `1e87618cf2`
remain separately queued for batch 193.

The complete main article, included proof sections and literal table received
two independent ordinary reviews, together with the new executable closure.
No mathematical retraction was needed before placement. The inherited source
and runtime utilities have the exact previously reviewed identities. The
submission's proof-search ancestry, Mira, Elliot Glazer's compact K theory,
Jeff's reference work, ProveIt and Andrew James Wade's compiler ancestry retain
their stated attribution and license scopes in the candidate publication.
No discovery-priority claim is made.

These notes reconcile the report without modifying delivered bytes or the
host article. No checksum-manifest suite, line-ending work, recursive ancestor
verification, omnibus wrapper, Lean or Rocq ran during this intake.

## How the state is saved

In the parent, native states 69 and 400 agree on scanned one, `1R31`, but
their zero branches lead to 105 and 104 respectively. Their only incoming
edges write opposite marker bits immediately behind the head:
`53/1 = 1R69` and `224/0 = 0R400`. The missing ingredient is an existing
decoder whose two children can select the two zero continuations.

Three closed source rotations expose that decoder at native 213:

| Rotation | Parent / child | Closed factor lengths |
| --- | --- | --- |
| `((A,B),C) → (A,(B,C))` | 210 / 188 | 27, 53, 374 |
| `((A,(B,C)),E) → (A,((B,C),E))` | 213 / 210 | 27, 427, 3,682 |
| `(D,(A,((B,C),E))) → ((D,A),((B,C),E))` | 201 / 213 | 14, 27, 4,109 |

All factors are closed and halt-free; this condition does not assert that they
terminate. Each participating state has one source role, and each rotated
child has a unique physical incoming edge. The constructor and an independent
reader check the **expected complete decoder bindings** after every rotation.
They also preserve all 4,751 operation/operand occurrences and the entire
guarded ordinal control graph. Thus equal ordinal/register configurations
remain related for arbitrary natural values, including divergent runs.

The final source retains **203 distinct subtrees, depth 45 and zero-run 6**;
94 source addresses change. The rotated table has
`213/0 = 0R92`, `213/1 = 1R90`, with `92/0 = 0R104` and `90/0 = 0R105`.
Redirecting 400's incoming edge to 69 and setting `69/0 = 0L213` gives:

| Origin marker behind head | Candidate zero-read route | Old endpoint |
| --- | --- | --- |
| 0 | 69 → 213 → 92 → 104 | 400's zero branch |
| 1 | 69 → 213 → 90 → 105 | 69's zero branch |

Both routes take exactly three steps, preserve both inspected cells, and
finish one cell right. The one branch is unchanged and takes one step. Every
other cell remains untouched. Starting in state 0 on any initial tape, the
unique incoming edges establish the marker invariant on every visit. Positive
blocks of length one or three give halting equivalence in both directions.
An arbitrary initial configuration inside the merged pair is not covered by
that invariant and is not needed.

Deleting 400 leaves **217 working states and 434 rows**, with no new state.
Relative to the dominated parent, nine retained rows change: 69/0, 188/0,
188/1, 201/0, 201/1, 210/1, 213/0, 213/1 and 224/0. The compact table uses
working labels 0–216 and halt 217. The halt has no outgoing rows and is not
counted. Initialization is included, with one binary two-way-infinite tape,
blank zero, initial state/head 0 and only L/R moves.

## Calibration and the complete machine proof

The axiom calculus is unchanged from Source 149. That source restricts rho8's
fourth field to `U≤A` and proves exact equality of native theorem sets with the
unrestricted calculus. Its 3,728-node derived-schema certificate, two independent
readers, common-input AX compiler and cofinal enumeration proof were already
freshly checked and reviewed in batch 191. Those results are inherited here,
rather than falsely counted as additional fresh executions. The numeric zero
alias and the private-code-coupled bundle remain covered by that calibration.

The final K217 runtime is checked separately on its exact bytes. At every
primitive entry the nine registers are independent naturals, the gap is
arbitrary, and the spare list is any nonempty finite list of naturals. Zero
and positive decrement guards exhaust the domain. Four exact-table unary
block schemas, list induction and literal transitions derive complete tape
endpoints, correct halt behavior and finite positive durations. A bound of
4,000 symbolic rules limits proof construction; it does not bound represented
registers, tape lengths or machine time.

Complete blank startup supplies the base of that simulation. The fresh
native sparse, independent dense and canonical dense calculations agree on
the entire expected tape after 312,617 transitions. The formula-bearing
registers and work stack are zero; the nonzero counters 3 are permitted by
the inherited clean-root/cofinal theorem. The later source execution therefore
halts exactly when the calibrated calculus has a finite refutation.

Composing these ordinary arguments proves the displayed equivalence in ZFC.
No consistency assumption is needed to prove the equivalence itself. It does
not prove unconditional nonhalting or minimality. The executable symbolic
checker and its mathematical induction rules remain part of the verification
basis; this is distinct from a proof-assistant kernel result.

## Fresh verification

| Selected job | Result |
| --- | --- |
| Deterministic reconstruction | Exact native/compact/source/unfolded bytes; three rotations and nine-row delta |
| Independently written source/fold audit | Whole instruction word/CFG and expected bindings; four marker/read cases |
| Independent complete startup and relabeling | Sparse/dense/native/canonical agreement on the entire frame |
| Independent all-tape fold checker | 962,479 invariant contexts; 256 nontrivial; positive 1/3-step blocks; corrupt initial halt rejected |
| Pinned symbolic runtime and startup | All 6,176 cases; 1,616,558 rules; all 434 rows; minimum duration constant 13 |

The full runtime took **158.764 seconds**. Every fresh ordered case object
agrees with the delivery; the aggregate runtime differs only in elapsed time.
The [actual process record](data/intake192-fresh/actual.json) and
[independent record audit](data/intake192-fresh/actual-review.json) retain
exit status, timeouts, raw logs and exact bindings. Construction/source/blank
jobs had 60-second caps, the local fold 90, and runtime 300.

| Complete startup property | Value |
| --- | --- |
| Transitions | 312,617 |
| Native / canonical dispatcher | 84 / 83 |
| Head / header / extra gap | −5 / 139 / 80 |
| Logical registers | `[3,0,0,0,3,0,0,0,0]` |
| Spares | 130 entries, each 1 |
| Complete nonzero support | 277 cells |
| Visited interval | [−15,553] |

The runtime leaf freshly generated a 312,617-event startup trace. The separate
blank audit independently recomputed the transitions and full tape, without
reading that stored trace; its `trace_rows_independently_replayed` is correctly
zero. This differs from the delivery's historical stored-trace comparison.
The fresh complete supports agree. [Reproduction](intake-192-reproduction.md)
preserves this boundary and avoids the delivered wrapper's manifest and parent
verification calls.

## Comparison and the next target

During the Source 149 follow-up, an independent closed-span reassociation
search found the same source before comparing it with this delivery. Its
candidate025 source is byte-identical. Its 217-state transition graph equals
the submitted table under the three-cycle `188→213→210→188`, with all other
states fixed. Expected decoder bindings, the local marker proof and full blank
frame also check independently. This corroborates the construction; it is
the same saving and cannot be counted twice. The
[separate reconstruction record](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/research/independent-helper-reconstruction/README.md)
preserves that derivation without duplicating the full runtime.

The earlier primary/contextual K218 folds share different source roles and
do not simply stack with this construction. The [omitted-MP-push composition](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k217/research/omit-zero-fold-search/README.md)
shortens the new source to 4,732 leaves while preserving its complete startup
trace, but does not itself delete a state. Its source/compiler transfer is
reviewed; a new full primitive runtime has not been claimed. Two bounded
fold searches, one on each 217-state layout, tested 1,292,544 specifications
with no survivor. These search bounds are not a minimality theorem. The
accepted result of this intake is K217; the active target remains **216 or
fewer**, with ordinary ZFC calibration and complete initialization required.
