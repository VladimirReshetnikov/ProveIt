# Intake 185: a 220-state construction and three equivalent alternatives

Placement `de06ba50be` imports two packages as **Sources 138–139** and retires
their committed ZIPs. Both contain useful new material. The host now has
**139 sources** and the collection remains **290 reports**. This reconciliation
also follows completion of [batch 184](intake-184.md), whose Source 137 had
already been placed in `abae578c29`.

| Source | Delivered archive | Arrival | Reviewed snapshot |
| --- | --- | --- | --- |
| 138 | `K220_Construction_2026-10-20.zip` | `7677a1f62fde5f1abf698f7e2d81596ebe7a570c` | `c011e44bc2df6238940bb600833730873b308334`, Source 132's exact K221 delivery |
| 139 | `K220_Alternatives_2026-10-20.zip` | `bf01dd349a0e2a4cef109cb911ce228c81639aa9` | `a27b5391bbf3cfdc7d06cc7acb135f4930a03101`, containing Source 138's delivery |

The [placement map](data/intake185-placement.json) accounts for **175 members**:
150 new ancillary files (11 root, 37 code, 102 data), seven existing aliases,
six within-batch aliases, two vendored-ZIP history aliases and ten archive-only
manuscript/PDF/delivery files. Existing aliases were checked in their original
placement trees as well as the current tree. Fresh extraction and index checks
confirm the new payload under existing Git attributes. No supplied checksum
manifest was validated. Nothing is discarded merely because its machine count
or proof-status sentence has become historical.

## Source 138: why the new decoder change saves a state

The [published machine](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k220/README.md)
has 220 working states, 440 rows, binary alphabet, a two-way infinite single
tape and L/R moves. Canonical start/dispatcher/halt labels are 0/22/220;
native labels are 0/84/254. Canonical SHA-256 is
`f80c57e800d4f999d9b4902a8e96bd36d1b6180b3ad322ca8ed0ab67b47f2a5f`.
Graph reachability of all working states does not assert that the blank run
visits every state.

Source 132's 221 is the exact predecessor. The change re-encodes a decoder
role whose existing `132/1` row is **not** a plain right-moving decoder edge.
The earlier intake's rotation search excluded that case. At source prefix
`11101001001101`, four closed blocks A/B/C/D have sizes 52/27/52/243 and
cover ordinals 274–647. Two rotations change
`((A,B),(C,D)) → (A,(B,(C,D))) → (A,((B,C),D))`.
No primitive instruction is deleted or reordered. Two independently
implemented guarded-successor resolvers confirm the same complete control-flow
graph, not just the same leaf word.

After rotation, state 202 and state 171 have the same read-1 action, but
read-0 successors 90 and 183. At valid source entries the preceding bit is
respectively 0 or 1. The shared row `171/0: 0 L 7` inspects that bit using
existing helper 7; routes through 86 or 205 restore the old tape/head and
reach the appropriate successor in three literal transitions. State 202
is removed. The five retained-row changes from the parent are:

| Native row | Parent | Final |
| --- | --- | --- |
| 132/0 | 0 R 147 | 0 R 171 |
| 132/1 | 1 L 163 | 1 R 201 |
| 171/0 | 0 R 183 | 0 L 7 |
| 203/0 | 0 R 132 | 0 R 147 |
| 203/1 | 1 R 202 | 1 R 132 |

This particular fold theorem is **restricted to valid source-decoder entries**.
Arithmetic also uses state 171, so it is essential to check the complete final
runtime. The source still has 208 distinct subtrees, 23 primitive types,
4,744 leaf occurrences, depth 38 and maximum zero run six. Its binary-state
accounting is 49 nondecoder states + 185 interior roles − 14 shared roles = 220.
A source-DAG count is not a binary-state count.

## Fresh checks and the consistency claim

Thirteen selected substantive jobs ran on disposable copies. All passed, and
rebuilt native, canonical and source files agree exactly with the deliveries.
The [fresh construction record](data/intake185-fresh-construction/actual.json)
and [fresh alternatives record](data/intake185-fresh-alternatives/actual.json)
retain commands, output paths, elapsed times, exit status and logs separately
from the authors' historical receipts.

| Check | Fresh result |
| --- | --- |
| Deterministic construction | Exact table/source; parent word and guarded CFG preserved |
| Canonicalization and full blank startup | 409,835 steps; exact complete tape and head |
| Complete final symbolic runtime | 6,167 cases, 1,516,421 symbolic rules, all 440 rows, minimum duration 13 |
| Independent runtime audit | Exact coverage, four unary/list schemas, source/CFG, contextual fold and startup |
| Three alternative constructions | Exact native and canonical table bytes |
| Positive macro equivalences | Both individual row changes and their composition pass |
| Three independent window checks | Each passes from unrestricted state 0 |
| Three canonical/startup checks | Each has the same exact 409,835-step blank startup |
| Independent alternative core audit | Baseline and all three variants pass |

The runtime certificate quantifies over arbitrary natural register values,
header gap, first spare value and finite spare tail, with symbolic induction
for unary runs and repeated list blocks. The 6,167 cases enumerate finite
control/guard cases, not bounded numerical samples. Initialization reaches
native state 84, head −5, logical registers `[3,0,0,0,3,0,0,0,0]`, physical
registers `[0,0,0,3,0,0,3,0,0]`, header 176, gap 117 and 167 value-one spares.
All 351 one-cells and the zero exterior are checked.

The K calculus and proof enumeration are unchanged. Source/CFG identity,
positive runtime simulation and exact startup transport the predecessor's
ordinary consistency calibration: blank nonhalting iff Con(ZFC), by an
argument formalizable in ZFC. This intake does **not** establish that equivalence
inside PA and supplies no exact-220 Lean kernel endpoint. The completed
[240-state PA theorem](../../../../../../Computability/BusyBeaver/Research/ZFC/rotation240_binary.md)
and the [221-state predecessor's formal status](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/README.md)
remain distinct. No proof-assistant command was run here. Recursive ancestor
replays, exhaustive research searches, delivered manifest validation and the
exploratory variants' missing proofs were not rerun or silently inferred.

## Source 139: composable continuations, still 220 states

The three alternatives change native `103/1` from `0 L 162` to `0 L 142`,
native `157/1` from `1 L 148` to `1 L 187`, or both. These reproduce Source
137's continuation ideas on the new 220 baseline, with fresh invariants and
checks. Their canonical tables are pairwise distinct, so these are actual
layout alternatives rather than renamings:

| Table | Canonical SHA-256 |
| --- | --- |
| row103 | `df5412edbdb22a53dc40f21d55c12c911c167c96d586962c54f3b3c7987fcc4a` |
| row157 | `93b6917ebf20d7290c7785cc0a4e0ba0939dc60ec12e5edce0fecacf269b7d5f` |
| both | `7114373310dde3d1447a73b6e1a40bbdfb2c8c3c138a3631a4bd2a132c66daa9` |

The state-103 proof uses the old invariant that the left neighbor is 1.
At state 157 it splits on that neighbor: the 0 branch joins after two steps
each; the 1 branch joins after one old and three new steps. Positive bounded
blocks preserve state, head and the entire tape. The independent radius-five
window check covers 91,337 contexts, with 96/320/416 nontrivial comparisons
for the three variants. It starts from all windows in state 0 and verifies
inductiveness; the exterior is arbitrary. Thus the claimed equivalence is
from state 0 on any tape and at any head position, not from arbitrary states.
The combined change is checked jointly; individual neutrality never licenses
an unchecked combination.

These rewrites stack with the 220 construction, but consume no fewer states.
They provide alternate continuation layouts for later searches. No 219-state
result follows from this package.

## Further questions and research

The ancillary theory and encoding investigations are retained below with their
exact scopes. The submitted main reports remain recoverable from the arrival
archives; the delivered supplementary proof notes and research code remain
unchanged. No standalone logical-basis countermodel is promoted to a model
of the entire K theory, and no finite search failure is treated as a lower bound.

### Exploratory 220-state layouts from Source 139

Three further tables are expressly excluded from the certified core:

- **Occurrence row160:** `160/0` becomes `0 R 187`, redistributing 81 physical
  source bindings while preserving the source. Historical checks cover 6,167
  basic finite cases, 6,162 admitted guards at three patterns, and a 410,123-step
  startup. A candidate-specific unbounded runtime or all-tape proof is missing.
- **Six-leaf zero NOP:** inserts six leaves, giving 4,750 occurrences and changed
  source control flow. Historical checks cover 6,164 admitted guards at three
  patterns and a 409,835-step startup. Its retained stuttering receipt binds
  the preceding source `9e5759…`, while the final source is `2b9932…`. The
  final closure receipt does not repair that mismatch. An exact final-source
  stuttering proof and unbounded binary runtime remain required.
- **NOP plus row160:** combines those changes and records 6,175 basic finite
  cases. No combined admitted-domain proof, exact startup or unbounded runtime
  is supplied. The two changes cannot inherit each other's evidence unchecked.

The [exploratory README](139-k220a-exp-README.md) retains these limitations.
Literal table reconstruction checks patch bytes only. Historical workspace
paths and unbundled discovery trees are not promised reproduction dependencies.
None of these three specimens is an additional certified consistency machine.

### Theory investigations from Source 138

The final 220 changes no logical theory. The independent theory work is
preserved in the [assessment](138-k220-res-theory-final_formalism_assessment.md),
[theory findings](138-k220-res-theory-theory_findings.md),
[membership/quantifier findings](138-k220-res-theory-membership_quantifier_fusion_findings.md)
and [rotation review](138-k220-res-theory-weak_rotation_review.md).
Native code 0 denotes truth and code 1 is the designated false atom R(0,0);
Boolean-algebra bottom/top in the countermodels are semantic values, not
those native integers. Binder labels and formula codes are coupled by the
actual encoding; a private binder must be chosen after matrix translation.

| Investigation | Result and scope |
| --- | --- |
| General equality helper G with binder κ(a,b) | The ungated G family is equivalent to the earlier equality row plus helper under the retained logic. Calibration needs off-diagonal freshness only. This uniform theorem was already in the predecessor and receives no new priority claim. |
| Implication-code binder instead of membership-code binder | Safely removes one increment but increases the measured source from 208 to 209 subtrees and the experimental binary allocation from 221 to 223; no final runtime proof. Fewer instructions need not mean fewer states. |
| Delete rho1 (equality existence) | A label-dependent many-sorted model validates the remaining exact native calculus, including the K bundle, while falsity stays false. ZFC constructs this model; the proposed deletion loses the required calibration. It is not represented as one ordinary one-sorted membership structure. |
| Replace rho6 by universal specialization T | A two-time, growing-membership model over an ordinary K+IR model refutes recovery of raw rho6. This is a relative full-theory countermodel to theorem equivalence; equiconsistency of the modified theory remains open. A finite machine screen does not settle it. |
| Fuse distribution and commutation | A four-element Boolean algebra validates the proposed logical basis but refutes raw distribution. The algebra does not satisfy K, so it gives no full-K consistency obstruction. Composite quantifiers become normal; interpreting the exact K template remains open. |
| Gate the G pivot and reuse it as binder | A modal countermodel refutes the opaque-core logical equivalence. It is not a K model and does not exclude a K-specific interpretation. |
| Membership/congruence fusion | A fused congruence row with a canonical binder recovers exactly congruence plus canonical vacuity, not full fresh vacuity. A four-parameter version with an independent pivot does recover full vacuity; its compiled cost was not measured. |
| Restrict membership vacuity to canonical/constructor/own-code binders | The retained countermodels refute the proposed purely logical replacements, not every possible K-specific equiconsistency proof. |
| Drop the K support clause | The natural numbers with membership interpreted as inequality satisfy the whole support-deleted ordinary schema. The proof uses finite-support automorphisms for arbitrary formulas. This exact deletion loses the intended consistency strength. |

A valid rescheduling moves left membership substitutivity into the existing
`c ≠ a,b` gate. The missing `c=a` case is propositional; the `c=b` case follows
using the other substitutivity direction and equality symmetry. With vacuity
retained separately, its quantified version M5 is interderivable by the usual
helper elimination. Thirty concrete layouts retained the stack interface and
passed direct word/AST and both CFG comparisons, but the best repaired source
had 212 subtrees, 4,790 leaves and zero run seven. Every attempted incremental
native compilation rejected its decoder binding. These are rejected layout
experiments, not verified binary machines.

The weaker reassociation lemma permits `(A,(B,C)) ↔ ((A,B),C)` when A has no
escaping break and C has no escaping continue. B is unrestricted; A's continues,
C's breaks and halts need not be forbidden. This enlarges the source search
beyond fully closed rotations. It does not dispense with exact decoder or
runtime checks. The winning 220 rotations satisfy the stronger closed condition.

### Encoding experiments from Source 138

The [encoding report](code/138-k220-res-enc-encoding_report.tex) and its
[README](138-k220-res-enc-README.md) preserve the finite search families,
allocator dependencies, logs and concrete rejected machines. These experiments
use the parent K221 table, not the accepted K220 allocation. They include
single/double state folds, non-pure and displaced folds, commuting blocks,
coordinated helper rewrites, schema parameter permutations, row order and
alternative reads of the fourth parameter. Their negative results apply only
to their stated finite proposals and bounds.

Two failed deletions are especially useful:

- Removing reset/scanner state 50 confuses a transient extra zero with the
  intended boundary. The retained decrement case at ordinal 40 returns to
  the wrong source position: 662 steps versus the baseline's 586.
- Deleting state 198 with the proposed `66/0` patch fails even on the blank
  tape. After 76 steps it enters state 35 to the right of every one-cell and
  writes ones forever while moving right. A value-one-spare invariant alone
  does not validate this deletion.

The joint eight-row parameter sweep bottoms out at 208 source subtrees in
exactly two layouts; the alternate rho6 parameter order still compiles to 221.
The tested 12 fourth-read variants reach no fewer than 209 subtrees, and the
fixed closed-atom row-order family has the original 208 as its unique optimum.
The rho3/rho5-swapped joint family bottoms out at 217 subtrees. The `super66`
experiment records 884 tests over 224 cases without a result; two disjoint-register
commutations preserve 208 subtrees and zero run six. Register coalescing was
not completed. The all-one-spare invariant is a source-boundary invariant,
not a statement that particular rows are unused on the blank run.
These are source-layout objectives and restricted search results, not a proof
that 220 binary states are necessary. Their discovery scripts and historical
receipts were retained, not rerun during this intake.

## Attribution and continuing search

The submitted constructions retain their credits to Elliot Glazer's K230
calculus and development (`3142e4dd980f0be12f4abb636c4ae2528afc17eb`), Mira,
Jeff's busy-beaver development, Andrew James Wade, BusyCoq, the Coq Library of
Undecidability and ProveIt's earlier reductions. See Source 138's
[attribution](138-k220-ATTRIBUTION.md), Source 139's [notice](139-k220a-NOTICE.md)
and [recovery/replay instructions](intake-185-reproduction.md). All inherited
licenses remain with their material; this intake asserts no relicensing.

The concrete lesson is that source equivalence and decoder allocation need
separate searches: non-pure re-encoding exposes a valid fold that an earlier
19,041-table pure-edge rotation search excluded. The three neutral layouts
provide additional starting points, and seed-relative specialization from
Source 137 supplies another route with its own invariants. None of these
observations alone establishes a sub-220 machine. Any proposed junk-code
formalism still needs both consistency directions to an accepted benchmark,
plus a complete compiled machine, initialization and unbounded simulation.
