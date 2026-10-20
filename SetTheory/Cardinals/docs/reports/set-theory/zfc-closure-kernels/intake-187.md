# Batch 187: alternative 219s and research toward 218

This reconciliation adds **Sources 141–143** to the 140-source host. It retains
three different 219-state constructions, two mathematical routes for modifying
the seed calculus, new equality implementations, and precisely scoped failed
encoding searches. **No verified machine with 218 states or fewer results.**
The accepted [K219](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/README.md)
remains the size benchmark. These are intake findings; the delivered files
remain unchanged.

## Provenance, placement and scope

| Source | Arrival and archive | Contribution and reviewed snapshot |
| --- | --- | --- |
| 141 | `ffcdff81ad34643b314552c807ec437b906740f0`, `K219_Alternatives_2026-10-20.zip` | Zero-terminal and retagged alternatives, their composition, source proofs and complete binary certificates. Explicit parent pin `26d5de6d21fa354d50e0b84fe851c289925b8d72`. |
| 142 | `0b0cec2d0d70fb340521deecd4dbd80468b56cf5`, `research218_progress_latex.zip` | Cofinal-bundle countermodel, core-only tail lemma, capture obstructions, shared-cancellation equality and partial dominated propositional basis. No reviewed Git commit is stated; supplied input-byte and mathematical-source pins are retained. |
| 143 | Same arrival, `research218_encoding_supplement_latex.zip` | Complete baseline return contracts, concrete failed cooperative edits, unresolved cases, Direct09/Direct13 source proofs and partial pilots. No reviewed Git commit is stated; exact baseline and source-input pins are retained. |

Placement **`99fbf38bbd`** accounts for all **274 members**: 218 new payloads,
14 existing aliases, 28 batch aliases, one historical parent-archive alias and
13 archive-only manuscripts, article inputs, PDFs or delivery READMEs. It
retired all three incoming ZIPs in the same commit. The exhaustive
[map](data/intake187-placement.json) records original names, flattened targets,
alias introduction trees and archive-only reasons. New material has prefixes
`141-alt219-`, `142-toward218-` and `143-enc218-`. Code, data and audit files are
placed according to the intake procedure; main manuscripts remain recoverable
from their committed arrivals. The longest new path with `C:\ProveIt\` prepended
is 147 characters. The host has **143 sources** and the collection still has
**290 reports**.

The [recovery and replay instructions](intake-187-reproduction.md) restore the
original layouts, including article inputs and predecessor archives. Scripts
and receipts still naming delivered directories are archival originals, not
commands to run from their flattened locations. Sources 142/143 identify some
upstream review notes by hash without supplying those notes; their included
manuscripts contain the essential arguments. Those omitted files have not
been treated as supplied or compiled.

This is a reconciliation note, following the existing-host option of intake
section 2; the host article and its labels are unchanged. The reports concern
this host's existing finite-refutation and encoding questions. Their baseline
is the current accepted source/table, not an obsolete machine mistakenly
reintroduced as new. No existing correctness claim required retraction.
Source 141's [NOTICE](141-alt219-NOTICE.md) credits ChatGPT-assisted development
for Vladimir Reshetnikov's ProveIt project under the inherited licence. The
unchanged predecessor archive preserves its complete attribution chain,
including Elliot Glazer, Mira, Jeff, Andrew James Wade and the formal-library
contributors. Sources 142/143 are credited as the progress companion and
encoding supplement; no individual author absent from those documents is
invented. The intake's new stacks and comparisons are identified below.

## Three alternative source/table pairs

Let `D_i`, `I_i`, `B_j`, `C_j` mean decrement, increment, break and continue.
Pair parentheses refer to the source language's control semantics, not
ordinary sequential composition. With `P=(D_6,C_2)`, the open fragments
`U=(P,B_1)` and `V=(P,D_6)` have identical contracts for **every natural R6**:
on a positive input each decrements it and emits continue1; on zero each
leaves zero and emits break1. They terminate and preserve all other registers.
This is a valid contextual replacement without a source reachability premise.
It does not identify an arbitrary `B_1` with `D_6`.

Replacing both U occurrences in each of four equality macros changes eight
primitive ordinals. Each changed leaf has exactly one incoming edge, the zero
guard of the unchanged D6 two ordinals earlier, in both source backgrounds.
This gives a second, whole-source justification. The physical runtime still
checks the added positive guards; it does not discard them as unreachable.

The independent retagging changes 81 copies of
`(((I_1,I_1),(I_1,I_1)),C_2)` to
`((I_1,I_1),((I_1,I_1),C_3))`.
Both add four to R1 and emit continue1. The increased continue level compensates
for crossing two right edges. All 405 moved leaf addresses and all ordered
ordinal control-flow successors, including both decrement guards, were checked.
Keeping the old continue level after rotation would be wrong.

These **source** transformations commute, but their selected physical patches
do not simply combine by union. In normalized native labels, zero-terminal
changes nine rows, retagging three, and composition twelve. The standalone
retagged row `139/0` is `0 R 99`; the composed row must instead be `0 L 139`.
The supplied native labels 102/120 correspond to accepted native 301/302.
Canonical and normalized native labels must not be mixed in comparisons.

| Layout | Distinct source subtrees / leaves | Working states | Full guarded cases | Complete blank startup steps |
| --- | --- | --- | --- | --- |
| Zero-terminal | 206 / 4,744 | 219 | 6,175 | 313,845 |
| Retagged | 206 / 4,744 | 219 | 6,167 | 312,707 |
| Composed | 206 / 4,744 | 219 | 6,175 | 314,043 |

All have 183 internal subtree types, depth 38 and 438 transition rows.
Their complete startup frames agree with K219: head −5, header 139, gap 80,
logical registers `[3,0,0,0,3,0,0,0,0]`, 130 value-one spares, exactly 277
one-cells and zeros elsewhere. The native start/dispatcher/halt labels are
0/84/254; canonical halt is the separate label 219.

All **14 selected fresh jobs pass**, including three full runtimes with
1,518,671 / 1,514,311 / 1,518,914 symbolic rules respectively, complete
source/patch transport, startup, independent audit and ten negative controls.
All 438 rows occur in each runtime. Case arrays, source/startup records and
canonical tables reproduce the delivered bytes; runtime records differ only
in elapsed time. The [actual execution record](data/intake187-fresh-alternatives/actual.json)
and [review](data/intake187-fresh-alternatives/review.json) preserve their exact
scope. The source-level proofs also received an
[independent mathematical review](intake187-source141-review.md).

The [unpacked alternative publication](../../../../../../Computability/BusyBeaver/Research/ZFC/candidate-k219/alternatives/README.md)
contains the exact tables and comparison evidence. Fresh verification and the
ordinary source proof are separate: the universal runtime quantifies all
natural register/gap values, the first spare and an arbitrary finite spare
tail; finite syntax checks alone do not prove these contracts. Its symbolic
proof-construction cap is not a bound on represented inputs or machine time.
It must establish positive duration, whole-tape endpoints and no early halt.
Ancestor calibration is reused, not recursively replayed. Exact-table Lean and
internal PA endpoints remain open; the earlier separately recorded K221 formal
endpoint is unchanged. No unconditional nonhalting or consistency is asserted.

## Combinations tested during intake

The earlier row157 rewrite changes only `157/1: 1 L 148 → 1 L 187`.
All three alternatives preserve its five required helper rows. If the bit
one cell left is zero, both routes meet at state186 in two steps; if it is
one, the old one-step and new three-step routes meet at state148 with the
same head and whole tape. Every block is positive. Thus it preserves halting
on every initial binary tape, without a source-entry assumption.

The intake constructed all three stacks and also ran the unchanged independent
joint-diagram checker with freshly computed radius-seven domains and fuel97.
All pass, each with 1,664 nontrivial contexts and maximum old/new blocks2/3;
the domains contain 1,019,753 / 1,019,279 / 1,029,097 contexts respectively.
Each immediate-halt negative control is rejected. These are **three additional
219-state layouts**, not a saving or a fresh full primitive replay. The earlier
row103 alternative still conflicts with the required generalized return.

A new [shifted-head search](../../../../../../Computability/BusyBeaver/Research/ZFC/k219-shifted-fold/README.md)
tests folds relating a dropped state's old head to the kept state's head two
cells away, in either direction. Incoming rows can sometimes absorb this shift
by reversing their move. This is distinct from the reports' equal-head folds.
Across all six original/row157 layouts, the inherited-action family completed
**1,031,840 candidates over 247,506 pair-shifts**, with no survivor and no
partial pair. Full rejection streams and independent census checks are retained.
This excludes only passes of that bounded discovery filter; it is not a
semantic refutation of every candidate or a state-count lower bound. The
independent positive checker has synthetic folds of both signs and rejects
incorrect incoming-direction and premature-halt controls.

## Source 142: what the theory results permit

The **whole-bundle tail proposal** retains unrestricted propositional rho8 but
emits the seed-plus-membership-vacuity bundle only at actual matrix/private
codes `c ≥ 4P(a,b)+1`. Its full countermodel validates even every `c>max(a,b)`.
The domain is the set HC of hereditarily countable sets; membership is
assignment-dependent via the first occurrence indices of its endpoint values.
Tagged countable payload containers and infinitely many disjoint markers
force the high-private-label subset test to act as equality.

The proof defines truth uniformly on all raw natural codes, including the
exceptional truth code `0=I(0,0)`. It handles coincident labels, literal nested
rebinding, request and predecessor support, and the container case that can
otherwise invalidate the closure argument. A countable closure under selected
witnesses remains in HC. ZFC can therefore prove consistency of this exact
weakened calculus. Assuming ZFC consistent, it cannot also prove the desired
lower consistency calibration. This is an ordinary proof reviewed at intake,
not an executed Lean proof or a negative theorem for every cofinal encoding.
It is distinct from the repository's fixed-membership-rho8 obstruction.

The **core-only tail lemma** instead keeps all logical rows and **every fresh
membership-vacuity instance**, and restricts only seed cores. At the fixed
public roles `(1,3)`, iterated double negation pads an equality-interpreted
matrix until its actual code exceeds any fixed cutoff and is fresh for its
syntax. The existing named-seed comparison then recovers the required
finite-refutation strength, with full vacuity reconstructing the bundle.
For an effective bound, totality in the metatheory is an explicit sufficient
hypothesis. An arbitrary noncomputable cutoff function is not an enumeration.
This result cannot justify dropping vacuity or weakening the classical logic
used in the padding and context-transport proof. Its arithmetic gate identity
does not yet imply a smaller program.

The two collided-core calculations are retained as interpretation obstructions:
`a=c=0,b=1` fails in an ordinary irreflexive structure with an empty object
because request and support conflict; `b=c=0,a=1` fails by diagonal
irreflexivity. They rule out those literal ungated cores in the specified
interpretation, not every alternative interpretation.

The different **dominated row `U≤A`** has checked I, K and Peirce fragments at
roots140/160/349, with 16/21/24 ancestral nodes. Its universally numeric
subfamilies include U=0, U=A and A=I(D,U); it is not one of the fixed-membership
restrictions ruled out elsewhere. Fresh checks verify leaf substitutions and
the eight-step LR-to-Peirce extension. The B and S text replays still assume
unproved `cd59`; S also uses conditional B. Their 1,093/2,530 calls and
379/878 admissible-row instances do not prove cd59, a full classical basis,
seed calibration or a state saving. Six finite checking jobs were freshly run
and passed; the last two retain those assumptions explicitly. See the
[mathematical review](intake187-source142-review.md) and
[execution receipt](data/intake187-source142-finite-replay.json).

## Source 142: shared cancellation and its binary boundary

Write `P=(D6,C2)`, `V=(P,I6)`, `A*=(D5,V)`, `U=(P,B1)`,
`R*=(A*,U)`, `T=(D6,R*)`, `E*=(A*,T)`. The cancellation A* leaves `(0,b−a)`
if a≤b and `(a−b−1,1)` if a>b. Thus its second register is zero exactly on
equality. In R*, repetition strictly decreases the counter sum and ends in
break1 at `(0,0)`. E* skips cleanup exactly on equality. This proves its
complete all-natural equality contract, preserving all other registers.

Four substitutions give 206 subtrees, 4,752 leaves, 6,179 guards and no
right-child decrements. This reuses cancellation itself for cleanup, a distinct
idea even though it does not improve the subtree count. Its raw binary graph
has 220 states and remains **NOT_PROVED**: the first symbolic right-child CI6
obligation stops on a possibly-empty run. No concrete behavior refutation of
that table follows. Its 872-action repair screen leaves 173 capped cases,
697 assertion stops and two missing-state stops. These are not the supplement's
different cooperative family or its 837/35 result.

A separate baseline invariant uses singleton values0…7 and even/odd tails to
prove R6=0 at ordinal4598. It accounts for 6,161 enabled nonhalting edges and
five infeasible guards. The halt annotation is nonbottom: it is not a
nonhalting proof. Its source-specific annotation cannot silently transfer to a
changed equality program.

## Source 143: exact return contracts and useful failures

The accepted return state302, normalized120, erases a run and enters state4.
Its only external callers are `103/1` and `113/0`; `119/1` also enters103
arithmetically. The delivered full baseline replay captures 1,432 frames:
1,419 ordinary113 cases, four exceptional right-child zero decrements and
nine103 cases. A vanished source subtree does not free a physical helper that
also has arithmetic duties. This remains true of the duplicate roles at13/108.
The baseline runtime is already accepted; intake did not repeat it merely to
regenerate this historical capture.

The fixed cooperative family deletes302, sets `103/1=0L162` and
`113/0=0L27`, and varies `27/0` over 872 actions. Four near-hits
`0L4`, `0L16`, `0R54`, `1R40` take a positive CD8 to the wrong first clean
endpoint: PC01, R8 still1, gap0, instead of PC001, R8=0, gap1.
The two inputs have explicitly different whole tapes. Three further actions
`0L113`, `1L113`, `1L66` have translated-left-half divergence certificates.
These are valid generic primitive inputs; no blank-run reachability is claimed.

The delivered owned literal filter rejects834 actions (710 wrong endpoints,
121 repeated complete configurations, three halts); the three divergence
certificates raise the total to837, leaving **35 unknown**. The834 were not
independently replayed in full. Caps, unsupported symbolic runs and window
escapes remain inconclusive. In particular, the four counterexamples do not
refute the separate shared-cancellation raw table.

The intake independently reconstructed and replayed **all seven explicit
obstructions on all six new layouts**: 42 checks, 182,964 literal transitions.
The four first-clean failures and three future-readable half-tape certificates
persist exactly. New source macros change some return-entry frames, so this
comparison transfers those particular failures, not complete old capture
coverage or all834 filter results.

State27 offers a useful unresolved direction. Its old arithmetic and proposed
new-return frames overlap at **every fixed observation radius** as the gap
grows. A local neighbor tag cannot separate them. Nevertheless their complete
languages are disjoint: after matching earlier runs, an old zero-run has length
three or two where the new one has length one. This is no same-input/different-
output impossibility theorem. Nonlocal discrimination remains possible, with
its own scanning and state costs.

## Source 143: positive source alternatives and bounded searches

Direct09 replaces cleanup by `R09=((D5,(I6,C2)),U)`: the inner loop transfers
R5 into R6, then successive U calls clear the sum. Direct13 replaces the test
by `L13=(A,(I5,A))` using the original cancellation A. The three order cases
show exactly the original equality branch and cleared scratch values. Both
terminate for all naturals and preserve all other registers; finite diagnostics
through100 and selected100,000-scale pairs are supplementary.

Direct09 has206 subtrees/4,748 leaves/four right-child decrements; Direct13
has207/4,760/none. Both raw allocations have220 states. The focused pilots
prove115 and131 arbitrary-natural primitive guards on78 and90 selected sites,
including the changed macros and selected external operation representatives.
**Unselected interfaces and startup remain unproved.** Shared zero actions at
303/122 or303/21 do not authorize merging their mixed arithmetic entry roles.
The11-source raw census has only220-state allocations and does not certify them.

The [source-stack census](intake187-u-stack.md) also applies Source141's all-natural U→V substitution to these
three new equality sources, with and without all81 retagging rotations.
The literal source/CFG census gives:

| Combined source | Subtrees / leaves | New zero terminals | Guarded cases | Right-child decrements |
| --- | --- | --- | --- | --- |
| Shared cancellation + zero-terminal | 206 / 4,752 | 4 | 6,183 | 4 |
| Direct09 + zero-terminal | 206 / 4,748 | 8 | 6,179 | 12 |
| Direct13 + zero-terminal | 207 / 4,760 | 12 | 6,199 | 12 |

In each case replacing U across the whole source equals replacing it inside
the four equality macros: no other U occurs. All81 rotations still compose
and preserve the ordered control graph. These are further source-equivalent
representations, with no205-subtree improvement. They have not been allocated
or verified as new binary machines; the extra right-child decrement obligations
must not be borrowed from an unmodified source's pilot.

The supplement also preserves these completed, bounded searches as historical
evidence. They were reviewed, not needlessly repeated during intake:

| Family | Recorded coverage | Scope limitation |
| --- | --- | --- |
| Direct folds | 47,306 ordered pairs | Fixed width-seven local constraint |
| Mixed-role detours | 12 pairs both ways, 20,928 actions | 64-step blocks; escapes not semantic failures |
| Delayed synchronization | 47,306 pairs | Keeper rows fixed; old1–4/new1–16 steps |
| Return footprints | 1,744 actions | Radius7; old16/new64; pending other edit excluded |
| Whole continuations | 1,744 actions, 566,192 symbolic rules | 667 caps, unsupported runs and short successful prefixes remain unresolved |
| Direct09 helper folds | 303 into122/28/109, 2,628 actions | 18,000 transitions total; the intermediate6,189 is already in the cumulative12,072 |

Together the reports support two next directions: source changes that alter
mixed helper entry contracts, and calculi whose missing logical calibration can
be proved before assigning them a machine count. None of the bounded negative
results establishes a global grammar or machine optimum. The fresh source
stacks and any subsequent results are recorded separately from the delivered
claims; the requested reduction below219 remains open.
