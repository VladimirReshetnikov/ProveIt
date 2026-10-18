# Batch 164: the routed 245-state candidate

Intake findings, 17 October 2026 (workspace date). The delivery is dated
18 October 2026. This single-manuscript intake prioritizes the user's request
for commit `8286787dd0`; it is source **68** of this host. Placement
`46e8518e0e` preserves 273 ancillary files from 294 payloads. The other 21
files, including the manuscript, PDF and delivery README, remain recoverable
from that committed archive. The six earlier queued archives remain pending.
Their scratch source numbers were provisional, and do not reserve maintained
source numbers. No delivery checksum manifest was verified or normalized.

The source pin is ProveIt `c6bf052c70bbbafba8c39370a6a2d123f57cd2c1`;
the upstream pin is `c132d7eae8158cd3a9850ea3eb7251158c3dd821` on
jeff87654/busy-beaver's `zf-254` branch. The construction builds on the
Mira-Cult 254-state construction, Jeff Ketchersid's verification, Andrew James
Wade's compiler framework, and ProveIt's earlier machines. Delivered notices and licenses are retained.
This is an addition to the existing minimization spine, using the established
reconciliation-note option; the delivered base article and its labels are
unchanged, and no merged article PDF is produced.

## Result and formal boundary

The candidate has **245 working states**, two symbols, one two-way infinite
tape, and a blank-zero start. Initialization is included. Its canonical start
is 0, dispatcher 88, separate halt 245, and all 490 working transition rows
are defined. The canonical table is
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`;
the old-label table is
`f8dbeacdad5fd89c57e3f240781324b09110be8e0ccdb838a9c710fb28d2a267`.

The delivery claims an ordinary mathematical proof of
**ZFC ⊢ (¬Halt245 ↔ Con(ZFC))**. Independent source reviews found no
substantive mathematical blocker within their stated scopes. The complete
fresh executable suite passes, including all 8,391 expanded whole-frame cases,
2,312,645 symbolic rules, exact startup and 8,385 finite literal regressions.
Four supplemental and four historical diagnostic checks also pass. This does not
supply a newly compiled Lean endpoint, a serialized ZFC derivation, or the
requested proof inside PA. The exact [246-state external Lean endpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/prefix246_binary.md)
remains the formally checked baseline. In particular, report.tex:414's
reference to the earlier 252-state endpoint describes its older source pin;
the repository now also has the closed exact 246-state endpoint.

The proof-search calculus and all eight axiom-construction rows are retained.
No stronger consistency assumption or weakened theory buys this saving.
Consistency gives actual nonhalting and its unprovability in ZFC; the opposite
unprovability is not inferred from consistency alone. The delivery retains an
appropriate arithmetic soundness assumption for two-sided independence.

## What changes

The useful new idea is to optimize the source grammar, the special entry
routes and the zero scanner together. The old decomposition is 119 framework
roles plus 127 grammar roles. Absorbing the special router at old state 177
into the charged grammar and shortening the scanner gives **117 + 128 = 245**.
Labels 74 and 177 are reused; only old label 247 disappears from the working
label set. There are 104 changed surviving rows, including four framework
rows. This is not an isolated state merge.

The rotation at 178 is repaired by routing 218/0 through 86 and reassociating
98, using the former scanner label 74 as a grammar helper. All 22 local
entry contexts and 54 bootstrap equations matter. The final grammar's maximum
zero run is six and its maximum path depth is 51. Those statistics guide the
search; the universal runtime checks establish the implementation contracts.

All 6,460 ordered instruction operations and arguments match the original,
but 6,241 leaf addresses change. A 3,013-pair, 6,024-edge segment bisimulation
handles breaks and continues, which ordered leaf equality alone would not
justify. The actual binary runtime uses complete frames with header distance
64+n for arbitrary n, independent arbitrary primary registers, and any
nonempty finite spare list. Pointer normalization is checked for all 8,390
nonhalting successors. The margin increases by positive-decrement plus
pointer overflow, and increment appends a spare, so composition preserves the
frame premises indefinitely.

The exact initializer takes 407,915 steps and reaches the same frame as the
checked 246 machine: head −5, marker −6, header 176, distance 181, logical
registers `(3,0,0,0,3,0,0,0,0)`, and 167 spare blocks of value one. The complete
tape has 351 one-cells and zero elsewhere. The scanner explanation checks
three zero cells at each of 1,410 contractions; each saves two moves from the
old 410,735-step prefix. A separate direct replay checks the final grammar
machine, not only the scanner-only edit.

## Other results retained

The intermediate 128-rule grammar with a seven-zero path failed a universal
affine obligation at source leaf 2337, a decrement of logical T. Its bounded
literal probe was unresolved; neither observation proves eventual behavioral
inequivalence. A 129-rule zero-six intermediate gives a 246-state control.
The final 128-rule solution was found by a heuristic with seed 129177 and
7,040,505 recorded proposals. Search statistics and two bounded 120,540-recipe
merge sweeps are historical evidence, not exhaustiveness or state lower bounds.

The supplemental architecture work proves an eight-axiom-row permutation
translation with 25 commands and 54 fields per axiom leaf, checked for 40,320
orders and 322,560 selectors. It also gives an exact 702-to-533-call spelling
of the same 1,270 finest AX tokens. The latter is minimal in the fixed
44-atom vocabulary, yet its supplied grammar costs 147 rules rather than 127.
It therefore does not improve the binary state count. The final 245 machine
uses the original AX word. The original grammar/atom expansion dictionary has
no collisions; the mandatory old non-AX/boot closure costs 51 rules.

Finite-field affine analyses for primes 2, 3, 5 and 7 concern the original
source graph. At every nonempty abstract site, the absolute-header resource
fiber has equation `H + sum(registers) − K = 15 (mod p)` and one free dimension;
the pointed header-distance/spare fiber is the full product with two free
dimensions. These are abstract closures, not a claim that all their points
are concretely reachable or that nonlinear invariants cannot help. No new
guard exclusions result. The separate propositional matrices refute
completeness of specified specializations of Łukasiewicz's fourth parameter;
they do not refute CP/GIC equiconsistency. The exact-register lifetime witness
concerns a theorem-safe source execution, not reachability from this blank
initializer, and does not exclude packed register representations.

## Reviews and next formal work

See the [mathematical review](intake-164-mathematical-review.md),
[machine review](data/intake-164-machine-review.json), and
[reproduction instructions](intake-164-reproduction.md) for independently
reviewed scope and fresh execution records. The [placement map](data/intake-164-placement.json)
discloses every rename. Code is under `code/68-route245-*`, records under
`data/68-route245-*`, and notices/audits at the host root. Delivered files
continue to use their original nested paths; recover the package before
running them. Two stale delivered references are explicit: the runtime proof's
`gradient245-zero6/machine.tm` means `machine/zfc245.tm`, and the supplemental
README's root `renumbering.json` is under `machine/` or `certificate/`.
The independent abstract grammar audit retains a fixed framework count of 118
and therefore prints 246 for 128 rules; this label excludes the scanner
shortening. The literal table and separate composition checker establish
117 + 128 = 245. The delivered audit is preserved unchanged.

All 46 rows of the 23 core arithmetic/selector states inspected against the
current 246 implementation are unchanged in old labels. Their proof structure
is reusable. Canonical numbers still change when label 247 is removed. The
new tree, changed decoder routes, complete coverage at padding 64, and exact
407,915-step startup need their own Lean bindings. These are the next concrete
formalization obligations; the existing consistency calibration can be reused
after the new machine simulation is proved. PA internalization remains open.
