# Comparison of the PA consistency-machine corpus

## Result and exact scope

The comparison is pinned to `VladimirReshetnikov/ProveIt` commit
`1c9524d8bf2e0a27b9a16ff622359927f536e663`. It covers all 61 filed research
packets under `Computability/BusyBeaver/Research/PA/docs`, all 11 current
`docs/incoming` ZIP archives, and the remaining PA directory's table and data
files. The delivery ledger therefore has 72 entries. Duplicate deliveries are
kept in that ledger, while their transition graphs are deduplicated separately.

The completed scan verified 10,171 tracked files against their exact Git blob
SHA-1 identities. It inspected 15,220 direct or archive-member payloads and
followed 25 distinct ZIP payloads through 37 archive references, recursively.
There are no missing-source or parse errors recorded by the scanner. The scan
recognized 3,422 complete table occurrences, 752 normalized labeled transition
tables, and 638 distinct action graphs having one halt target and a root from
which all their working controls are reachable. Six normalized tables have no
such root and are retained as diagnostics rather than silently discarding their
unreachable components. Thirty-five incidental one-state JSON fragments were
excluded; explicitly stored one-state literal tables remain in the inventory.

The recognizer accepts complete numeric five-column binary L/R tables in
`.tm`, `.txt`, `.tsv`, and `.csv`, and the explicit transition arrays,
dictionaries, row records and embedded text forms documented in
`json_inventory.py`. It does not run arbitrary generators or infer machines
from prose or TeX. The packet ledger supplies the accompanying design-level
coverage. Consequently these are reproducible counts for a stated syntax and
snapshot, not a claim to recognize every possible encoding of a Turing machine.

The present 194-state frontier contains **82 spanning action-graph classes**,
plus one disconnected synthetic diagnostic. The earlier filed-packet catalogue
lists 49 194-state classes because it only considers filed `*.tm` tables.
It misses incoming constructions and tables encoded only in JSON. The 83-entry
comparison table classifies the full current frontier as follows:

| Attributed historical evidence | Classes |
|---|---:|
| Reported principal constructions | 40 |
| Supplementary constructions | 7 |
| Research auxiliaries | 25 |
| Research seeds | 4 |
| Explicitly rejected designs | 6 |
| Disconnected diagnostic control | 1 |
| Total | 83 |

These categories describe what the supplied packets claim and document. They
are not 40 freshly proved consistency equivalences, and no row is being
promoted to a completed iPRA theorem by this inventory. All 82 connected
frontier representatives are retained for exact reproduction of the novelty
comparison.

## Which designs actually differ

The source architecture is highly shared: an enumerating scheduler operates
on a small register store, a numerical proof calculus supplies axiom heads,
a binary source tree directs a unary register-file engine, and contextual
folds reduce the physical controls. Most changes affect one of these layers.
The number of source instructions and the number of physical states are
therefore different optimization objectives.

| Family | Substantive difference | Consequence for correctness and cost |
|---|---|---|
| PA209/U208 and PA196 | Earlier numerical/source bases, register controls and contextual folds | Larger ancestors and reusable compiler components; their existence does not calibrate a later changed table automatically. |
| PA195, 195S/C/DC | Separate or bundled diagonal head and different cache conventions | Predecessors of the 194-state family; source and selector interfaces differ. |
| Primary PA194, alternate 68/8 | The same separate-diagonal calculus and original sum-testing controller; allocation `134+67-7` versus `134+68-8` | Both have 194 controls, but different complete graphs. The primary has a ten-entry AX selector interface. |
| PA194-AD | Physical A/D register placement | Changes routing and exact initialization while keeping the resolved abstract source. |
| C and CS | Successful MP stores its result in the cache and clears top/offset; Shift tests the cache. CS reverses the destructive comparison operands | A different command-store protocol; CS removes a restoration loop but requires an extra reader compensated by a fold. |
| N | Successful MP omits its dummy-zero push, returns a visible consequent, and preserves the original sum guard | Requires a reserved-zero proof compiler, not merely deletion of the physical push. |
| H and HS | Visible no-push MP with cache-only Shift; HS uses symmetric comparison | The final contradiction must reach the cached head, for example using Pop. A plain sum-guard completion word is insufficient. |
| SUMS and sum-guard NS | Symmetric comparison preserves the original sum guard, with original or no-push MP | Distinct from the cache-only NS/HS protocol despite the reused name. |
| Q, QN/NQ, QNS, QS, QH/QHS | Exchange the two curried premises of the universal-distribution head, combined with the corresponding controller | A recurring emitted formula changes; K/S/MP proof translations justify the premise exchange. |
| D and DHS | The diagonal-vacuity head is Gamma(D), replacing Gamma(A) | Changes offsets and selectors. D/DHS use a different decoder allocation; DHS has `135+69-10=194`. |
| M5/M6, N5/N6, H5/H6, Q5/Q6, QN5/QN6, QH5/QH6 | Change the numerical constructor coefficient from four to five or six | Changes formula arithmetic and MP matching throughout execution. One native row can change all 61 constructor blocks. Logical recoding must handle unused residues and the zero-code alias. |
| J, F, A, CSZ/X, ZR, HA/HAZ | Replace source jumps by decrements of registers proved zero, sometimes combined with A/D placement | Require an inductive source invariant and a separate complete startup check. Correct source behavior alone does not protect initialization. |
| R, M4R, source rotations | Reassociate the binary source tree | Preserve the resolved source graph but change addresses and physical fold opportunities. Many retained rotations are research objects, not independently calibrated releases. |
| AX11 | Push the final guarded AX head and enter the full MP parameter reader | AX now has eleven stack entries and consumes an extra parameter `z`. The completeness word chooses `z=0`; soundness must cover every `z`. |
| MP196 | Successful MP immediately recognizes consequent one and otherwise returns a visible consequent with cleared offset | Changes the halting protocol and requires its own invariant; the implemented table has 196 controls. |

The common identity `fixed controls + raw AX readers - compatible folds`
explains why deleting several source instructions often leaves the physical
count unchanged. A tempting pair of optimizations may also compete for the
same control or fold, so their claimed savings cannot simply be added.

## Repeated tables and ambiguous names

The same principal PA194C table appears in five deliveries. The lowercase
`pa194ns_conpa_2026-11-13` machine is the same graph as PA194HS, whereas the
sum-guard NS in `PA194NS_research` is different. PA194QN and PA194NQ repeat the
same graph; two QNS packets repeat their primary QNS. PA194CSZ equals the later
PA194X. N6 is repeated by multiple earlier packets. Among the current incoming
archives, QH5 appears both in its own packet and in AX11's companion material,
and QN6 appears both in its own packet and beside QN5.

A designated starting control is part of a machine theorem. It is not part of
an unrooted graph identity. Some native tables in the HAZ packet were relabeled
`0,...,193` while their intended starting control was not zero. The present
occurrence ledger records an explicit comment start when present, labels the
usual dense-zero convention as an assumption when used, and does not assign
zero to a native table merely because its labels are dense. Unknown starts
remain unknown. Novelty is tested against every spanning root, which is
stronger than comparing just the documented starts and avoids this ambiguity.

Similarly, graph reachability is not evidence that every control is visited
on the actual blank run. None of the counts is a blank-run coverage assertion.

## The 193-state objects are not established solutions

The current corpus contains **53 spanning 193-state action graphs**. This is a
large increase over the two conspicuous early 193-state objects, caused mostly
by later experiment archives, not by successful consistency constructions.

The first important object is the coefficient-three shortcut. Its physical
implementation is smaller, but the proposed numerical calculus is inconsistent.
For the supplied coding, `I(a,b)=3p(a,b)` and `E(a,b)=3p(a,b)+3` collide:
`E(1,0)=6=I(0,1)`. The supplied proof certificate combines that collision with
the unchanged heads and inference rules to derive code one. Later work extends
the obstruction to all nonnegative constant equality offsets for that particular
unchanged coefficient-three family. This is a rejection of a specific logical
coding, not a lower bound on all 193-state machines or all three-residue codes.

The other central object is Runtime193. It identifies marker control 301 with
88 and changes `(88,0)` and `(51,0)`. Its generic source-outcome contracts can
hold, yet its inherited blank startup enters an outward blank ray. Thus it is
a runtime implementation with a missing initialization, not a blank-start
consistency machine. The later 51 classes are experimental transplants and
related modifications. The QN6 packet alone retains 49 patched files; some
repeat graph classes. Its recorded all-start screen reports 9,457 simulations
of those files, 100 halts, 9,357 certified rays, and no accepted complete source
frame. These are attributed historical results; the present census does not
claim to have rerun all 9,457 simulations.

The supplied ZFC-style relay also fails: its conditional source screen has
nine failures, and a literal startup certificate reaches a blank ray after
116 transitions. The relevant positive lesson is precise: runtime contracts,
source equivalence, startup correctness and arithmetic calibration are separate
obligations. Passing one is not a substitute for the others.

## What the negative searches establish

The literature in these packets includes many grammar anneals, source-family
screens, merge searches and startup repairs. Their search counters count
attempted moves or finite tests, frequently including repeats and inapplicable
moves. They do not count independently verified machines and are not global
lower bounds. The exact direct-selector obstruction is similarly restricted:
for a specified raw 201-control parent and a specified disjoint-fold family,
its dual certificate bounds the net saving by seven. Changed grammars,
helper chains, overlapping folds and more general detours lie outside it.

The count 194 is therefore the current supported physical frontier in this
corpus, not a proved minimum. Repairing Runtime193's startup, finding a genuinely
new source interface with a cheaper compatible allocation, or changing the
register engine remain logically open possibilities. A source change should
be judged after recompilation and full tape simulation, not by token count
alone.

## Relation to the requested iPRA statement

The top-level PA README at the pinned revision explicitly says the two
machine-specific iPRA reductions remain open for the primary 194-state target.
The papers above predominantly assert ordinary PA-provability arguments and
supply executable source/tape certificates. An ordinary PA proof is not thereby
an iPRA proof. A Lean theorem about standard finite runs is not by itself a
proof that the corresponding arithmetic equivalence holds at nonstandard
proof lengths and machine times. Nor is a conditional endpoint a discharged
calibration premise.

The structural comparison and new physical constructions therefore support
relative preservation results. They do not repair the inherited arithmetic
calibration merely by producing fewer states or a new graph. The requested
property must be stated conditionally until that remaining proof is supplied.

## Novelty of this task's two new constructions

The new AX11QH5 table has 194 working controls and 388 rows. It composes the
QH5 source (coefficient five, exchanged universal head, visible no-push MP,
cache-only Shift) with AX11's final AX push and full field-reader fallthrough.
This changes recurring command behavior rather than just state names. The
reported construction receipt has 3,732 source sites and 4,839 source outcomes;
the latter corrects an earlier provisional count of 4,833.

The companion physical-layout table swaps register blocks 7 and 8 and changes
two routing rows of the primary machine. Its abstract source is unchanged, but
its transition graph and concrete tape layout differ. The state-reduction
workstream separately establishes its exact startup and universal contracts.

Both tables were compared by **full canonical tuple equality** against every
one of the 82 old spanning 194-state graphs. The comparison permits arbitrary
state renaming, every spanning initial root, global L/R reflection, global
symbol complement, and arbitrary write/move effects on the terminal edge.
Neither has a match. Bit complement is deliberately a broad structural test,
not an assertion that changing the blank symbol preserves the same zero-blank
semantics. The one disconnected diagnostic cannot be isomorphic to either
whole-table-spanning candidate. The final census reference set and all 82 file
hashes were checked against the exact novelty receipt.

These are corpus-relative novelty results, not global priority claims. The
new ordinary constructions and their physical certificates still inherit the
separate iPRA calibration obligation identified above.

## Reproduction and data files

`full_summary.json` gives the final complete counts with zero errors;
`full_census.json` records every occurrence, source identity, archive reference
and graph class; `packet_ledger.csv` contains the 72 deliveries; and
`frontier_comparison.csv` contains all 83 frontier records with mechanisms and
attributed evidence. `representatives/` retains the 193--196 graph tables,
including all 82 connected 194-state representatives. `check_novelty.py`
reproduces the exact broad graph comparison. `new_design_novelty.json` and
`novelty_scope_validation.json` bind the two new candidates to the final scope.

For a full repository reproduction, `audit_repository.py --repo CHECKOUT
--output DIRECTORY` reads pinned Git blobs directly, so it does not need a
full working-tree checkout. Its recognizers are the attributed, preserved
`literal_inventory.py` and `json_inventory.py`, with `machine_classes.py`
providing the catalogue-compatible rooted fingerprint. It does not execute
research generators or claim that an inventoried table is correct.
