# Current PA-machine archive audit

Source: `VladimirReshetnikov/ProveIt` commit
`906367250a7f96c923147b10df392294bced7be5`.

## Outcome

Every one of the 27 incoming archives was opened, its top-level README was
read, and every nested ZIP and literal `.tm` member was inventoried without
executing archive code during the inventory. None of these archives represents
a machine below 196 working states as a successful construction. Several
contain literal 195-state diagnostic tables whose intended simulations fail.
This is a statement about the inspected constructions, not a lower bound.

The current source differs materially from the older 23-archive census.
There are five additional designated 196-state graphs: Combined196, three
diagonal-calculus layouts, and zerojump196. The selected corpus now has
20 pairwise nonisomorphic rooted action-labelled graphs, including two
experimental MP tables. The selection deliberately excludes exploratory
tables and known blank-halting negative controls. It does not assert that
all 20 have equally strong correctness evidence.

## Freshly reproduced counts

| Quantity | Count |
|---|---:|
| Top-level incoming ZIPs | 27 |
| Distinct ZIP byte payloads, recursively | 40 |
| Greatest nested depth | 7 |
| Literal `.tm` members in distinct ZIP payloads | 1,466 |
| Byte-distinct `.tm` files | 521 |
| Parsed-distinct transition tables | 515 |
| Unparsable `.tm` files | 0 |
| Selected 196-state tables | 20 |
| Rooted action-preserving graph classes in that selection | 20 |
| Working states / action-bisimulation classes for each selected table | 196 / 196 |
| 195-state table occurrences | 14 |
| Byte-distinct 195-state forms | 8 |
| Identified rejected 195-state constructions | 6 |

The 1,466-member inventory includes earlier parents, copies, experiments,
rejected candidates, and small synthetic controls. These are not 1,466
accepted consistency machines. Rooted graph reachability permits arbitrary
read-symbol sequences; it is not reachability on the actual blank run.
The action-bisimulation result rules out ordinary state identification
preserving each transition's write/move action and next equivalence class.
It does not rule out history-sensitive or multi-step reductions.

`current_inventory.json` records exact archive/member locations and hashes.
`current_archive_comparison.json` and the CSV provide all 27 contributions
individually. The older 23-entry comparison is adapted with attribution from
`pa_below196_research.zip`; its archive identities were rehashed against the
current checkout, and its outcome descriptions were corroborated against
each archive's own README. The newest four contributions were read directly.

## Main machine families

| Family | Working states | Primitive source sites | Distinction |
|---|---:|---:|---|
| James Chang PA209 | 209 | 3,948 | Direct predecessor of PA196 |
| Original U208 A/B | 208 | 3,909 | Separate U209 ancestry; conditional-history fold |
| U208 helper variants | 208 | 3,909 | Eighteen additional helper choices; twenty graph classes overall |
| Published PA196 | 196 | 3,812 | Transposed universal constructor, six heads, guarded equality vacuity |
| Combined196 | 196 | 3,788 | H-only Shift and MP result in H |
| Diagonal196 | 196 | 3,700 | Diagonal-vacuity axiom emitter, 191 macro items |
| Separate196 | 196 | 3,673 | Unconditional diagonal clause separated as an extra head, 190 macro items |
| Scanner-oriented Separate196 | 196 | 3,673 | 69 AX readers, seven folds; remaining scanner obstructions |
| Zerojump196 | 196 | 3,812 | Source-26 zero-register jump encoded by a decrement |
| Direct-negation197 in Combined196 packet | 197 | 3,556 | Strong source reduction with larger physical allocation |

Published PA196 uses 36 tape-engine states, 13 leaf routers, and 147 reader
states representing 159 internal source nodes. Its six reader-pair folds
are already charged in the published total. The original U208 history fold
does not supply another deletion by renaming the same numeric labels.
The U208 and James Chang PA209 tables are different despite their ancestry
passing through the same headline state count.

## Fresh certificate replays of the newest positive tables

The five added selected tables were independently recounted, hashed, rooted
canonicalized, and tested for ordinary action-bisimulation. Their supplied
uniform source-contract and exact startup verifiers were then replayed in
extracted working copies.

| Table | Uniform instruction cases | Exact blank startup | Result |
|---|---:|---:|---|
| Combined196 | 4,928 | 57,922 | PASS |
| Diagonal196 | 4,815 | 58,154 | PASS |
| Separate196 | 4,780 | 58,154 | PASS |
| Scanner-oriented Separate196 | 4,780 | 58,294 | PASS |
| Zerojump196 | 4,959 | 58,402 | PASS |

The Combined196 replay also passed its source binding and command algebra
checks, including versions run with Python optimization. The zerojump replay
reconstructed the 274,880-pair joint zero/positive invariant, its 14 eligible
forward jumps, and the exact rejection witness for its attempted 195-state
fold. The scanner-oriented replay rebuilt the identical table bytes and
verified unchanged source control flow under its exterior rotation.

These are executable symbolic checks using retained register-engine
interfaces, plus literal finite whole-tape startup checks. They do not
constitute new Lean proofs. The existing verifiers were reviewed at their
entry points and used as supplied; their entire symbolic runtimes were not
independently formalized here. Logs are included.

## The six rejected 195-state constructions

| Diagnostic | Recorded failure and its scope |
|---|---|
| Two-rotation quotient | 93 failed primitive contracts; native/dense files are one construction. The source CFG identity survives but decoder history does not. |
| `warm_physical_61_8047` | 714 symbolic failures; source 1111 has a concrete four-transition cycle after 26 transitions from a valid frame. |
| `extended_physical_61_12085` | 777 reported symbolic failures; no new concrete counterexample was replayed in this audit. |
| Seven-zero scanner regrouping | Source 1003 returns to the wrong clean frame; the eight-zero repair has 196 states. |
| Short-scanner deletion in newest diagonal packet | 96 unrestricted branch failures; even the invariant-conditioned clean seed fails. Its first root return after 118 steps differs in 43 tape cells. |
| Zerojump/helper fold | Source 26 takes the wrong successor and increments register 6; exact failure is reproduced both in an isolated frame and on the candidate's actual blank trace. |

A failed source simulation is not automatically a theorem that the altered
table cannot accidentally have the same blank halting property for another
reason. These tables have no accepted proof of the requested property, and
their proposed implementation arguments fail. The audit does not claim a
stronger theorem without evidence.

## Lessons from earlier attempts

1. Source grammar size, source word length, and binary state count must be
   tracked separately. The 157-node source does not furnish a 157-state TM;
   its reported complete repaired implementation has 207 states. Direct
   negation removes hundreds of source sites but compiles to 197 states.
2. Individually possible reader folds need not compose. The optimistic
   `134 + 70 - 9 = 195` count in a diagonal layout fails simultaneous-helper
   and entry-side checks. The stronger search retains cost 62, hence 196.
3. Initialization matters independently of interpreter contracts. The
   U208/PA196 hybrid passes 4,957 arbitrary-register contracts in a supplied
   frame but every existing initial control reaches an outward blank loop.
   Its 197-state prefix repair reaches a frame but fails a runtime contract.
4. Scanner shortening requires a source-address and entry-history proof.
   A zero-run bound alone is not enough, and the strongest supplied
   invariant-conditioned short-scanner test still fails.
5. Much direct folding has already been attempted. The latest reports cover
   all 38,220 ordered baseline state identifications with stated two-row,
   bounded-window templates, as well as large head-offset and some three-row
   screens. These are narrow finite search results, not global lower bounds.
6. Formula recodings must preserve the property's numeric-code/private-label
   interface. The explicit membership-transposition example `R(5)=9` changes
   the guard at parameters `c=5,a=9,b=0`. A logical recoding lemma alone does
   not provide a valid emitter or proof compiler.

## Proof status and the requested PA biconditional

The inspected imported Lean endpoint explicitly exports

    PA proves Nonhalt(PA196) -> Con(PA).

It also has external nonhalting and independence results. Those do not by
themselves export the converse internally. This is a precise limitation of
the inspected formal endpoints, not a claim that the converse is false.

Several incoming manuscripts go further at the ordinary mathematical proof
level. They propose or assert proof-producing translations into PA by binary
bit membership, equality, and formula-specific bounded comprehension, and
combine these with positive instruction simulations and exact startup. The
Combined196 packet in particular writes down command selectors, a protected
stack compiler, source-loop inductions, and the tape/source time argument.
A lack of a new Lean theorem should not be presented as proof that all those
ordinary arguments are invalid. Conversely, replaying a symbolic instruction
checker is not a substitute for auditing the uniform proof translation and
its arithmetic representation.

The full formal endpoint still needs arbitrary-internal-time literal-trace
reflection and uniform native-proof-to-PA-proof translation, including the
zero-alias stack convention `pair(0,0)=0`. A valid state reduction transfers
the exact endpoint proved for its parent; it does not create a missing
arithmetic implication merely by reducing the state count.

## Concrete new combination worth investigating

The most specific untried combination identified in this audit is to graft
the newest effective-62-reader Separate196 or Diagonal196 AX grammar into
the Combined196 exterior, then allocate readers jointly. The new diagonal
layouts retain the old 169-site exterior; Combined196 retains the old
3,643-site AX while replacing the exterior by 145 sites. Older combination
searches used the physically larger 198/199-state diagonal layouts. This
cross-archive combination therefore has a different cost profile and is a
well-defined next experiment. Its command selectors must also be adapted
because Separate196 pushes an additional axiom item. No state saving is
asserted here.

## Reproduction

Run `python3 verify_selected.py` for the compact 20-table graph/byte census.
It uses explicit exceptions and is independent of Python assertion settings.
Run

    python3 audit_archives.py /path/to/ProveIt/docs/incoming output.json

to rescan the current incoming archives as data. Confirm that the checkout
is at the stated revision before comparing counts. The five full supplied
runtime verifiers remain in their original pinned archives; their replay
logs and table hashes are retained here. Original James Chang and ProveIt
licenses accompany the selected tables.
