# Current PA consistency-machine comparison

Snapshot: `VladimirReshetnikov/ProveIt@1e1a41f799d4658b829cdd0eabae3775a0c8c4a0`.
This note is an independently assembled comparison of the repository material. It does not infer an arithmetic theorem from the presence of a machine table or a PASS receipt.

## Executive findings

The present corpus has **82 filed deliveries plus four current incoming archives: 86 delivery payloads**. One incoming archive reuses the basename of a filed packet but changes its mathematical content substantially. Its two principal transition tables are already present in the filed collection.

The unified replay verifies **13,109 tracked source payloads against their pinned Git blobs**, reads **18 distinct ZIP payloads through 30 references**, and finds **908 occurrences of 194-state matrices, 111 transition-table classes, 110 of them admitting a spanning root and one disconnected diagnostic**. This combines all `.tm` files in the PA subtree and current/nested archives with supported explicit JSON matrices and complete `.txt`, `.tsv`, and `.csv` matrices. The JSON extension adds no new 194-state class. Recognition does not execute arbitrary generators, extract prose-only tables, or establish correctness.

The 111 classes divide, using the reports' own evidence and explicitly manual classification of the newest research inputs, into **56 reported principal constructions, seven supplementary constructions, 36 research auxiliaries, four research seeds, seven rejected classes, and one diagnostic control**. These are evidence categories, not 56 independently checked iPRA consistency theorems.

The most relevant existing mechanisms occupy four largely independent axes: the arithmetic/logical emitter; the command-store interface; destructive comparison and return logic; and the physical decoder/register layout. Most 194-state results are different combinations or implementations of these inherited mechanisms. The same state count can conceal different source interfaces and different missing proof obligations.

The new **AX11GH/AX11GHS** combination was absent from every current named proposal and source discussion checked: AX11G retains the sum Shift, whereas GH/GHS retains the ten-entry AX interface. Exact full-tuple comparison now confirms that both new literal graphs differ from all 110 recognized spanning historical graphs and from one another, even after arbitrary control renaming, any spanning root, reflection, global symbol exchange, and ignoring terminal write/move effects. The remaining disconnected diagnostic is excluded by the spanning invariant. This structural result supplements, rather than replaces, the operational command proof.

## Reproducible inventory artifacts

- `packet_ledger86.{csv,json}`: one row for every filed or current incoming delivery.
- `comparison194_complete.{csv,json}`: all 111 recognized 194-state classes, their representative locators, mechanism/evidence labels, and file hashes.
- `representatives194/`: a literal representative of every class, usable without the repository or archives.
- `census_replay/`: authoritative unified rescan, including all nested historical archives and exact Git-blob checks.
- `literal194_summary.json`: preliminary direct `.tm` component scan counts and exact scope.
- `supplement_summary.json` and `supplement_occurrences.json`: explicit JSON/non-`.tm` recognition and its 311 194-state occurrences.
- `rebuild_census.py`: optional pinned-repository census replay using the three attributed, vendored recognizers. The reported historical labels are retained in the supplied ledgers; they are not inferred as mathematical truth from a transition graph.
- `check_novelty.py`, `new_candidates_novelty.json`, and `canonical_tuples194.json`: completed enlarged-symmetry novelty replay. It compares complete canonical tuples, not hash equality alone.

Counts are not interchangeable with those quoted inside older packets. The official filed `docs/MACHINES.md` covers 82 filed packets and gives 94 classes with 194 reachable states. The four new incoming archives add five principal classes and eleven research/neutral-edit classes; an explicit diagnostic was absent from that filed `.tm` comparison. Older 72- or 82-packet ledgers and 82-/94-class counts describe earlier snapshots or narrower recognizers.

## Mathematical proof status: three distinct evidence levels

The pinned top-level PA README states that neither machine-specific iPRA direction has yet been established for its primary table. It describes extensive standard-run Lean components, model-uniform scheduler/gate results, and generic IΣ₁-to-iPRA transfer theorems. Those are not themselves a literal-machine iPRA calibration.

Older research packets ordinarily claim a written **PA** equivalence. A relative iPRA proof that two physical machines halt together does not upgrade a PA calibration to iPRA. Likewise, an unfinished Lean build does not by itself invalidate an independently complete written mathematical proof. These distinctions should remain explicit.

The current incoming `pa194_ax11h_research_2026-11-14.zip` is a material exception to a blanket statement that all reports leave the arithmetic theorem open. It **claims a complete written iPRA calibration** for the existing AX11H and QAX11H tables, without a new Lean/Rocq kernel build. Its new files include `physical_ipra_audit.tex`, `source_command_completion.tex`, `foundation_paeq_completion.tex`, `term_leaf_completion.tex`, `forward_calibration_completion.tex`, and `consistency_equivalence.tex`. The original placed packet under the same basename explicitly leaves the absolute theorem open. The new claimed proof therefore needs mathematical scrutiny; the unchanged table hashes do not settle the claim. This inventory attributes that claim and does not certify its proof.

Other current incoming packets remain explicit about relative status: AX11G claims a relative iPRA halting transfer to primary PA194; AX11QH4L/R claims relative physical time bounds to AX11QH; GH/GHS supplies constructive command/refutation compilation and universal physical certificates, retaining the absolute arithmetic bridge as a separate obligation.

## Architecture comparison

### 1. Primary grammar and the state budget

The primary PA194 table implements the supplied separate-diagonal 195S source: 190 AX macro tokens and 3,673 resolved primitive instruction sites. Its budget is

`134 fixed controls + 67 raw AX readers - 7 simultaneous history folds = 194`.

The second PA194 uses 68 raw readers and eight folds. Several radix/controller alternatives use 135 fixed controls and an effective 59-reader contribution. Thus shortening the source program or removing a few primitive sites need not save a literal state. Extra multiplier helpers or newly incompatible folds can consume the apparent saving. Every shared-state proposal also needs to preserve the self-initialization path before it reaches the valid source-frame invariant.

The earliest PA195 and 195S/C variants are different source/store protocols. They are not just less compact numberings of PA194. Larger PA196 and U209/U208 predecessors supply the register engine, histories, logical calibration ancestry, and earlier contextual folds, but their own one-way formal results should not be silently strengthened.

### 2. Numerical calculus and emitted axioms

| Axis/family | Change | Essential proof issue |
|---|---|---|
| Primary, M4R | Separate diagonal-vacuity head with coefficient-four formula constructors | Original source-calculus and PA proof calibration |
| M5/M6 and descendants | Formula constructor coefficient becomes five or six | Hereditary recoding of formulas and variable labels, unused residues, exceptional zero code, restricted propositional-head dominance |
| Q | Exchange the two curried premises of the universal-distribution head | Explicit primitive-recursive proof translations; fixed restricted-implication exchange certificate |
| D/DHS | Emit the separate diagonal head at Γ(D) instead of Γ(A) | Rebuild selectors and the diagonal proof translation |

Q is independent of MP/cache protocol. There are Q designs with dummy-push MP, no-push MP, cached-result MP, original/symmetric Shift, and coefficients four/five/six. A new coefficient specialization is a genuine changed arithmetic implementation, but can be a modest contribution rather than a new proof-search architecture. The H5 report itself makes this qualification.

No accepted existing 194-state Γ(H) emitter was identified; H is normally the controller's cache-only halt protocol, not the choice of diagonal-head parameter. Conflating the two meanings would misdescribe the designs.

### 3. Command-store protocols

Use `(t,w,d,h)` for visible top, underlying stack, offset, and cached theorem.

| Mechanism | Operational change | Compiler consequence |
|---|---|---|
| Original MP | Successful MP pushes a dummy zero and exposes its consequent | Existing Pop/proof-word invariants |
| N | Successful MP omits the dummy push and returns `(b,w,b,0)` | Explicit reserved-zero discipline for subsequent Pop |
| C | Put the consequent in the cache and clear top/offset | New cached-store invariant and selectors |
| H | Shift tests cached `h=1` rather than `t+h=1` | A visible contradiction with zero cache requires Pop, not an immediate plain Shift |
| AX11 | Push the gate as well as the other generated heads, then fall into the full MP reader | Four encoded operands and an eleven-entry prefix; the fourth operand cannot be omitted |
| G | Saved generalization is `U(c,h)` with explicit first AX operand `c`, replacing `U(d,h)` | Generalization word no longer needs to set the offset first |

This is where a combined AX11GH design differs operationally from the available AX11G and GH protocols. The existing AX11G has all of AX11, G, Q, N, and original sum Shift. Existing GH has G, Q, N, H, but ten AX prefix entries. GHS changes the implementation of the same GH commands to symmetric comparison. Their combinations are mathematically plausible but require checking all-store soundness/completeness, zero-stack aliases, all eleven entries, actual fourth-operand consumption, and the final contradiction word.

### 4. Comparators, known-zero returns, and physical implementation

CS/HS and their Q/AX11 descendants reverse the destructive comparison order to remove a restoration loop. SUMS and sum-guard NS preserve the original sum test while changing the comparison algorithm. This is different from H, which changes the logical halting guard itself.

J, A, F, ZR, CZ/CSZ, and HA/HAZ replace selected unconditional jumps by decrements of registers proved zero. These are source identities only under their stated invariants. Their complete blank initialization must be verified separately: an apparently valid source-frame return can fail before the frame invariant is established.

PA194B changes the low-level dispatch and shares two history-marked reader contexts through a dedicated selector. It has 22 self-loops, unlike the earlier 21-loop family, and an exact all-tape local simulation argument. It restores the arithmetic marker row that the failed Runtime193 splice borrows.

PA1944L, AX11QH4L, and AX11QH4R change the association of four-increment decoders, adding a helper and a compatible fold. Their source program is preserved. The AX11QH4 pair supplies explicit relative halting-time factor-two bounds. Incoming research also contains B-composed 4L/4R graphs; these are research inputs, not additional principal calibrated machines.

PA194-AD, P5, TDY, and HX permute physical registers and router targets while preserving the logical source. They are not merely renamings of finite controls: they change the tape representation throughout the computation and the initialization time. Nonetheless, they are lower-level implementation variations, so a new register permutation should not be sold as a new logical consistency encoding.

## Exact duplicate and naming traps

| Names/deliveries | Actual relationship |
|---|---|
| PA194C across five C packets | Same principal graph, repeated derivations/packages |
| PA194HS and lowercase filed PA194NS | Same cache-only symmetric graph |
| PA194NS in uppercase PA194NS_research | Different sum-guard NS graph |
| PA194QN / PA194NQ | Same principal graph |
| Two QNS packets | Same principal graph |
| PA194CSZ / PA194X | Same graph |
| N6 paired and separate reports | Same principal table |
| QH5 in AX11 companion and separate report | Same principal table |
| QN6 paired and separate reports | Same principal table |
| AX11QH5 standalone and combined later report | Same principal table |
| Filed AX11H and current incoming AX11H | Same table; incoming report asserts a stronger new proof |
| Filed AX11QH and current incoming QAX11H | Same table under different naming; incoming report asserts a stronger proof |

Do not infer start state zero solely from contiguous labels. One older HAZ packet renumbered native states to zero-based labels without making state zero the blank start. Start-sensitive semantic comparisons must read the packet's map/metadata. The inventory forgets the start only for structural graph classification and novelty; it does not use that convention to prove halting equivalence.

## Why existing sub-194 artifacts are not solutions

The coefficient-three shortcut has an inconsistent numerical calculus with the supplied unchanged heads. A prior explicit primitive refutation and a later all-offset obstruction rule out that particular syntax/head family. They do not rule out every possible coefficient-three syntax, let alone every 193-state machine.

Runtime193 identifies native 301 with 88 and changes two decoder/engine rows. It passes the clean-source contracts but fails blank startup. Prior packets already classify every start of 52 physical runtime-experiment graphs: 10,036 runs, 106 halts, 9,930 exact outward rays, maximum prefix 117 transitions. Another exact certificate rejects all 9! physical register allocations for the specified Runtime193 splice/start. These are useful restricted obstructions, not a global state lower bound.

The current incoming AX11H packet reports that its new 193-state splices enter a ray after 92 blank steps. GH research adds extensive paired/triple startup edits and neutral-rewrite merger screens; surviving fuel-cutoff cases remain unresolved rather than being promoted to permanent failures. The even-only scheduler is mathematically meaningful but currently costs 195 states in its verified complete implementation. The even-runtime194 graft is a rejected diagnostic.

## Where new effort is best spent

The numerous independent-looking names largely populate a product of the same few design axes. Repeating coefficient, Q, H, AX11, or physical-permutation combinations without checking the current incoming ZIPs risks redelivering an existing table. The four current archives already cover AX11G, GH/GHS, and AX11QH4L/R.

A sub-194 success still needs either a genuine effective-reader saving below the repeatedly attained score 60, a smaller fixed runtime, or a representation/protocol change that frees a helper while preserving complete blank initialization. A successful clean-frame quotient alone is insufficient. The corrected Runtime193/B comparison makes the startup marker conflict particularly concrete.

The new AX11GH/GHS protocol composition fills a current gap: its generalization interface, fourth operand, eleven-entry selector lengths, cache-only contradiction detection, and Pop compiler are jointly addressed by the new construction and command proof. It should be described as a new composition of credited mechanisms and exact literal implementations, not as the invention of each constituent idea or a wholly new proof-search architecture.

The most valuable mathematical work beyond the state count is to scrutinize the current incoming claimed full iPRA compiler and physical internalization, then make any transfer theorem explicitly rest on the validated parts. Repository-level status and newer incoming proof claims presently differ; both must be reported accurately.

## Principal source anchors

All source locators are relative to the pinned repository revision above.

- `Computability/BusyBeaver/Research/PA/README.md`: current formal endpoint and open obligations.
- `Computability/BusyBeaver/Research/PA/docs/MACHINES.md`, `MACHINES.tsv`, `MACHINE_FILES.tsv`, `machine_classes.py`: current filed table classes and comparison conventions.
- `Computability/BusyBeaver/Research/PA/docs/README.md`: all82 filed delivery descriptions.
- `.../docs/PA194B_PA194G_research_2026-11-14/comparison/named_194_designs.md` and `comparison_narrative.md`: attributed forty-principal/seven-supplementary historical architecture taxonomy.
- `.../docs/pa194_research_2026-11-14/comparison/frontier_comparison.csv`: historical82-spanning/one-diagnostic class classifications matched to current literal canonical classes.
- `docs/incoming/pa194_ax11g_research_2026-11-14.zip`: new AX11G source interface and relative proof.
- `docs/incoming/pa194gh_research_2026-11-14.zip`: new GH/GHS source interfaces and command compiler.
- `docs/incoming/pa194_ax11qh4_research_2026-11-14.zip`: four-increment source-preserving physical variants and clock bounds.
- `docs/incoming/pa194_ax11h_research_2026-11-14.zip`: unchanged AX11H/QAX11H tables with newly claimed full written iPRA calibration.

The larger ZFC, DiophantineConsistency, and ConciseIPRA branches are analyzed separately by the theory task; none of their logical strengths or state savings should be imported without the relevant consistency and literal-runtime translation.
