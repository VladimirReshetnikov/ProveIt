# Audit of the PA consistency-machine corpus

## Snapshot and principal findings

This audit is pinned to ProveIt commit `1e407ae841e4666f932777fad977ba784ebbcfd5`. The requested PA tree contains **41 filed research packets**, and `docs/incoming` contains **five further archives**. Thus the present top-level delivery inventory has **46 packets**. Many recent packets describe a 41-packet comparison at the older commit `17f92105e2bc4317feae6c219cb2143437b482ff`; their novelty claims are historical claims against that older corpus, not novelty against the present snapshot. The filed `PA/docs/README.md` assertion that no archives remain in incoming is stale at the present commit.

A fresh read-only literal-table census recognizes 3,741 occurrences, 666 byte forms and 476 root-spanning action-graph classes. There are two disconnected synthetic controls (six and nine states) outside the graph-class count. At 194 states, the census finds **261 occurrences, 51 byte forms, and 28 graph classes**. Sixteen of those classes occur as principal or fully described companion constructions; nine are supplementary/research inputs, and three are explicitly rejected. These classifications record the evidence supplied by the packets; they do not mean that this audit has independently reproved every claimed PA equivalence.

The most conspicuous duplicates are:

* Five separate PA194C reports deliver the same principal dense table, SHA-256 `d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`. The report `pa194_new_designs_2026-11-13` supplies an additional distinct PA194CS construction.
* The newest PA194R packet's **PA194X is exactly the same literal machine as PA194CSZ** in the PA194Q packet. Their common dense SHA-256 is `62e93098caf7c09ff2938d07064f0dbbb47c71ec369892968258fff708592269`.
* The older five U208 submissions initially supplied nine named final tables but only two rooted action-preserving graph classes; their state savings all use the same contextual 172/211 fold and cannot be added together.

No recognized non-synthetic table below 194 working states is present in this snapshot. This is a corpus statement under the stated recognizer, not a nonexistence theorem and not a claim that every representation inside arbitrary source code was recognized.

## Recognition and exact novelty convention

`corpus/audit_census.py` recursively scans `Computability/BusyBeaver/Research/PA` and `docs/incoming`, including nested ZIP members. It accepts complete numeric five-column binary tables in `.tm`, `.txt`, `.tsv`, and `.csv`: each working state has exactly one transition for each bit; moves are L/R; exactly one target label has no outgoing rows. Leading comment lines beginning `#`, `;`, or `//` are allowed. A table must otherwise consist entirely of transition rows. Arbitrary tables encoded only in Python, Lean, JSON, prose or PDFs are outside this recognizer.

Repeated byte-identical nested ZIP payloads are traversed once; all 31 ZIP references and 19 distinct ZIP payloads are recorded. The occurrence count consequently differs from previous reports that revisited duplicated archive payloads. The filed source tree also omits byte-identical upstream copies that are available in the separate imported James Chang snapshots. All stated counts refer to this exact traversal, not to original archive-member totals.

For a literal table with n working states and a graph-spanning root, canonicalization tries every eligible root, numbers states by first discovery in fixed read-bit order and records all write, move, and target data. The smallest tuple is invariant under arbitrary working-state renaming and under changing the designated initial state. A unique indegree-zero state is a mandatory spanning root, so that common case is optimized. A second key minimizes over reflection and simultaneous read/write symbol complementation. For this corpus the ordinary and enlarged cosmetic equivalences yield the same 476 class count.

`corpus/compare_candidate.py` compares full canonical tuples, not only hashes, against all stored byte forms of the same state count; it tries reflection and complementation explicitly. It permits no semantic state merging and therefore establishes only finite graph novelty. Global symbol exchange is included as a strong cosmetic test; it does not preserve the chosen all-zero blank convention by itself.

## Main construction families

| Family | Working states | Mathematical/construction distinction | Current evidence boundary |
|---|---:|---|---|
| Imported James Chang PA209 | 209 | Original compact numerical proof search and register compiler | Imported source/table checks; consult upstream theorem statements |
| U208 Joint/Plain families | 208 | Same source, finite-history fold involving native 172/211 | Written fold arguments and symbolic checks; multiple repeated presentations |
| Imported James Chang PA196 | 196 | Smaller numerical source/compiler | Imported PA implication `Nonhalt -> Con(PA)` does not itself prove the internal converse |
| 196-state rebracketings/layouts | 196 | Decoder reassociation, command variants, zero-closing, register permutations | Many distinct tables; most do not improve state count |
| Original PA195 | 195 | Bundled diagonal emitter; 134 fixed +68 raw readers -7 folds | Ordinary mathematical PA biconditional claimed; 3,700 source sites |
| PA195S/195C | 195 | Separate diagonal head; 67 readers -6 folds; original/cached controllers | Ordinary mathematical calibration and symbolic certificates; 3,673/3,649 source sites |
| M195S8 | 195 | Eight folds require an eight-zero scanner | Accepted scanner repair; rejected 194 precursor explicitly retained |
| PA195DC | 195 | Original bundled diagonal source with cached controller | 3,676 source sites; 134+68-7 |
| Primary PA194 | 194 | Combine 67 readers with seven compatible folds | 3,673 source sites; same complete source as supplied PA195S |
| PA194_AD | 194 | Exchange A/D physical register placement | Separate graph; same logical source; different exact startup |
| Second PA194 allocation | 194 | 68 readers and eight compatible folds | Distinct accepted allocation; do not confuse with the failed scanner quotient |
| PA194C | 194 | Cached-head Shift/MP protocol with 67/7 decoder | 3,649 source sites; repeatedly delivered identical principal table |
| PA194CS | 194 | Symmetric destructive equality shortens Shift | 3,646 sites; extra controller reader compensated by a contextual fold |
| PA194N | 194 | Original Shift, successful MP skips dummy-zero push | 3,654 sites; new proof-command compiler |
| PA194Q | 194 | Exchange the two curried premises of one quantifier-distribution axiom | 79 source-instruction changes; 3,649 sites; explicit proof translation |
| PA194CSZ = PA194X | 194 | Symmetric Shift plus known-zero X decrement at source entry | 3,646 sites; same table in two latest packets |
| PA194F | 194 | Replace final emitter return with known-zero X decrement | Source preservation uses a four-site cut invariant |
| PA194A | 194 | Replace entry return with known-zero A decrement | Source preservation plus exact startup |
| PA194R | 194 | PA194F source with a new 67-reader decoder arrangement | 1,111 source-address paths change; 44 reader subtree types replaced |
| PA194J | 194 | Replace ten unconditional source jumps with proved-zero decrements | 263,180 invariant pairs; 3,646 sites |
| PA194D | 194 | Separate diagonal head `Gamma(A)` becomes `Gamma(D)` | New selector, 69 readers -9 folds; 3,649 sites |
| M4R, M5, M6 | 194 | New decoder and formula-constructor coefficients 4,5,6 | M5/M6 have an additional numerical proof recoding; M4R preserves coefficient-4 source |

The 194-state principal/companion list above has 16 distinct graph classes after merging PA194CSZ/PA194X. `corpus/frontier194.csv` gives all 28 classes, including supplementary and rejected records. `corpus/packet_ledger.csv` covers all 46 top-level packets; the individual file/member locators and byte identities are in `corpus/current/tables.json` and `occurrences.json`.

## What actually changes between the command controllers

The original controller uses store components `(t,w,d,h)`. A successful MP with parameter x sets `b=d+x`, requires `I(t,b)=h`, retains b in the top and D, empties H, and pushes a dummy zero: `(b,[0;w],b,0)`. Its Shift contradiction test is `t+h=1`.

The cached/Combined controller instead returns `(0,w,0,b)` from successful MP and tests the cached H value directly for contradiction. Its proof compiler is correspondingly different. The PA194C constructions are genuine command changes relative to the original primary PA194, but repetitions of the same PA194C table are not new machines.

The no-push PA194N returns `(b,w,b,0)` while retaining the original Shift test. It proves `MP(0)(t,w,0,h)=(0,w,0,0)`, giving a one-command Discard. Its supplied compiler reserves a zero below MP premises and removes it explicitly, accounting for the ten-entry AX interface, the Cantor stack-zero collapse and implication-code-zero alias.

PA194CS changes a local equality test from `(h,1)` to `(1,h)` after rearranging how the cache is restored. The destructive inequality branch clears both operands, so the surviving register state agrees even for arbitrary incoming scratch. This removes three primitive sites. It is already supplied prior art.

## Proof status: PA, iPRA, ordinary proof, and certificates

The user asks for equivalence provable in PA. A missing Lean or iPRA endpoint does not by itself invalidate an ordinary mathematical proof that PA proves the equivalence. Conversely, a packet's claim of such an ordinary proof is not established merely by a successful transition-table or source-simulation check.

The current top-level PA README explicitly says that neither machine-specific iPRA consistency direction has been completed for primary PA194, original PA195 or PA196. The numerous `pa194-*` directories are primarily proof companions for the same pinned primary table: arithmetic coding, source binding, quotient, blank initialization, source coverage and clock composition. They are not 20-plus distinct 194-state machine designs.

The primary PA194 table has SHA-256 `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`. Its 201-control parent, seven-fold quotient, 3,673 source-site coverage and source-clock composition have substantial formalized support. Those results do not complete the machine/refutation translations inside the weak arithmetic endpoint. The imported PA196 result includes an internal PA implication from literal nonhalting to consistency. The complete biconditional requires the other syntactic direction as well; external truth or consistency alone is not a substitute.

The latest five packets consistently state an ordinary mathematical PA-provability argument, explicitly inherited numerical-calculus calibration, universal literal-tape/source contracts, exact full blank startup, and no new end-to-end Lean/Rocq theorem. Their claimed universal contracts cover arbitrary nine natural register values, both decrement outcomes, an affine header gap and every nonempty finite list of natural spare values. The inherited soundness of the symbolic rules and generic loop inductions remains part of the mathematical verification base.

A safe new result must keep four bindings separate and explicit:

1. Syntactic translations between PA refutations and numerical-calculus refutations, formalizable in PA.
2. A finite command compiler linking numerical proofs to the actual source program, with dirty stores, stack tails, zero aliases and early halts addressed.
3. Positive-duration literal-machine simulations of every source outcome, including all simultaneous folds and engine interfaces.
4. Exact blank startup reaching the clean source seed with the entire tape, head and control correct.

## Rejections and why they matter

The old `near194_bad4_k17595.native.tm` is a rejected seven-zero scanner quotient. Its local folds and source CFG can be correct while the physical source scanner misidentifies address structure. The accepted M195S8 adds the needed scanner capacity, losing the apparent 194 count.

The latest PA194R and radix packets retain different rejected source-equivalent jump changes. One literal machine halts after **1,361 startup transitions** before reaching the clean source seed. It can pass all subsequent source contracts. This is a concrete reason to rerun full blank startup for every accepted table rather than infer it from source equivalence or a shared register engine.

Research files labeled `MPH`, `C_I_Z`, `CS_both_zero6`, `PA194CSZ_A3/A5/A6`, and `Gamma(D)_CSZA` are useful candidate inputs but must retain their individual evidence scopes. The J/D packet explicitly says that its full independent physical replay was performed for its two principal tables, not every supplementary sibling.

## Opportunities remaining after comparison

The common accounting target is an effective axiom-decoder cost of 59 rather than 60 with the standard 134-control scaffold, or an independently valid saving in that scaffold. Raw reader count alone is not enough: some successful allocations use 67/7 and others 68/8 or 69/9. Reassociation and contextual folds must be checked jointly, including every incoming context in the final folded table.

Source length and state count are only loosely related. NEG18 reduces the complete source to 3,441 primitive sites but its reported physical machine has 197 states. Shorter code can introduce new subtrees or break scanner constraints; fewer instructions is not a certificate of fewer controls.

The newest independently proved modifications occupy separate dimensions: emitter premise exchange, diagonal-head relocation, constructor coefficient, cached/no-push controller, known-zero decrement replacement and physical register layout. Composing compatible changes is a plausible route to a materially different 194-state fallback. It is not automatically a one-state reduction, and the literal table should be checked against all 28 current classes, including experimental inputs. In particular, a no-push controller combined with the exchanged-premise axiom emitter or a coefficient-5/6 emitter would need a fresh source/interface binding, universal physical verification and blank startup; the underlying command and logical transformations are available as separate inherited ingredients.

## Audit files

* `corpus/audit_census.py`: reproducible read-only corpus scanner.
* `corpus/compare_candidate.py`: exact tuple novelty comparison against the saved corpus.
* `corpus/current/summary.json`: all observed counts and scope.
* `corpus/current/tables.json`: every recognized byte identity, graph key and occurrence path.
* `corpus/current/occurrences.json`: every traversed numeric table occurrence.
* `corpus/current/archives.json`: all nested archive identities and references.
* `corpus/current/literal_tables/`: exact recognized tables with at most 196 states, named by SHA-256.
* `corpus/packet_ledger.csv` and `.json`: all 46 delivered research packets.
* `corpus/frontier194.csv` and `.json`: all 28 current 194-state classes and evidence labels.

All paths and byte identities above were read from the pinned snapshot. No source repository file was changed by the audit. Corpus claims are distinguished from independent semantic proof checks throughout.
