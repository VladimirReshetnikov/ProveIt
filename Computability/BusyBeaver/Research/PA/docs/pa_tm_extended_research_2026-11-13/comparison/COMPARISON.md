# Comparison of the supplied PA consistency machines

## Source identities

The source snapshots are ProveIt `f7d2482e35cf2f8f3bd03b5a82387ad999243548`, James Chang's current BusyBeaver `407cdc356f6b586635e71ac92be394255f4bfea4`, and its requested predecessor `69d98241a721ead20b4f0b17df9062950b40fbfe`.

All eleven ZIPs currently present in ProveIt's `docs/incoming` were extracted. Five are construction packages containing nine designated final 208-state tables. Five more are comparisons or further searches, and one (`pa_unary_power_cover.zip`) is a logical-calibration and numerical-stream package. The later research packages explicitly report that they did not obtain an accepted machine below 208 states. Their exploratory files named `rejected207` must not be treated as constructions.

## Exact machine census

The nine designated tables in the five U208 construction packages have exactly two rooted, action-preserving transition-graph isomorphism classes. This was independently recomputed by breadth-first canonical numbering, taking read-zero before read-one and keeping the halt distinct. `input_manifest.json` supplies every retained file hash and the archive inventory; `reproduction.json` supplies every canonical state map. Run `python3 compare_all.py --output reproduction.json` to recompute the comparison.

| Construction package | Class A final table | Class B final table |
| --- | --- | --- |
| U208_ConPA_2026-10-29 | `machine/u208.tm` | None |
| U208_ConPA_Conditional_Context_2026-10-29 | `machine/u208.tm` | `alternative/u208.tm` |
| U208_ConPA_Entry_Context_2026-10-29 | `machine/u208.tm` | `machine/u208_compatibility.tm` |
| U208_ConPA_History_2026-10-29 | `machine/u208.tm` | `machine/compatibility_variant/u208.tm` |
| u208_research_2026-10-29 | `machine/variant_plain/u208.tm` | `machine/u208.tm` |

Each table has 208 working states and 416 rows. There are five presentations of class A and four of class B. Their canonical hashes depend on the exact JSON serialization in the fresh comparison, so they need not equal canonical hashes using a different serialization in an older report. The underlying state bijections are the meaningful comparison.

All nine apply the same final conditional-history identification of native roles 172 and 211. The parent reaches 172 with the two bits `10` immediately before the head. When 211 scans zero, its preceding bit is one. A shared read-zero branch moves left into helper 217 in the Joint labeling (helper 214 in the other layout). Four complete local blocks have lengths 7, 1, 3, and 1. These are alternative presentations of a single deletion, not independently additive reductions.

The two classes also implement the same 3,909-occurrence register program. Their source addresses differ because of tree association. The counts and source equivalence reported in the retained comparison packages are 1,558 increments, 1,175 conditional decrements, 80 breaks, 1,095 continues, and one halt; 5,083 nonhalting source edges; and 5,084 branch contracts. Class A has maximum source depth 42, class B 41. Both use 197 distinct syntax subtrees when leaves are counted.

## James Chang's branch

The requested 209-state table has SHA-256 `0610d978675320f0b4b1ef34619dcd3daa5912632d7037e200dfcc70954fea51`; its literal labels are the 209 elements of `{0,...,213} \ {50,122,150,157,205}`, with halt 215. This is a different machine from the U209 parents embedded in the U208 packets. A shared number in an archive name does not identify a transition table.

The current 196-state table has SHA-256 `e8bbccd4cfa325251ca95066db116b5aa766e404b0971c33c02772be1c3617a8`, contiguous working labels 0 through 195, and halt 196. It has 392 rows, a 58,154-step blank startup, and 3,812 source occurrences. Its quantifier constructor exchanges the arguments of Cantor pairing. It removes the old primitive-equality transitivity head, adds guarded equality vacuity to the separation gate, and rearranges/permutates the surviving heads to improve sharing. The AX body contains 201 macro items and 68 distinct internal macro-tree nodes, read by 62 states. Its complete source has 159 internal nodes read by 147 states, together with 13 leaf routers and 36 engine states.

The literal-to-native maps in the upstream Lean conjugacy files make the comparison exact. Freshly converted tables are `inputs/pa209.native.tm` and `inputs/pa196.native.tm`. They share 134 working-state labels; 265 of their 268 common rows agree exactly. The three changed common rows are:

| Native row | 209-state action | 196-state action |
| --- | --- | --- |
| 164, read 0 | 0 L 311 | 0 R 77 |
| 190, read 1 | 1 L 308 | 1 R 99 |
| 101, read 1 | 1 R 115 | 1 R 1367 |

The last row enters the replacement AX body. The first two bypass obsolete distinguishing controls. The 196 construction removes 75 old states and adds 62 states in the 1300-plus range, giving the net reduction of 13. Both native 172 and native 211 are already absent. Consequently the U208 deletion cannot simply be pasted into the 196 transition table.

## Evidence boundaries for the PA statement

Both James Chang papers explicitly separate an external search-soundness result from the internal PA refutation-transport result. The current `docs/result.md` lists the internal theorem as `PA ⊢ N → Con(PA)`, where `N` is the exact nonhalting sentence. It does not list the reverse internal implication. External soundness under consistency and two-sided independence do not by themselves establish an internal biconditional. Any claimed `PA ⊢ N ↔ Con(PA)` for a reduction of this machine needs either a separate proof of the missing direction or an explicit account of the additional upstream formalization being used.

By contrast, the U208 manuscripts assert the biconditional after composing their retained ordinary mathematical U-to-PA interpretations and proof-search calibration. They also explicitly disclaim a new end-to-end Lean, Rocq, MM0, or exported PA certificate. This difference in verification status is substantive and should be preserved in the final report.

## Portable ideas and fresh searches

The below-208 work contributes context-dependent state sharing, shared selector synthesis, head-offset representations, source-conditioned invariants, complete primitive-endpoint searches, and careful rejection of invalid tree rotations. None is a state-count lower bound. A shorter source or fewer DAG nodes does not, by itself, provide a smaller physical table.

The two particularly concrete source specializations transfer to the current 196 source: the register-1 cleanup loop beginning at source ordinal 3773 always sees zero, and the register-6 test at ordinal 7 always sees zero. Three primitive occurrences are unreachable. Removing the two zero tests and their unreachable bodies gives 3,807 occurrences. An independent trit reachability analysis found the necessary guards from the actual candidate-2 source seed, but the straightforward specialization increases syntactic sharing cost. Actual physical layouts remain a separate obligation.

Fresh all-natural replay of the unmodified PA196 table against the flattened current source completed 4,959 branch contracts and exercised all 392 rows. This used the inherited unary/list symbolic engine with the current transition table as data; it is independent executable mathematical evidence, not a new kernel proof. The first all-natural contract rejects the tempting shortening of the origin scanner by removing native state 34. The current maximum source zero run is still six, and transient instruction paths matter.

Fresh bounded searches on the 196 table also checked 33,540 head-offset aliases, 53 two-fold/shared-new-selector combinations, and 122 broader two-fold driver combinations, without a survivor. A complete primitive-endpoint regression screen considered 366,912 one-row state folds against 14,877 sampled full frames; ten passed targeted cases and all failed the full suite. These negative results concern their finite search families only.

### Final classification of the additional source experiments

The count of source leaves is not the count of Turing-machine states. The following are experimental allocations, not accepted reductions of the blank-tape machine. The exact count and hash receipts are in `search_receipt.json`.

| Source experiment | Source occurrences | Working states in straightforward allocation | Result |
| --- | ---: | ---: | --- |
| Remove the always-zero register-6 test and its unreachable loop body | 3,810 | 198 | All 4,956 arbitrary-natural primitive contracts pass. Blank startup is uncalibrated: neither the original clean seed nor a decoded candidate-2 frame was found within 1,000,000 literal steps. |
| Remove the always-zero register-1 cleanup test and unreachable body | 3,809 | 202 | Rejected by a full-frame primitive check at new source ordinal 3796. |
| Apply both prunings | 3,807 | 204 | Rejected at new source ordinal 3794. |
| Apply both prunings and remove the redundant final jump | 3,806 | 204 | Rejected at new source ordinal 3794. |
| Specialize the first guard to the actual test H=1, and remove its artificial increment of register 6 | 3,806 | 199 | The source guard has the required elementary behavior, but the straightforward table is rejected at source ordinal 126, the zero branch of CD8. |

The last specialization uses the upstream `NIPGuard` and `S36Lift` contracts: immediately before the final increment, register 6 is zero and register 5 contains the sum to be tested; the increment sets register 6 to one, and the generic comparator tests equality. A direct test of register 5 against one can therefore replace the increment-plus-comparator sequence. However, the old comparator is also used by the MP and AX gates. Its extensive DAG sharing makes the shorter specialized source more expensive: it has 185 distinct source subtrees including leaves, against 182 in the original. A bounded enumeration of 45,360 six-leaf guard trees found five that pass the finite guard filter, all with a best count of 185. This is not a lower bound on all possible guards or implementations.

The rejected physical allocations illustrate another constraint. Several apparent decoder states also provide transient return routes during a primitive instruction. Preserving the source CFG and successfully reading every stored source prefix does not prove that those return routes remain valid. This is why full arbitrary-register primitive contracts and a separate literal blank-startup calibration are both required.

A further beam search of physical tree rotations outside the replacement AX states examined 3,725 distinct transition tables through depth 15, with beam width 32. Every explored source rotation was checked against the exact source CFG. No table obtained an identical-state fold or reduced the maximum source zero run below six. This is a bounded negative experiment, not a global minimality claim.

No experiment in this comparison produced an accepted blank-tape machine with fewer than 196 working states.
