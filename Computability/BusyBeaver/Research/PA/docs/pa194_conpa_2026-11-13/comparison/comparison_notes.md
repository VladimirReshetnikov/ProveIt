# PA machine comparison at 5ed5a41fa5932433111eea096311364c6087e8e3

## Scope and fresh census

All 32 top-level ZIP archives in `docs/incoming` were read from this exact Git commit, with nested ZIPs recursively traversed once per byte identity. Every direct `.tm` file in `Computability/BusyBeaver/Research/PA` was included. The inventory recognizes complete numeric binary `.tm` and `.txt` transition tables with one undefined terminal label. It does not parse tables embedded solely in arbitrary source code or JSON; a no-halt four-state synthetic control is excluded. Two other disconnected synthetic controls are recognized but excluded from the root-free graph classification.

Fresh results: 45 distinct ZIP payloads, 73 ZIP references, maximum nesting depth 8, 25,069 file occurrences within distinct archive payloads, 2,360 recognized transition-table occurrences, 582 byte-distinct tables, and 421 classified root-free action-preserving graph classes. These counts include ancestors, experiments, duplicates, and rejected tables; they are not counts of established consistency machines. All 40 distinct archive bodies in the previous 27-archive snapshot hash-match this new census, so the preceding archive comparisons apply to unchanged inputs.

The important frontier has **37 occurrences of 195-state tables, 14 byte strings, and exactly nine root-free graph classes**. Three classes are positive manuscript constructions; six are rejected or diagnostic. No 194-state table occurs in the recognized corpus. The `.tm` table files with fewer states are synthetic controls, not consistency constructions.

Artifacts in this package:

- `comparison/census.py`: the fresh independent inventory and canonicalization script (read-only repository).
- `comparison/census.json`: complete archive, member, hash, table, and class inventory.
- `comparison/existing195_classes.json` and `comparison/existing195/`: the nine classes and all 14 literal byte forms.
- `verification/independent/`: the new machines' independent literal checks, reference tools, and recorded receipts.

Canonicalization preserves the read-symbol labels, written bits, L/R directions, and unique halt. It minimizes deterministic read-0-before-read-1 BFS serializations over every working control from which the complete graph is reachable. Thus different canonical forms cannot be explained by a change of finite-control names or designated start. This particular hash serialization differs from previous archive hashes, but is internally consistent.

## The three positive 195-state designs

| Family | Source program | Allocation | Source instructions | Symbolic source branches | Exact blank startup | Literal dense table SHA-256 |
|---|---|---:|---:|---:|---:|---|
| Original PA195 | Bundled diagonal-vacuity `diagonal191`; original controller | 134 fixed + 68 AX readers − 7 folds | 3,700 | 4,815 | 58,154 | `5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455` |
| 195S | Separate diagonal head `separate190`; original controller | 134 + 67 − 6 | 3,673 | 4,780 | 58,154 | `30246dfe308e4b406e3bbf461f511530d49112974f90972327cf950ba41f919f` |
| 195C | Same separate190 AX body; cached-head Shift and MP controller | 134 + 67 − 6 | 3,649 | 4,749 | 57,922 | `72ccfe50005110eb302f34cbec4110521ca6971d7ef5bca8d959ff39f0661011` |

Original PA195 is in `docs/incoming/pa195_conpa_2026-11-13.zip`, primary member `pa195_conpa/pa195/pa195.tm`. 195S and 195C are in `docs/incoming/PA195_ConPA_research_2026-11-14.zip`, primary members `pa_consistency_research/construction195/rebuilt_195S/machine.dense.tm` and corresponding `rebuilt_195C`. All use binary, two-way infinite, blank tape, working labels 0–194, start 0, separate halt 195; the native forms start at 74 and halt at 254.

The original saves a state through an additional compatible history-sensitive fold, without reducing its 68-node allocation. 195S/C instead save a raw reader node while preserving six compatible folds. These are different physical optimization mechanisms. The diagonal191→separate190 word conversion deletes exactly the zero-based macro token 184 (`node65`), which removes the outer composition that bundles Gamma into the gate. This observation supplied an intermediate cross-grammar experiment before the final 194-state construction.

### Exact local-fold evidence for original PA195

The original archive supplies a 202-to-195 quotient with 28 exhaustive history/read-bit cases: ten length-1, seventeen length-3, one length-5. The finite endpoint checks preserve the entire two-cell window, head displacement, and projected control. All incoming rows establish the required history bit, ordinary rows commute with projection, and the start is not exceptional. Consequently positive one-step simulation extends to every full tape and hence halting equivalence by determinism.

The PA directory's `pa195-quotient`, `pa195-all-tape`, `pa195-translate`, `pa195-ordinary`, `pa195-simulation`, `pa195-control`, `pa195-generic-trace`, and `pa195-global` directories are **proof layers for this one original table**, not eight additional 195-state designs. `pa195-global/README.md` says that the global theorem proves halting equivalence between the native unfolded 202-state and folded 195-state tables, from native 74 on every tape. Its theorem is about ordinary natural-number traces. It does not export a PA-internal consistency biconditional or dense-table conjugacy theorem.

`pa195/ipra/README.md` is equally explicit that the two machine-specific reductions remain hypotheses in `PA195Endpoint.lean`/`PA195ForwardGG.lean`. Its table binding, primitive recursiveness, standard-model identification, and conditional assembly should not be described as a completed iPRA/PRA/PA proof.

This formalization boundary does **not** mean that the supplied manuscripts contain no ordinary mathematical argument. The original PA195 report's `sections/pa_calibration.tex` contains a detailed mathematical proof of the PA-provability statement: diagonal equality-interface replacement templates; a uniform finite bit-comprehension proof supplier; a syntactic calculus-to-PA refutation compiler; a canonical proof-stack invariant handling Cantor pair(0,0)=0; positive command/source/physical simulations; and a bounded trace-determinism argument. I found no immediate logical counterexample in that argument. The newest 195S/C report composes its physical preservation with the separate-head parent's stated mathematical calibration. A result preserving these machines may inherit that mathematical endpoint while candidly stating that no new kernel-checked PA theorem was produced.

## Six rejected 195-state classes

| Diagnostic family | Reason the claimed simulation is not accepted | Distinguishing raw SHA prefix |
|---|---|---|
| Two-rotation quotient | 93 recorded primitive-contract failures | `82982544cecbb684` (native), `ab74caa51f260159` (dense) |
| `warm_physical_61_8047` | 714 failures; site 1111 reaches a four-transition cycle after 26 transitions | `178fe861dc4a1cf8` |
| `extended_physical_61_12085` | 777 recorded primitive-contract failures | `22d0fae804421381` |
| Seven-zero scanner regrouping | Wrong clean frame at site 1003; adding scanner state repairs it to 196 | `324811f795fc1f4c` |
| Short-scanner deletion | 96 unrestricted failures; invariant-conditioned seed return also wrong | `5cbbd2a0d688374a` (native), `6f9cd148718c7225` (dense) |
| Zero-jump/helper fold | Wrong successor and wrong incremented register at site 26, reproduced on blank computation | `9452415fa9c82887` |

A failed intended simulation does not prove that a table could never possess the same blank-tape property under another interpretation. It does disqualify that supplied certificate as a successful construction. Two separately rejected **196-state** Shift layouts are stronger negative controls: both actually halt on blank tape at exactly 43,563 steps, with a Lean-checked finite trace in the repository.

## Archive-by-archive contribution ledger

All names below are directly under `docs/incoming` at the pinned commit. The first 27 were already at `906367250a7f96c923147b10df392294bced7be5`; the final five are the current additions. Counts and statuses below are descriptions of the supplied construction/evidence, not newly proved logical endpoints.

| Archive | Main contribution and comparison consequence |
|---|---|
| `Below_U208_Research_2026-10-29.zip` | Full-frame windows, offset quotients and guarded pruning; source 3,909→3,904; no accepted below-208 table. |
| `ConPA_below208_research_2026-10-29.zip` | Finite-model role-collapse objection, 279,936 fixed-association parameter cases, fold synthesis; no sub-208. |
| `PA_consistency_TM_research_2026-11-13.zip` | 159-node five-zero source and 157-node combined representation; exact source CFG checks, no smaller physical allocation. |
| `U208_ConPA_2026-10-29.zip` | Particular native172/211 history fold reduces a U209 parent to U208. |
| `U208_ConPA_Conditional_Context_2026-10-29.zip` | Conditional-entry proof; same two original U208 graph classes. |
| `U208_ConPA_Entry_Context_2026-10-29.zip` | Full entry-context proof; same two original classes. |
| `U208_ConPA_History_2026-10-29.zip` | Finite-history proof with four exceptional blocks; same original saving. |
| `conpa_tm_comparison_and_reduction_search.zip` | Experimental MP-result-in-H and MP-without-zero-push 196 variants; rejected Shift layouts halt at 43,563. |
| `conpa_tm_comparison_and_search.zip` | A/D register-swap 196; rejected two-rotation 195 fails 93 contracts. |
| `conpa_tm_study_2026-11-13.zip` | Combined196 = H-only Shift + MP-result-in-H: 3,788 sites, 4,928 contracts, 57,922 startup; direct-negation 197 too. |
| `pa196_research_2026-11-13.zip` | Exact 157-node representation of 3,812-site original program; loses contextual sharing, no physical reduction. |
| `pa208_research_2026-10-29.zip` | Eighteen further helper layouts; 27 designated U208 presentations give 20 graphs, not two. |
| `pa_below196_research.zip` | Eight equivalent gates, membership/equality orientations, broad grammar searches; original201-token best 196. |
| `pa_consistency_comparison_2026_11_13.zip` | Modal-head/explosion split, twelve semantic compositions, joint gate; physical results 196–200. |
| `pa_consistency_comparison_and_new196_2026-11-13.zip` | Diagonal196 (3,700 sites), Separate196 (3,673), Scanner-best196; principal logical/source parents of positive195. |
| `pa_consistency_reduction.zip` | Rebracketed196, H-only196, integrated gate 203/206; two failed 195 diagnostics. |
| `pa_consistency_research.zip` | Two exact158-node sources and repaired196; nominal195 needs added scanner state. |
| `pa_consistency_research_2026-10-29.zip` | Inductive 3,909→3,904 specialization; no physical sub208. |
| `pa_consistency_research_2026-11-13 (2).zip` | Twelve-rotation196, diagonal198, successful-MP halting-source experiment; no sub196. |
| `pa_consistency_research_2026-11-13.zip` | Earlier diagonal-vacuity199 and short-negation197. |
| `pa_tm_comparison_and_reductions.zip` | Two rotated196 graphs; distributed-gate198 with 3,773 source sites. |
| `pa_tm_extended_research_2026-11-13.zip` | Four closing-decrement variants and stronger zero invariants; all change the same row, hence not stackable. |
| `pa_tm_research_2026-11-13 (2).zip` | Zerojump196 (4,959 contracts, 58,402 startup); parity/disequality experiments; rejected195 fails source26. |
| `pa_tm_research_2026-11-13.zip` | Shorter-path196 and independent physical checking; detailed direct PA reverse-translation strategy. |
| `pa_unary_power_cover.zip` | Unary weak-covering theory and PA proof translations; no new compiled small table. |
| `u208_comparison_research_2026-10-29.zip` | Original two-class audit; weak/exact schemas; rejected207. |
| `u208_research_2026-10-29.zip` | Primary/alternative U208 and symbolic contracts; same initial history fold. |
| `pa195_conpa_2026-11-13.zip` | Positive original PA195: unchanged diagonal191 program, 68−7 reader allocation, detailed ordinary PA calibration. |
| `PA195_ConPA_research_2026-11-14.zip` | Positive195S and195C: unchanged separate190 AX word, 67−6 readers; full source/runtime/startup certificates plus independent literal-tape audits. |
| `pa_consistency_cross_archive.zip` | Four new196 combinations: diagonal/separate AX + Combined controller, each optionally zero-jump; sites 3,676/3,649 and startups57,922/58,168. |
| `pa_consistency_reduction_audit_2026-11-14.zip` | Four further experimental MP-H compositions, two196 and two197; parameter/order/association/helper/scanner negative searches. |
| `pa_consistency_research_2026-11-14.zip` | NEG18: `INC7; INC7; node64`, 18-site encoded negation; complete source3,441 and197 states (134+68−5); independent macro and scratch-zero proofs. |

## Why simple savings cannot be added

James Chang's PA209 (3,948 source sites, pinned `69d98241a721ead20b4f0b17df9062950b40fbfe`) and the U209 parent of U208 are distinct machines. PA196 (3,812 sites, upstream `407cdc356f6b586635e71ac92be394255f4bfea4`) already includes transposed quantifier coding, a revised equality interface, changed head order, and six reader folds. Its published count is 36 arithmetic engine + 13 leaf routing + 147 readers = 196. Subtracting an already applied fold again is incorrect.

Raw source-site savings do not automatically save physical controls. A 157-node DAG may need more reader controls than a 159-node DAG because a useful contextual helper disappears. Pairwise potential folds do not automatically compose: helpers may themselves be changed by a second fold. Final-table simulation for the entire fold set is necessary. The newest195 search specifically used exact simultaneous compatibility rather than an optimistic maximum matching.

## Relevant prior negative coverage (not lower bounds)

- PA196 literal single-control contractions with at most one patched retained row were checked across ~59 million patch choices under successive local invariants, including radius-six abstract blank-window reachability. None passed the restricted 16-step/radius-two endpoint template.
- Exact original source reassociations: 1,037 individual rotations; 161 global first rotations; 26,083 second pairs; constrained 314,692 third rotations; no DAG reduction below159 in that stated family. Later incoming work finds other157/158 layouts but no automatic smaller tape machine.
- Both fixed diagonal191 and separate190 associations: all46,656 independent six-head role permutations each; all720 orders of six unrestricted heads each. The original choice uniquely minimizes the matching bound62; others are worse. This does not rule out different associations with reordered heads.
- Joint modified-word searches included role permutations, head order, curried antecedent exchanges, equality reversal and/or Gamma placement; none of the recorded older runs found a strict reduction. Thus a changed axiom-head order alone is not a previously untouched proposal.
- Full-prefix, two-row pure-reader fold synthesis: Separate196 6,555 pairs and Scanner-best196 6,441 pairs, up to100 local steps, no survivor; a known202→201 fold is a positive control.
- Deleting a scanner state requires more than eliminating interior AX zero runs. The first source site's `000000` path and transient increment zeros remain hazards. Two cost-free exterior rotations preserve all contracts but still fail the shortened scanner at site0.

## New 194-state construction and independent audit

The new primary `PA194` keeps exactly the 3,673-site, 4,780-branch separate-head source program of 195S and the original physical register map `(6,2,0,4,3,7,8,5,1)`. It changes the AX reader grammar to obtain 67 raw reader controls and seven simultaneously valid folds. Its exact allocation is **134 fixed controls + 67 raw AX readers - 7 folds = 194 working controls**. The existing 195S design has the same number of raw readers but only six compatible folds; the original PA195 has seven folds but 68 raw readers. The new construction achieves both savings together. The 190-token macro word and all 3,673 resolved instructions remain exactly unchanged, so the improvement does not depend on a new proof calculus or logical calibration.

The seven native fold redirects are `2016→2052`, `2018→2027`, `2022→2032`, `2024→2046`, `2037→2015`, `2055→2019`, and `2060→2014`. They are checked as one complete final table. The dense primary table has SHA-256 `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`; the native table has SHA-256 `e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54`.

A second 194-state construction, `PA194_AD`, keeps that reader allocation and logical source, and changes the physical register map to `(6,2,0,3,4,7,8,5,1)`. This swaps the physical positions of logical A and D through exactly three native target changes, at rows 17/1, 144/1, and 161/1. The arithmetic engine rows are unchanged. Register permutation already appears in a supplied 196-state construction; the contribution here is its verified composition with the new 194-state reader. This is not a claim to have invented register permutation.

| New family | Working states | Source sites | Source branches | Independent symbolic steps | Maximum symbolic steps in one branch | Exact blank startup |
|---|---:|---:|---:|---:|---:|---:|
| Primary `PA194` | 194 | 3,673 | 4,780 | 1,078,198 | 397 | 58,154 |
| Companion `PA194_AD` | 194 | 3,673 | 4,780 | 1,078,321 | 397 | 58,122 |

Both native tables passed independent universal literal-tape checking, including a complete blank startup comparison and exact native/dense conjugacy. The independent verifier reconstructs four generic list-sweep lemmas from each new literal table and uses no arithmetic-box oracle. It covers arbitrary natural values of all nine registers, every decrement outcome, an arbitrary finite nonempty spare list, and header distance `48+n` for arbitrary natural `n`; the zero run after source path `p` has length `48+n-|p|`. Every symbolic physical duration has nonnegative affine coefficients and strictly positive constant; the minimum constant is three.

Both machines start from a blank tape, reach the source frame at native control 84 (dense control 24), head -2, source site 25, logical registers `[2,0,0,0,0,0,0,0,0]`, header distance 48, and 26 one-valued spares. The complete finite nonzero tape support is compared with the expected seed, with zeros elsewhere. The difference of 32 startup steps between the two tables is consistent with their changed register routing.

The primary and companion have distinct root-free canonical control graphs, so neither an arbitrary control relabeling nor a changed designated root identifies them. They are not related by global left/right tape reflection either: their action counts are both `(0,L):49`, `(0,R):170`, `(1,L):29`, `(1,R):140`, which reflection would exchange. Every working control reaches the complete graph, and both machines have 194 ordinary action-bisimulation classes. No earlier 194-state table appears in the recognized pinned corpus. These facts certify graph differences; they do not establish that 194 is minimal among consistency machines.

Exact source references, graph hashes, transition-table hashes, individual branch contracts, list-lemma traces, startup seeds, and observed verification results are included under `verification/independent/`. The mathematical positive-simulation argument and consistency calibration are given in the report. No newly kernel-checked end-to-end PA theorem is claimed.
