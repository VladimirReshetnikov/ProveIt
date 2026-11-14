# Current PA consistency-machine corpus: comparison and proof boundaries

Snapshot: `VladimirReshetnikov/ProveIt@768c2be1a8e4d2fcf8aa3443c7b0f084d145734c`.
All state counts exclude the unique terminal halt control and refer to a binary, single, two-way tape with all-zero initial contents unless a rejected/experimental entry says otherwise.

## Scope and fresh inventory

The fresh census traversed all **36** top-level incoming ZIPs (**245,340,389 bytes**), recursively reading each byte-distinct embedded ZIP once. It encountered 77 archive references representing 49 distinct ZIP payloads, with maximum nesting depth eight and 26,258 file occurrences inside the distinct payloads. It additionally inspected the direct `.tm` files under `Computability/BusyBeaver/Research/PA` (14 recognized complete tables).

The parser recognizes complete numeric five-column binary tables in `.tm`, `.txt`, `.tsv` and `.csv` members: two rows per working control, write symbol 0 or 1, direction L or R, and exactly one terminal target with no outgoing rows. It does not recover tables encoded only in arbitrary Python/Lean source, JSON or prose. A no-halt four-state synthetic control fails this declared parser convention; two disconnected six- and nine-state controls have no spanning root and are omitted from root-free graph classification. All proposed frontier machines are represented by literal tables recognized by this parser. No archive-reading errors occurred.

| Count | Fresh result |
|---|---:|
| Recognized literal-table occurrences | 2,519 |
| Distinct literal byte strings | 606 |
| Root-free action-graph classes | 437 |
| 194-state byte forms / graph classes | 7 / 4 |
| 195-state byte forms / graph classes | 25 / 15 |
| 196-state byte forms / graph classes | 163 / 99 |
| 208-state byte forms / graph classes | 177 / 142 |
| 209-state byte forms / graph classes | 20 / 13 |

These are corpus counts, **not counts of correct PA-consistency constructions**. They include ancestors, diagnostic experiments and explicitly rejected tables. The only recognized tables below 194 states are explicitly synthetic six- and nine-state controls; none is a proposed consistency machine. No recognized table has between 10 and 193 working states. These are inventory statements, not lower bounds.

Canonicalization preserves the read-bit labels, written bits, L/R directions and the unique halt. It chooses the lexicographically least compact-JSON breadth-first serialization over every working root reaching all working states, processing read bit zero before read bit one. Thus equal root-free forms disregard finite-control names and designated start states. The complete definitions, hashes and archive/member locators are in `census/census.json` and `census.py`.

The 32 archives reviewed by the supplied primary PA194 packet are **all byte-identical** in this current 36-archive snapshot. Its archive-contribution ledger therefore remains applicable to those unchanged inputs. We read the new packets and their recorded evidence, and freshly traversed and canonicalized the whole current corpus. The four additions are the two PA194 packets, PA195DC, and the PA195 follow-up containing M195S8 and a rejected 194 quotient. The full current archive ledger and exact hashes are in `archive_ledger.json` / `.csv`; `archive_ledger.tex` is a report-ready longtable. Narrative evidence is reported at its actual level; the census does not independently prove all manuscript theorems.

## All existing positive 194-state families

There are **three** positive manuscript constructions at 194, not merely several renamings of one machine.

| Family | Allocation | Source sites / branch contracts | Exact startup | Dense literal SHA-256 |
|---|---|---:|---:|---|
| Primary PA194 | 134 + 67 - 7 | 3,673 / 4,780 | 58,154 | `4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f` |
| PA194_AD | 134 + 67 - 7 | 3,673 / 4,780 | 58,122 | `27613aa92da79ba2ec6e2e88e0ac909fda218e06495ecc0af27201eac0e26c8f` |
| Eight-fold PA194, second packet | 134 + 68 - 8 | 3,673 / 4,780 | 58,154 | `9087d70fc0e1878c38ceff928e6e7e0999c86b6efed00a5ec353821c00641c87` |

The first two are `pa194_conpa_2026-11-13.zip!pa194_conpa/construction/tables/pa194.tm` and `pa194_AD.tm`. The third is `pa194_conpa_2026-11-13 (2).zip!pa194_conpa/pa194/pa194.tm`.

All three retain the same separate 190 axiom-emitter word and the original command controller. The first achieves both the 67-reader allocation and seven simultaneous folds. The third accepts one additional raw reader but gains two additional folds relative to the 67-reader/six-fold195S pattern. The AD companion exchanges the physical positions of two logical registers, changing three native transition targets. All three have different root-free action graphs; neither an arbitrary control relabeling nor a changed initial control identifies them.

The fourth recognized194 graph is explicitly rejected: `pa195_followup_research.zip!pa195_followup/evidence/rejected_candidate_194/near194_bad4_k17595.native.tm`. Its eight local folds are compatible, and its 3,700-site CFG is correct, but a seven-zero address run triggers the old return scanner. The first failed raw runtime contract is source ordinal 1,003, on the zero branch of logical register 1 (physical 2), after 1,309 successful earlier contracts. Adding one scanner control repairs it to M195S8. The local quotient alone therefore does not establish a correct interpreter.

## The entire 195-state frontier

Six graph classes are positive main or intermediate manuscript constructions. Three further classes are auxiliary physical/search witnesses with more limited endpoint claims. Six classes are earlier rejected diagnostics. This totals all 15 recognized195-state graph classes.

### Positive main or intermediate manuscript families

| Family | Emitter and controller | Allocation | Sites | Contracts | Startup |
|---|---|---|---:|---:|---:|
| Original PA195 | Bundled diagonal191; original controller | 134 + 68 - 7 | 3,700 | 4,815 | 58,154 |
| 195S | Separate190; original controller | 134 + 67 - 6 | 3,673 | 4,780 | 58,154 |
| 195C | Separate190; cached-head Shift and MP-to-H | 134 + 67 - 6 | 3,649 | 4,749 | 57,922 |
| Separate195 intermediate in second194 packet | Separate190; different association; original controller | 134 + 67 - 6 | 3,673 | 4,780 | 58,154 |
| PA195DC | Bundled diagonal191; cached-head Shift and MP-to-H | 134 + 68 - 7 | 3,676 | 4,784 | 57,922 |
| M195S8 | Bundled diagonal191; original controller; longer scanner | 135 + 68 - 8 | 3,700 | 4,815 | 59,164 |

The exact dense table hashes are:

| Family | Dense literal SHA-256 |
|---|---|
| PA195 | `5c6afd87f7c4f24d9ad8e9e302cc21df14b6f2e3715d03322a75463a431d8455` |
| 195S | `30246dfe308e4b406e3bbf461f511530d49112974f90972327cf950ba41f919f` |
| 195C | `72ccfe50005110eb302f34cbec4110521ca6971d7ef5bca8d959ff39f0661011` |
| Separate195 intermediate | `f5300673492372f70b72fbbaec819593acf922981c257604fb3167ff23e55f2e` |
| PA195DC | `e5cc1b2cb374fa4342070e95d8bdfd60c1bb845e7a52d44857bdee937bba7938` |
| M195S8 | `df6ec639713c4ae7bb3656e59c833dd55ca6336a46bea8327eca639341b34662` |

The intermediate separate 195 is physically distinct from 195S despite having the same numerical allocation and source. Its README, `receipt.json` and source artifact consistently identify separate 190/3,673 sites/4,780 contracts. A row of the second194 report instead calls it a diagonal3,700-site layout; this is a clerical inconsistency in that row, not the actual construction. The table above follows the concrete artifact.

The original PA195 packet contains the central detailed ordinary argument for the PA-provability biconditional. Its later relatives supply source/calculus/physical preservation and compose with that calibration. None of these manuscripts claims a newly compiled end-to-end Lean/Rocq theorem for its complete PA biconditional.

### Auxiliary 195-state witnesses

* `quotientcross.best.tm` in the primary194 packet is a195 endpoint of a specified finite sequential local-quotient search. The search closes after 192 distinct tables. It is research evidence rather than a separately delivered complete PA-consistency construction.
* PA195R in `pa195_diagonal_combined_2026-11-13.zip/search/annealing/secondary195` swaps the two unrestricted parameter roles of the restricted rho8 head. Its allocation is134+69-8=195. Its4,815 physical contracts,3,700-site source,32 local cases and58,154-step startup pass; preservation of the head family is explained, but it remains an optional secondary witness rather than that report's main arithmetic endpoint.
* PA195N in the sibling `negative_gamma195` folder replaces `Gamma(A) = A -> U(A,A)` by `(A -> 1) -> U(A,A -> 1)`. It has197 macro tokens,3,794 sites,4,937 contracts,58,154-step startup and134+71-10=195 controls. Its physical checks pass. The additional positive/negative vacuity calibration is explicitly separated from the finite checks and is not a newly kernel-checked endpoint.

### Six rejected 195-state diagnostics

| Family | Recorded failure |
|---|---|
| Two-rotation quotient | 93 primitive-contract failures |
| `warm_physical_61_8047` | 714 failures; source 1111 reaches a four-transition cycle after 26 transitions |
| `extended_physical_61_12085` | 777 primitive-contract failures |
| Seven-zero scanner regrouping | Wrong clean frame at source 1003; an extra scanner state repairs to 196 |
| Short-scanner deletion | 96 unrestricted failures; an invariant-conditioned seed return is also wrong |
| Zero-jump/helper fold | Wrong successor and wrong incremented register at source 26, reproduced during blank execution |

A failed intended refinement certificate is not a universal theorem that the bare table cannot have a useful interpretation. It does prevent treating that supplied certificate as a successful consistency construction. Two separate 196-state Shift-layout diagnostics provide stronger negative controls: both actually halt on blank tape after 43,563 steps, with Lean-checked finite traces in the direct PA tree.

## The principal larger families

| Family | Working states | Main distinction and evidence relevance |
|---|---:|---|
| James Chang PA209 | 209 | Imported upstream commit69d98241a721ead20b4f0b17df9062950b40fbfe;3,948 source sites. Distinct from the U209 parent below. |
| U209 parents | 209 | Unary weak-cover theory and3,909-site source; two principal layouts are the parents of the original U208 pair. |
| Original U208 pair | 208 | Same native172/211 history identification explained by several packets; local complete-tape simulations have lengths1,3,7. Nine designated presentations in the initial five packets reduce to two graphs, so their one-state savings cannot be stacked. |
| Expanded U208 helper family | 208 | Eighteen additional helper layouts bring27 designated accepted presentations to 20 graphs. The much larger142-class literal census includes exploratory/rejected graphs and should not replace this evidence classification. |
| Published PA196 | 196 | Imported upstream407cdc356f6b586635e71ac92be394255f4bfea4;3,812 source sites,4,959 contracts,58,154 startup. Transposed quantifier coding, changed head order/equality interface, and six reader folds already incorporate the old kind of saving. |
| Decoder/layout PA196 relatives | 196 | Shorter paths, multiple associations/rotations, scanner repair, and A/D physical register permutation. Usually preserve the 3,812-site CFG; smaller source DAGs can require more physical readers or an extra scanner control. |
| Closing-decrement PA196 relatives | 196 | Four alternative helper returns change the same row. They are alternative implementations, not four additive savings. Zero-mask proof and common startup are only parts of the full equivalence argument. |
| H-only and Combined196 | 196 | Cached-head Shift removes one source primitive; MP-to-H combined with it yields3,788 sites/4,928 contracts and57,922 startup. This controller change later transfers to 195C and PA195DC. |
| Diagonal196 / Separate196 | 196 | Bundled diagonal-vacuity191 versus separate-head190;3,700/3,673 sites and4,815/4,780 contracts. These are the logical/source parents of the 195 and194 frontier. |
| Cross-archive Combined196 | 196 | Diagonal+Combined and Separate+Combined yield3,676/3,649 sites; zero-jump counterparts are separate implementations. All four include full source/runtime/startup evidence in their packet. |
| Encoded-negation variants | 197 or more | Direct18-primitive negation can reduce separate source to 3,441 sites but costs197 controls in its retained implementation. A source instruction saving does not itself imply a finite-control saving. |

The prior original 195 packet selects25 supported196 layouts, and the later cross-archive work supplies four more combinations. The later separate 196 closing-R113 variant supplies another same-size comparison point. The current 99 root-free196 graph classes additionally contain unaccepted experiments, variants and failures. The reusable inherited selected-machine manifest is copied as `inherited_selected_machines.csv`, with original provenance and recorded evidence status retained.

## Formalization boundary at the current pin

The direct PA README explicitly distinguishes a conditional iPRA endpoint from a machine-specific consistency theorem. Neither machine-specific direction has been established there in iPRA for primary194, original 195 or196. The PA195 dense/all-tape proof does prove a real, substantial preservation result: the native202-control parent and dense195-control table halt equivalently on arbitrary complete tapes, with bridges to ordinary finite-run semantics. That result does not by itself supply the logical/refutation calibration.

The imported PA196 development states the internal implication `PA proves Nonhalt(M196) -> Con(PA)` and external nonhalting in the Lean metatheory. The internal converse does not follow merely from external nonhalting. The incoming manuscript arguments explicitly supply additional uniform syntactic proof transformations and positive simulation to claim the biconditional in PA. Their paper-level proof claim and their lack of a new end-to-end proof-assistant endpoint must both be stated; absence of the latter is not itself a mathematical refutation of the former.

## Novelty of the new cached194 controller

`pa194C.tm`, SHA-256 `d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b`, has194 working controls,388 transitions and halt194. Its canonical root-free action graph is
`b79f4d344740679b87dace02fe3f211565c2cd4513f346812570d90caa3d9a3f`.
Every working root spans the whole working graph. None of its four forms (ordinary, L/R mirror, global read/write complement, or both) matches any existing 194 graph class. Bit complement is used only as a conservative graph comparison, not as an assertion about the all-zero start.

The novelty is also algorithmic: the existing three 194 constructions use original Shift and MP; the new construction uses cached-head Shift and MP-to-H and has3,649 source sites instead of 3,673. Graph comparison establishes absence of a relabeling explanation; it does not on its own prove the arithmetic theorem. The construction's source, command and physical proofs supply that separate obligation.

`verify_novelty.py` reproduces this finite comparison against `census/census.json`; `pa194C_novelty.json` records the result. As a positive control, the same checker recognizes the existing primary194 in precisely its two dense/native byte forms (`novelty_positive_control.json`).

## Additional symmetric-guard 194-state design

A further accepted construction, emitted as `pa194CS.tm` and named PA194Sg in its secondary package, changes the cached Shift source itself. It omits restoration of scratch X into H and exchanges the inputs to the existing destructive equality guard. Its source has **3,646 instructions and 4,745 branch contracts**; its complete blank startup takes **57,768 literal transitions**. The independent literal checker reports all contracts passing.

The dense SHA-256 is `1c71002e5b8a2ddd1dd1311a2c54c424764624b611b69c8efbee1ac23c2e6f5f`; its root-free action-graph hash is `b9dcfe9418c780a3fc8c681b4e13faf744158b5e5548c50eb6cfaa1667f5f9c3`. It differs from every existing 194-state graph and from PA194C under arbitrary state relabeling/root change, reflection, complement, or both. See `pa194CS_novelty.json` and `pa194CS_vs194C.json`.

The precise source preservation is stronger than a legal-command special case. With arbitrary initial `(T,H,X)=(t,h,x)`, the common clear/copy prefix leaves `(h,0,k)` for `k=h+x`. The old tail gives the guard `(H,X)=(k,1)`; the new tail gives `(1,k)`. The exact comparator halts if its inputs agree and otherwise clears both and continues, preserving every other register. Hence both complete source blocks have the same outcome even with arbitrary initial scratch X. The normal cached-command semantics is the inherited special case X=0.

The finite source binding, universal induction proof and exact source-step counts are provided in `check_symmetric_source.py`, `symmetric_source_certificate.json`, and `symmetric_guard_review.tex`. The independent duration regression verifies 4,225 guard pairs and 2,197 Shift triples; the universal justification is the induction proof, not extrapolation from those tests. Source-step savings are zero for k=0, four for k=1, and 2k+4 for k≥2; this does not assert uniform physical-tape speed improvement.
