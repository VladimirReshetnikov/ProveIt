# Comparison of the pinned PA consistency-machine corpus

## Coverage and counting convention

The pinned source is `VladimirReshetnikov/ProveIt@7c0bb454cf73c29ca1c385f9fec856ddd236a7cb`. It contains 100 filed research packets under `Computability/BusyBeaver/Research/PA/docs/` and six remaining incoming ZIPs. The comparison reads the complete filed-packet ledger and all six new delivery descriptions, reconciles the named design catalogue, and separately scans every tracked `.tm`, `.json`, `.txt` and `.zip` below PA and `docs/incoming`. Nested archives are traversed; repeated byte-identical ZIP payloads are counted once for contents. All 15,727 selected source files were checked against the exact pinned Git blob identity, with no missing inputs.

The explicit-table scan recognizes complete binary five-column transition tables and four concrete JSON table encodings. It does not execute arbitrary generators or infer tables from prose. It requires one external halt label. It found 7,331 explicit table occurrences, 1,380 normalized labeled tables, and 1,164 spanning control-graph classes across all state counts. Of these, 548 are 194-state classes and 61 are 193-state classes. There are seven further normalized tables with no spanning start, including two 194-control diagnostics. The 23 recorded parser exclusions are synthetic/runtime fragments without exactly one external halt; none is a 194-state table, and no archive was corrupt.

These are counts of supplied transition graphs, including rejected trials and comparison representatives. They are not counts of valid Con(PA) machines. A distinct graph is also not by itself a distinct mathematical algorithm. The named ledger contains 104 catalogued positive-claim 194-state graphs (91 earlier entries plus 13 new ones), all freshly matched to the current corpus. “Positive claim” records what the supplying packet claims; it does not represent 104 newly re-proved absolute iPRA theorems. Supplementary constructions with narrower evidence are explicitly marked.

The repository's historical `MACHINES.tsv` uses a different broader graph convention and counts source occurrences before filing removed duplicates. Its 1,153 classes and 18,218 occurrences should not be directly compared to the new strict one-halt census as if only new designs changed. For the 194-state frontier the historical 528 classes become 548 under the fresh scan. The present novelty check includes all 548, including the newest incoming graphs.

## Mechanisms that distinguish the existing designs

The detailed `mechanism_families.csv` uses 43 descriptive groups; this grouping is an editorial organization, not a canonical mathematical count. The important independent choices are as follows.

| Layer | Existing alternatives | What must be proved when changing it |
|---|---|---|
| Numerical coding | Constructor coefficients 4, 5 and 6, with several Q variants | Uniform hereditary recoding of formulas and proofs, including the zero alias |
| Logical axiom heads | Original vs exchanged distribution premises; diagonal at A vs D; independent witness consequent; coupled first-head change | Explicit proof-list translations in both directions, with the weak-base restriction on rho8 respected |
| AX command interface | Ten entries and three operands; AX11 with eleven entries and a real fourth operand from MP fallthrough | Exact all-store effect, selectors and word encoding, including the fallthrough operand |
| Generalization binder | Inherited offset versus explicit AX operand c; independent binder and diagonal choices | The generalized formula and the all-store compiler must agree |
| MP and Shift controller | Dummy-zero push vs visible no-push MP vs cached MP; sum halt guard vs cache-only guard; symmetric destructive comparator | Complete command store equality, zero-stack alias and final contradiction detection; cache-only machines require Pop rather than a bare Shift |
| Source control routing | Known-zero decrements, shortened returns, cached symmetric comparison | A source invariant covering each changed path, with exact startup checked separately |
| Physical register layout | Transpositions, optimized nine-register permutation, four-cycle and 3+2 cycle | Register-frame conjugacy and complete blank initialization |
| Decoder structure | Binary reassociations of operand, MP, increment loops and continuation blocks | Resolved source identity, changed source addresses, contextual fold guards and every literal source contract |
| History sharing | Single or simultaneous last-written-bit selectors, marker separation | Exhaustive incoming-edge invariants and complete local tape equality, including secondary entries |
| Physical shortcuts | One, two or three guarded three-to-one returns, compatible selector/loop compositions | Exact finite-time simulation with primitive recursive clock bounds |

This separation matters for optimization. A shorter AX expression or fewer register-machine instructions need not save a physical TM state. A removed reader can require a new history selector; a shortened source routine can destroy useful decoder sharing. Conversely, a graph change with unchanged source can be substantial if it alters hundreds of recurring instruction addresses and its history-sharing structure.

## The six latest incoming packets

| Incoming ZIP | New named designs | Main change |
|---|---|---|
| `PA194ORH_research_2026-11-15.zip` | PA194ORH; supplementary PA194OR | Operand reassociation changes 134 addresses. The apparent one-state saving must pay for a repaired second entry of reader 213: 135 fixed + 66 readers − 7 folds = 194. |
| `pa194_ax11hc4_c32_research_2026-11-15.zip` | PA194AX11HC4; supplementary PA194C32 | Physical register four-cycle and 3+2 cycle, with six and seven active router-row changes. HC4 inherits the revised AX11H calibration; C32 is directly relative to the original primary source. |
| `pa194_new_designs_research_2026-11-15.zip` | PA194LCAX11HSF3; PA194MP | Third guarded return added to LC plus selector/acceleration; independent four-block MP decoder reassociation changes 87 addresses and four rows. |
| `pa194_research_2026-11-14(1).zip` | PA194GD_SF; PA194GDH_SF; PA194GDHS_SF | Four-row history selector plus two guarded shortcuts on the three independent binder/diagonal controllers. |
| `pa194_research_2026-11-15.zip` | PA194H5X_MF; PA194JH5X_MF | Dedicated marker/history selector plus two shortcuts on the witness and coupled-witness sources. |
| `pa194_symmetric_witness_research_2026-11-14.zip` | PA194H5XS; PA194JH5XS | Compare `(1,h)` rather than `(h,1)`, removing cache restoration while preserving every clean-store command effect. |

These six packets add the 13 named classes in the table to the imported 91-entry catalogue. They add 20 new 194-state graph classes in total when experimental and supporting tables are included. No supplied passing sub-194 construction was identified.

## What the recurring rejected 193-state attempts teach

- **Runtime-only fold `301 → 88`:** it can work on initialized frames but loses an initialization operation. The concrete blank execution reaches state 35 on a blank cell beyond all nonzero support at time 92; `35/0 = 1 R 35` then gives an outward ray. A proved trivial nonhalting ray cannot serve as the intended PA-consistency search.
- **Operand-reader deletion without the extra history helper:** reader 213 has a second entry from the 69/0 history route. The apparent 193-state ORH core fails 30 source outcomes. The incoming ORH search tests all 772 replacements of that single transition without repair. The helper restores 194 states.
- **False merge `16 → 38`:** the delivered finite witness gives a complete blank-tape configuration recurrence after 28,217 steps, with period 52. The same failure appears in a canonical primitive source branch. Agreement on a short local tape window is insufficient.
- **Marker-fold guard repair:** replacing the runtime helper and rerouting its guard fails 88 source outcomes and still produces the startup outward ray. Startup and recurring source-frame contracts are independent obligations.
- **Shorter logical expressions:** independent-binder generalizer and modal consequent experiments reach 195–199 physical states or leave all-store completeness unproved. Counting tokens does not certify the full machine budget.

The negative experiments are counterexamples to concrete transformations, not a lower bound of 194 states. The census includes 61 distinct 193-state graphs precisely because proposed smaller machines can be explicitly supplied and still fail the required semantics.

## Novelty of the fresh joint reassociations

The new joint forest search preserves the exact AX11H resolved source while jointly changing the operand, MP and loop association trees, then rebuilding shared decoder nodes and contextual folds. Of its 250 compiled families, 70 have cost 194 and 63 pass the recorded full source contracts and complete blank startup checks. This census agent independently performed the graph comparison for those 63.

Sixty-two passing candidates are new and mutually distinct under a deliberately broad equivalence test: arbitrary control renaming and any spanning start, tape reflection, global symbol exchange, and ignored write/direction actions on halt edges. The test compares exact canonical tuples; hashes are identifiers, not the only evidence of equality or inequality. Global symbol exchange is used only to strengthen the cosmetic-novelty test and is not claimed to preserve the fixed-zero-blank semantics.

The one old graph, `A0M2L11_194`, is exactly PA194ORH. Recovering it is a useful positive control. The 62 others remain different even under the broad convention. All passing candidates have 194 controls reachable in the directed control graph from their stated start and immediate-action bisimulation quotient size 194. This rules out a simple ordinary control congruence reduction; it does not exclude contextual or semantic reductions.

Two representatives are particularly useful: `A0M3L6_194` changes 449 source addresses and has exact startup 57,922; `A2M0L6_194` changes 438 addresses and has startup 58,082. They are distinct from each other and the entire supplied frontier. Their mathematical correctness still requires the independent literal verification and weak-arithmetic transport supplied elsewhere in the final report; this graph census alone does not prove their consistency equivalence.

## Proof status

The current Lean project has incomplete machine-specific calibration endpoints. The revised AX11H packet separately supplies an ordinary written iPRA calibration using explicit proof compilers and exact machine clocks. Its audit is `reference/WRITTEN_CALIBRATION_AUDIT.md`, and the entire inherited packet is included unchanged. New source-preserving designs can inherit that written result once their own exact uniform physical simulation is proved. They should be described as written mathematical constructions with executable finite bindings, with end-to-end kernel verification still open.
