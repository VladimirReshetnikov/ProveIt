# Final freshness audit and exclusion addendum

**Exclusion cutoff:** `7def5e00ef3593b296eb595add1d955d27121d0c`.

**Proof source/compilation pin:** `553a5f7a463cbaab8800ff8148fef0bc5a9e1b22`.

This addendum supersedes the initial candidate screen for integer interval induction and shared-edge row construction. Both were independently rediscovered during the present review, but newly available packets already propose them. They are therefore excluded from the final recommendations, including their advertised integration work. Completing an earlier unimplemented bridge is not credited as a new idea.

## Corpus changes and exact identities

**Delivery relocation check:** `45ac0dfc366f798d4686070a89d66e8dafdb6879` contains the same 22-packet corpus, now all placed as a–v. `DELIVERY_CHECK.md` verifies all a–u subtree identities and accounts for every Round3 member in v; the only content-format change is CSV line-ending normalization. No new substantive proposal was introduced.

At the initial source pin, the requested collection contained six placed packets and twelve incoming ZIPs. At the refreshed cutoff, the index places twenty-one packets, `2026-10-26a` through `2026-10-26u`, and the additional Round3 ZIP remains in `docs/incoming`. Thus the bounded exclusion corpus now contains **22 packets**.

The former twelve incoming ZIPs are now placements `g`–`r`. The refreshed index maps each to the exact archive name already reviewed; this relocation does not introduce twelve new proposals. `freshness-summary.json` records that mapping. Four genuinely additional packets required review:

| Key | Exact location at cutoff | Principal manuscript |
| --- | --- | --- |
| S | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26s/` | `report.tex` |
| T | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26t/` | `report/report.tex` and `report/sections/*.tex` |
| U | `Computability/DiophantineConsistency/research/lean-proof-simplification/2026-10-26u/` | `report.tex` |
| R3 | `docs/incoming/ProveIt_Lean_Simplification_Round3_2026-10-26.zip` | `LeanReview3/report/proof_simplification_report.tex` and `LeanReview3/report/sections/*.tex` |

S/T/U contain **164 placed repository files**; all have Git blob IDs and SHA-256 identities in `freshness-added-file-identities.json`. Their **159 textual files** were read for inventory/candidate searches. R3 is **2,963,759 bytes**, SHA-256 `323b106aaf53cf5453cf21794d87ba713e763af917ebf77866db1e7f87d60629`, Git blob `582c23e8a01eb96401e551ee8b3ff0ccabfe85ca`. It contains **985 nondirectory members**, including **980 extracted textual members**. The refreshed candidate search therefore spans **1,139 additional text files**, including unchanged snapshots before their scratch copies were pruned. All archive-member hashes were retained.

The audit read all new manuscript proposal sections and relevant notes/code and searched all additional textual members for the selected mechanisms. It does not treat unchanged bundled source snapshots as separate proposals or claim semantic verification of every snapshot. The local Git fetch is shallow; this addendum makes no claim about the number of intermediate commits.

## Exact collisions and consequent removals

### Integer interval induction: excluded

U `report.tex` lines 270–318, section **Use integer induction around the known point**, proposes translated integer induction for the exact `WangTiles942ResetRows.interval_propagate` theorem. Lines 306–318 explicitly propose the arbitrary-center `Int.inductionOn'` alternative and discuss its axiom footprint. U `patches/optional/interval-propagation-centered.patch` contains the same interval motive and forward/backward branches as the discarded present candidate.

R3 `LeanReview3/report/sections/06_interval.tex`, **R1 Induct over a translated integer interval**, independently contains the translated version and exact same target. Shorter binder syntax in the present prototype is not a new simplification mechanism.

### Shared-edge construction: excluded in full

U `report.tex` lines 353–438, **Make Wang horizontal matching structural**, already specifies west(x)=E(x−1), east(x)=E(x), the single pulse at min(old head,new head), and a direct equality with the actual literal `stepTile`. It explicitly handles the unconditional horizontal theorem by overwriting the configuration's state with the supplied live index. Its actual-tile integration is proposed work, and is assumed completed under the user's rule.

R3 `LeanReview3/report/sections/07_pulse.tex`, **R2 Describe both horizontal edges by one pulse**, supplies the concrete bond function and paired west/east invariant from the actual constructors. The bridge, pulse, unconditional-state adapter, and proof by direct constructor cases therefore receive no new credit in the final packet.

## Four surviving mechanisms

| Mechanism | Refreshed finding | Required novelty boundary |
| --- | --- | --- |
| Helical vector-period normalization and period-one seam invariant | No matching proposal in S/T/U/R3. Periodic-function hits are existing source hypotheses, source history, or unchanged proofs. | Reuse integer multiples of `(w,-1)` on the uncurried function; do not re-propose finite-cell geometry or the already-excluded interval induction. |
| Fixed-index Pell-six threshold anchor | No matching proposal. T changes fundamental-unit minimality; U strengthens the native-rank envelope. Their copies of `large_of_six_le` retain the old variable-exponent argument. | Use fixed `xn(5) ≤ yn(6)` and index monotonicity with no new polynomial helper; generic monotonicity itself is not new. |
| Symbolic color moments for selector masses | No matching proposal. No new manuscript or candidate code certifies weighted signals through the target count, target sum and rail sum. | Assume balanced chunk assembly and packed-field descriptors already available; charge every symbolic/statistic/cutoff bridge. |
| Canonical recognition of an arbitrary allowed operating row | No matching proposal. U/R3 construct the explicit row; neither proves that an arbitrary globally matching allowed strip row with the given upper configuration equals it. | Assume the entire shared-edge construction already implemented. Credit only the converse whole-row invariant, its charged recognition lemmas and actual clients. Local fiber classification is also assumed available from earlier packets. |

No global novelty claim is made. These conclusions concern the supplied exclusion corpus at the stated cutoff. The proposed canonical-recognition development still needs its mathematical/Lean proof and cost assessment; non-overlap does not establish implementation benefit.

## Source freshness

The fifteen selected target/dependency modules were compared byte-for-byte between the proof pin and the refreshed cutoff. **All fifteen are unchanged.** They include the helical/seam/interval targets; `NativePellBootstrap`; the two selector-mass modules; the literal tile Core/Data/Signals/OperatingRow/RowStep/StepConstruction modules; and WangMachineStep/Encoding/Action. Their old/new SHA-256 pairs are in `freshness-target-source-identities.json`.

This permits the retained proof experiments to keep the earlier compilation pin while the novelty exclusion boundary advances. It does not assert that the whole maintained Lean tree is unchanged; other source modules changed upstream. The original count of 445 module-directory Lean files is an initial-pin statistic, not a current-main inventory.

## Additional exclusions

The following fifteen overlapping coverage records supplement the original 131 records. They include repeated/refined prior ideas where needed to make the new corpus boundary explicit; they are not fifteen disjoint new inventions. For paths beginning `2026-10-26s/t/u`, prepend the research collection directory above. `Round3::` denotes the exact archive member.

| ID | Mechanism to assume already applied | Exact reference |
| --- | --- | --- |
| F01 | **Compositional exact object-formula specifications.** Normalize selected Sat clauses, atom specs, scons and determined existential witnesses; retain structural expression induction but combine add/mul semantic cases. | 2026-10-26s/report.tex, sections Normalize exact object-formula specifications compositionally (177–290). |
| F02 | **Pell comparison through positive scale/error envelope.** Share scaled upper and lower ratio comparisons across ordinary and native clients, preserving denominator normalization; parameterized error allowance and wrappers are prior. | 2026-10-26s/report.tex291–384;2026-10-26u/report.tex125–197. |
| F03 | **Integer recovery from two error budgets.** Use Nat.floor_eq_iff to identify natural integer parts from two strict intervals with nonnegative offset and total error ≤1; half-binomial,ordinary and variable-denominator clients. | 2026-10-26s/report.tex385–442; examples/IntervalExtraction.lean. |
| F04 | **Closure of observed internal certificate sets.** Abstract internal-set union/insertion closure via monotone step predicates and injective observation encoding; bound,renaming and rank clients; malformed unobserved members allowed. | 2026-10-26s/report.tex443–517; examples/ObservedClosure.lean and ClosureClients.lean. |
| F05 | **Exact list codec and typed parents via raw checker.** Identify concrete encodeNatList with standard Encodable list codec, reuse its length theorem, derive typed parent correctness by encoding through raw correctness. | 2026-10-26t/report/sections/02_encoding.tex. |
| F06 | **Local coefficient fiber as foundational theorem.** Isolate one selected pair-sum exponent without global Sidon assumptions; handle diagonal/off-diagonal multiplicities, mixed products, and derive separated rows through selective-zero results. | 2026-10-26t/report/sections/03_coefficients.tex;07_next.tex mixed products. |
| F07 | **Absolute second-coordinate Pell minimality.** Replace signed y enumeration by |y| and y², use the consecutive-square gap, and optionally derive fundamentality from minimal y² among competitors with x>1. | 2026-10-26t/report/sections/04_pell.tex; optional/PellMinimum.lean. |
| F08 | **First failure with its valid prefix.** Package least bounded departure and all earlier predicate instances; retain separate geometric endpoint/nonexistence premises in InitialStrip left/right clients. | 2026-10-26t/report/sections/05_first_exit.tex;2026-10-26u/report.tex320–352. |
| F09 | **Stronger common native-rank envelope.** Use positive transport gap to prove (2q−1)(q²−1)≤R for q≥3; derive R≥40 and R>3q from one nonlinear proof, with original public wrappers. | 2026-10-26u/report.tex198–269. |
| F10 | **Integer interval induction centered at the seed.** Replace two Nat inductions/toNat distances by translated Int.induction_on or arbitrary-center Int.inductionOn'; preserve strict interval motive and discuss choice-axiom tradeoff. | 2026-10-26u/report.tex270–318; patches/optional/interval-propagation-centered.patch; Round3::LeanReview3/report/sections/06_interval.tex. |
| F11 | **Shared-edge construction and paired spatial pulse.** Build west(x)=E(x−1),east(x)=E(x) with pulse at min(old,new); preserve unconditional statements by overwriting state with supplied q; prove direct stepTile bridge and/or paired edge invariant once. | 2026-10-26u/report.tex353–438,lean/SharedEdgeRow.lean;Round3::LeanReview3/report/sections/07_pulse.tex. |
| F12 | **Absolute-value trace-bound API reuse.** Turn t≤|x| directly into the exterior disjunction through le_abs'; retain inclusivity and halted/write-before-move behavior. | 2026-10-26u/report.tex440–449;Round3::LeanReview3/report/sections/05_machine.tex M3. |
| F13 | **Sentinel-last state encoding injectivity.** Identify none-at215 stateNumber with finSuccEquivLast.symm followed by Fin.val, then compose existing injectivity. | Round3::LeanReview3/report/sections/04_encoding_action.tex E1. |
| F14 | **Reflect action halt through state-number injectivity.** Rewrite equality through stateNumber_injective.eq_iff, act_stateNumber and stateNumber_none; keep target<216 bound. | Round3::LeanReview3/report/sections/04_encoding_action.tex M1. |
| F15 | **Split machine color proof only at write site.** Use one-cell tape write support/frame rule; leave moved-head conditional symbolic away from old head instead of splitting destination again. | Round3::LeanReview3/report/sections/05_machine.tex M2. |

## Evidence files

- `freshness-summary.json`: cutoff, packet relocation mapping, exact R3 identity, exclusions and surviving mechanisms.
- `freshness-added-file-identities.json`: all 164 S/T/U placed-file identities.
- `freshness-new-text-manifest.json`: hashes for all 1,139 additional searched text files.
- `freshness-candidate-search.json`: complete recorded keyword hits, including snapshot hits; manual report reading determines the decisions above.
- `freshness-target-source-identities.json`: fifteen exact old/new source comparisons.
- `freshness-exclusions.json`: the fifteen additional coverage records.

The original `EXCLUSIONS.md` and `exclusions.json` remain the baseline catalog, with this addendum governing all later novelty decisions. The final report should present four retained directions and should not include the withdrawn integer-induction or shared-edge proposals as recommendations.
