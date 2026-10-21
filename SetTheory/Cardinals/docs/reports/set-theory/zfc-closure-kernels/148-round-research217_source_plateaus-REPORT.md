# Closed-factor source plateau census

The approved search has not constructed a 217-state machine. This is a source-DAG census, not a physical-state allocation.

## Verified baseline and scope

The literal published baseline has 4,744 primitive leaves, 23 primitive types, 182 distinct internal subtrees, and 205 total source-DAG nodes. Its physical machine independently has 218 states. Input source SHA-256: b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9. Input native table SHA-256: 2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f.

Every move globally replaces one distinct subtree by a single reassociation of three halt-free factors whose exact boundary is (0 escaping breaks, 0 escaping continues, false halt). Baseline source roles bound to physical states 157 and 200 are excluded as direct rotation targets, reserving those physical experiments for the encoding lane. Changes to their ancestor/source identities may still occur as a consequence of a different global rotation; no physical edits are performed here.

## First step: complete

Of 193 inventoried baseline global closed rotations, six reserved targets are excluded, leaving 187 candidates:

- 75 remain at 205 source-DAG nodes.
- 112 rise to 206 source-DAG nodes.
- None reach 204 or lower.

All 75 neutral source candidates retain the exact primitive word and ordinal control graph. Full continuation-stack and binary-address resolvers independently agree with the baseline on all 4,744 vertices and 6,166 edges. Each candidate has exact serialized AST and source hashes.

## Second step: capped, not exhausted

The chosen 24 neutral first-step roots prioritize the existing-child reuse count. Their second-step inventories contain 4,492 eligible rotations, below the approved ceiling of 5,280. The 60-second aggregate wall-time guard stopped the run after 1,716 second-step tests:

- 686 evaluated transformations have 205 source-DAG nodes.
- 1,030 have 206 source-DAG nodes.
- No evaluated transformation reaches 204 or lower.

This is CAP_UNKNOWN, not a negative exhaustion claim. Deduplicating backtracks and repeated results leaves 717 distinct neutral candidate sources across both stages, including the 75 first-step candidates. Every saved candidate received full primitive-word, continuation-CFG, and address-CFG validation. Expensive verification and file serialization are included in the cap; setup before the timed loop is not.

## Concrete handoff

The strongest new local reuse lead is a left rotation at source role 86, factor lengths [27, 1, 1]. Its old shape is (A, (CI1, CI1)); the new shape is ((A, CI1), CI1). The new left child already has the 28-leaf decoder entry 150. The new right child is primitive CI1, not another decoder node. Current rows are 86/0 = 0R90 and 86/1 = 1R99; a physical implementation would require 86/0 to target 150 and a proved read-one CI1 interface. No physical edits or primitive claims were made.

Exact source: source_65c7caa193095276.sites.json, SHA-256 65c7caa19309527690d7f3a087b0fae801fad139bdf20d303bb156fd63c4923c.

Exact AST: source_65c7caa193095276.ast.json, SHA-256 68fc0a7e7f10642d9f51883eda7eb1faa063acf3273b87bb8abd24e0a34a61b3.

The left rotation at role 188 merely recovers the already known stage205 source (SHA-256 0f6c3f9d3f0408f8d5c02d4b2f7c48a3111df4c0e24a1f1816ccab43b11d9a61). It is not a fresh reduction and risks the existing selector helper row 188/1. A neutral role-85 rotation shares a physical state with another source role and requires distinct treatment.

## Role and proof cautions

ROLE_RISK_ANNOTATIONS.json reconstructs every saved transformation from the literal baseline and exact Merkle identities, then reports affected baseline source identities and known mixed physical allocations. Losing an old AST identity is not evidence that its physical state can be removed. Changes to source identities above a rotated node do not by themselves require changing those ancestor transition rows.

In particular, selector helpers 188/1, 189/1, 190/0, 190/1, 156/1, and 176/1 must retain their non-decoder contracts even where a source allocation calls them pure. Parent source-role changes may affect helper allocations. Arithmetic, bootstrap, primitive entry/exit, and whole-source binding proofs remain mandatory for every eventual physical candidate.

## Artifacts

- search_plateaus.py: owned source census driver.
- INVENTORY.json and SECOND_STEP_INVENTORY.json: recorded inventories before each census phase.
- FIRST_STEP_RESULTS.json and SECOND_STEP_RESULTS.json: complete tested rows, cap status, and exact-source receipts.
- SUMMARY.json: concise machine-readable search results and candidate hashes.
- annotate_role_risks.py and ROLE_RISK_ANNOTATIONS.json: exact source reconstruction and structural role-hazard annotations.
- source_*.sites.json, source_*.ast.json, source_*.receipt.json: exact validated neutral sources. These files are not physical machines.

## Subsequent structural ranking and corrected role86 disposition

The generic census was not extended. The 717 saved sources were ranked for a concrete physical-selector mechanism instead. This revealed that the tempting role86 reuse is invalid as a ready patch: state150's 28-leaf role is observed only with predecessor marker1, whereas the proposed86/0 transition supplies marker0 and selects its54-leaf role. State86 also acts internally when decoding role171. The encoding lane independently rejected the cheap gate substitutions. The source itself remains exact, but the local reuse claim requires a new compatible detour and is not recommended.

The owned static row-plan analysis rejects all edits to states157/200, state85, or the six protected helper rows. It also rejects source target/inner reuse with ambiguous physical roles. Of717 saved sources,374 have a syntactic small-row plan; after rejecting known existing-child marker mismatches,259 remain. An independent exact census over every baseline internal-child one-bit decoder walk finds52 interior helper rows. Requiring every edited old row to be a bit-preserving right transition that is never one of those interior helpers leaves106 plans. These filters are necessary conditions, not full prefix-binding or primitive proofs.

A static incoming-transition analysis then finds87 plans that create at least one new pair with a shared row and opposite forced predecessor markers. It does not run a selector search, and no plan closes the old19 near-misses by a simple unchanged-helper endpoint match. Three four-row, two-role variants were forwarded for targeted prefix binding and selector tests:

1. Role213 left, reuse221. Source SHA-25662d69601c790b0c314b298b65bfe79b740e093d1f97c42f8329bdac839286e27. New static marked pairs [100,186], [100,221], [203,221].
2. Role222 right, reuse209. Source SHA-2566550ca5904ccf72702c3f667bcfdd2e618c1c98d071b4366191f01b442db72f3. New static marked pairs [129,133], [133,182], [216,222]. No row of157 or200 changes.
3. Role100 left, reuse101. Source SHA-256da92475c629a42cba63ad37ccf0113100d92f637f2982b2c57f9e9fd88527681. New static marked pairs [100,220], [101,203], [101,213].

Exact source and AST hashes, local row changes, pair markers/actions, and all caveats are in SELECTOR_OPPORTUNITY_SHORTLIST.json. The files PHYSICAL_LEAD_RANKING.json, MARKER_FILTERED_RANKING.json, INTERIOR_HELPER_ROWS.json, and PURE_ROW_SHORTLIST.json preserve the intermediate filters. Their owned reproduction drivers are rank_physical_leads.py, rank_marker_compatible.py, filter_interior_helpers.py, and rank_selector_opportunities.py. No physical machine was saved or state-count reduction certified by this lane.
