# Independent audit of the five supplied U208 packages

Source snapshot: `VladimirReshetnikov/ProveIt` commit `c086b5adaa6228009365768946d691dfc49a20bb`, `docs/incoming`, retrieved 29 October 2026. This audit reads all five top-level reports (including their input sections), literal final tables, the complete unary lower interpretation and upper proof-transport argument, and the principal executable local checkers. It freshly runs all five advertised quick/finite replays and, subsequently, the full symbolic interpreter replay for both distinct final table classes. It does not construct a new end-to-end proof-assistant certificate.

## 1. The actual comparison: nine final tables, two machines

The five archives contain nine designated final 208-state tables, counting supplementary variants. Every table has 416 rows, 208 graph-reachable working states, start 0, a separate halt label, binary symbols, and L/R moves. All nine belong to **exactly two rooted action-labeled transition-graph isomorphism classes**. In this classification the read symbols, write symbols, directions, root, and halt are fixed; tape reflection and symbol complementation are not permitted.

| Current archive | Principal class | Supplementary class | Principal dense SHA-256 prefix | Distinct contribution |
| --- | --- | --- | --- | --- |
| `U208_ConPA_2026-10-29.zip` | A | None | `9f4ea95849c5e1d0` | Three-row orientation of the history fold; independently implemented local checks; detailed failed source compression |
| `U208_ConPA_Conditional_Context_2026-10-29.zip` | A | B | `a2fee9e41311c0d4` | Particularly clear five-state inductive invariant; two-row orientation; independent finite C++ evidence |
| `U208_ConPA_Entry_Context_2026-10-29.zip` | A | B | `a2fee9e41311c0d4` | Same literal tables as Conditional; explicit reproducible bounded-context discovery and clear proof-layer separation |
| `U208_ConPA_History_2026-10-29.zip` | A | B | `926d15c43daebdafd` | Plain-native orientation; portable fold checker and a concrete failed-rotation witness |
| `u208_research_2026-10-29.zip` | B | A | `5d487fb3ea29a84be` | Makes the distinct Compatibility layout primary and documents full symbolic replays for both final classes |

Conditional and Entry are byte-identical in both their native and dense principal tables; their alternative dense tables are also byte-identical. Other matching-class tables have different filenames, serialization, or state renamings. They are not different halting algorithms. The independent script `research/audit/compare_tables.py` verifies the classification directly from all nine final tables and stores each complete canonical labeling in `research/audit/table_comparison.json`.

Canonical fingerprints under this audit's explicit BFS serialization are:

- A: `5d858b5d7528dd98c5272f83d308c782ae323a47fc394a73ad9efda1096a5284`.
- B: `f0c6098fabd68fce3fca0c6ac78a1b4e9dbb4ded60437b84d3e9d9ccda74f11d`.

These fingerprints are serialization-specific; the complete label maps, rather than the hash alone, are the isomorphism witnesses. All working states are reachable in the transition graph, so canonicalization covers the full table. Graph reachability does not mean reachability on the blank run.

## 2. The same fold is presented five times

All five packages implement the same new U209-to-U208 idea: merge the two native control roles 172 and 211 using recent tape context. In Joint labels, parent state 172 always has predecessor word `10`; parent state 211, conditional on currently reading zero, has a one immediately to the left. The parent states share their read-one transition. The combined read-zero dispatch moves left into helper 217, which uses these contexts to recover the required behavior. Plain/Compatibility use corresponding helper label 214.

Conditional and Entry keep 211, delete 172, redirect `116/0` to 211, and change `211/0` to `(0,L,217)`. Three-cell keeps 172, deletes 211, redirects both rows of 163, and changes `172/0` to `(0,L,217)`. The different number of changed retained rows, two versus three, is an orientation of the quotient and does not make a different machine. History uses the Plain-native names for the three-row orientation. Research uses Compatibility-native names for the two-row orientation.

The four exceptional blocks take 7, 1, 3, and 1 steps for old 172/0, 172/1, 211/0, and 211/1 respectively. They preserve the complete tape and end at the projected parent successor. The remaining 414 parent rows commute with the projection. Consequently, from start 0 on every common tape:

`T208 = T209 + 6*N209(172,0) + 2*N209(211,0)`, and `T209 <= T208 <= 7*T209` for halting runs.

This is a genuine unbounded equivalence argument, not a finite-prefix test. The proof is sensitive to reachable parent configurations: it does not identify the two state functions on arbitrary local tapes. It does not require the parent invariant to hold at intermediate child configurations inside the seven-step block.

Primary proof locations are `Conditional/paper/local_proof.tex`, Three-cell `report.tex`, section "Complete proof of the new machine equivalence", Entry `report.tex`, section "Complete proof of the new reduction", History `report.tex`, section "Complete preservation proof", and Research `report/report.tex`, section "A contextual fold of native states 172 and 211". Here the abbreviated package names refer to the first table.

**Consequence for the new task:** none of these five advertised savings can be combined additively. A candidate below 208 needs a genuinely new deletion or changed source layout, not a combination of these report titles.

## 3. What separates classes A and B

The source maps are byte-distinct but implement exactly the same ordered 3,909 primitive opcode/operand pairs and the same 5,083 nonhalting ordinal control edges. A fresh independent prefix-interval resolver in `research/audit/compare_sources.py` checks this fact. Counts are 1,558 increments, 1,175 conditional decrements, 80 forward branches, 1,095 backward branches, and one halt. Splitting each decrement into its zero and positive guards yields 5,084 contracts.

Exactly 720 source addresses differ. The greatest source-address depth is 42 for class A and 41 for B; both have maximum consecutive-zero run six. Their source SHA-256 identities are:

- A: `cddbed7f20e7a8b085b7ca0e76811d07b021522375643b5d1134eec0d2d23164`.
- B: `912724f29b0de28b3326c710fdf1f3863ebd07058c6db1a9b4bbaffb3ae5e3f3`.

The distinct layouts arose earlier when combining folds of native states 180, 181, and 218. Class A used keeper 163 for state 180, while B used keeper 216. An eight-factor reassociation creates B's differing 720-leaf region. The same U208 history fold then applies to both.

The full symbolic-runtime replay was freshly regenerated for both classes and passed: 1,251,865 symbolic inference applications for class A and 1,250,564 for B, each covering all 5,084 primitive guard contracts and all 416 transition rows. The fresh receipt is `research/audit/replays/research_full.json`. These are costs of the checker, not measured full consistency-search runtimes. A smaller maximum address depth is also insufficient to prove a global runtime advantage.

For further optimization I recommend retaining **both graph classes as separate search inputs**. Entry/Conditional is a convenient class-A reference because its invariant and table binding are explicit. Research is the convenient class-B reference because its primary target and both full replays are organized around that family. There is no mathematical reason to call five isomorphic presentations five independent confirmations of the shared logical calibration.

## 4. Fresh replay results and their limits

All five advertised quick or finite commands freshly passed. Exact invocation arguments, stdout logs, and receipts are under `research/audit/replays/`; `summary.json` records return code zero for every package. The independent canonicalization and source-control comparisons also passed.

The quick replays inspect manifests, exact reconstruction, local fold identities, source bindings, and blank startup according to each driver's scope. Their universal-runtime phases were explicitly skipped at that initial stage. A subsequent fresh `u208_research` full run regenerated and passed the symbolic interpreter contracts for both graph classes, recorded in `research/audit/replays/research_full.json`; elapsed time was about 187.24 seconds in the preparation environment. The parent source inference engine is largely shared across these packages, so multiple reports do not provide five independent implementations of the unbounded runtime reasoning.

The reports consistently distinguish executable symbolic induction from a proof-assistant kernel certificate. They establish literal local equivalences by ordinary mathematical arguments and check finite reconstruction and startup. They retain earlier mathematical compiler, calculus, and interpretation proofs to reach PA consistency. No package contains a new complete Lean, Rocq, MM0, or exported PA proof object for its final U208 endpoint.

## 5. Theory U audit

The exact unary schema, in equality-free classical first-order logic over a nonempty domain, is:

`forall a exists b [forall x (E(x,b) -> phi(x)) and forall x (Sub(x,a) -> (phi(x) -> E(x,b)))]`,

where `Sub(x,a) := forall t (E(t,x) -> E(t,a))` and the only permitted free matrix variable is x. Bound-variable count and quantifier complexity are unrestricted. The source a must not occur freely in phi. Outputs are weak covers; exactification by inserting `Sub(x,a)` into phi would violate the unary restriction.

I read the complete `pa_unary_power_cover/sections/unary_core.tex`, `unary_arithmetic.tex`, and `upper_transport.tex`, as well as the separation and positive-interface sections. I found no concrete circularity or illicit free parameter in the reviewed lower interpretation. Its delicate steps are handled in the following order:

1. Coextensionality, saturation, numerical representatives, and endpoint conditions are defined without assuming external finiteness or a global extensional universe.
2. Empty objects and local predecessor facts precede total successor existence.
3. Unary failure filters prove representative induction using the least failure inside an existing number or that number itself if the interior has no failures. The latter case avoids assuming a successor of the counterexample.
4. `forall parameters (base-and-step -> theta(v,parameters))` internalizes parameters in a legal unary matrix. This also covers induction predicates not invariant under coextensionality.
5. Comparison and global least numerical tuples then yield bounded numerical comprehension. Its invariance and support hypotheses are explicit. The support is selected outside the matrix; numerical tuples are bound inside a least-failure formula.
6. Successors, numerical powers, saturated numerical pair codes, and graph comprehension follow. Old histories are existentially bound inside canonical graph formulas, not smuggled in as free nonnumerical parameters.
7. History uniqueness precedes extension. A separate numerical value bound prevents an unstated monotonicity assumption. Successor iteration defines addition and addition iteration defines multiplication; induction was already available.

The reverse interpretation uses binary-bit membership in PA. Formula-by-formula bounded comprehension follows from PA induction; no uniform satisfaction predicate is introduced. The operations on formulas and fixed derivation templates support the stated PA-verifiable finite-refutation transport. The manuscript does not deliver a fully implemented arbitrary-proof translator or a checked kernel theorem for it. That is a formal-artifact gap; this audit did not identify a missing mathematical lemma in the examined interpretation.

## 6. The machine does not directly enumerate unary U

The final machines retain the native Cantor-coded calculus calibrated to unrestricted weak covering W plus global irreflexivity IR. The unary ZIP's positive dyadic stream is a separate abstract specification and has not been compiled into these tables.

The retained logical cycle is `Con(PA) -> Con(W+IR) -> Con(U) -> Con(PA)`. Its first arrow uses the PA bit interpretation, its second unary-instance inclusion, and its third the lower interpretation. The numerical calculus has target code 1 and truth alias 0. The separate dyadic stream instead targets code 0. Confusing these conventions invalidates the claimed endpoint.

The inherited native bridge must handle low-code aliases, auxiliary equality through membership indiscernibility, variable freshness and padding, source/output collisions, arbitrary old stack content, and cofinally many successful proof descriptions. Blank startup also enters an interior axiom-generator suffix, not a clean proof-search root. Its nine theorem heads protect an opaque tail; a ghost stack length is needed because `P(0,0)=0`. The unbounded scheduler credit argument, not the finite 48,140-step startup trace, prevents exposure of that unsafe tail.

These obligations are carefully identified in Conditional `paper/calibration.tex`, Entry `report.tex` section "The logical calibration retained from U209", and the corresponding calibration sections of the other reports. The k215-pa theorem concerns K215 and Con(ZFC); it cannot be transferred to a changed U table by changing the statement text.

## 7. Hazards and excluded shortcuts relevant to a new reduction

- Pure source-DAG reassociation is insufficient because the same physical decoder states can be entered by backward arithmetic paths. The tempting changes `((98,12),150)->(98,(12,150))` and `((166,12),150)->(166,(12,150))`, followed by merging equal states 85 and154, preserve the source word and ordinal CFG but fail literal interpreter simulation. History's `research/rejected_source_fold` supplies a finite witness: source ordinal25, zero-valued registers, expected return28, actual return44.
- Shortening the seven-zero origin detector by removing native34 and changing23/0 to75 fails the first zero-decrement primitive. Source address zero-run statistics omit temporary runtime markers.
- The apparently dominated propositional axiom row cannot simply be deleted. The retained older analysis supplies an interpretation validating the remaining calculus while keeping the target false.
- A bounded-context search with no successful fold is not a lower bound. Entry retains a depth8/31-step one-row-fold search with no results, but this only excludes that fixed search space.
- A local fold theorem should specify the exact parent table, all physical incoming rows, a complete invariant, arbitrary-exterior tape identities, positive block lengths, halt reflection, and initializer treatment. Merely counting 207 state labels or preserving a finite blank prefix does not meet the requested standard.

The appropriate final claim for a new candidate is a proved literal halting-equivalence theorem first, then an explicit composition with the retained mathematical PA calibration. Any not-yet-checked kernel endpoint should remain clearly distinguished from that ordinary proof.
