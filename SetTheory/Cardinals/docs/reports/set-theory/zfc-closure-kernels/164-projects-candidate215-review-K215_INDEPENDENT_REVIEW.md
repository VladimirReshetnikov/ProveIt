# Independent review of the 215-state composition

**PASS at the ordinary mathematical proof scope described below.** The exact 215-state table has passed the fresh unbounded primitive replay, independent inventory of every replay case and affine clock, independently implemented source-bisimulation checks, both retained all-tape marker proofs, and independent dense native/canonical startup replays. No unresolved issue was found in these new obligations. The foundational numerical-calculus/ZFC calibration remains inherited, and no new proof-assistant endpoint is claimed.

## Exact objects

| Artifact | SHA-256 |
|---|---|
|Native table|`04b4dbb537306f40f8965ad6a0ee6034e9953f079c233153e9696acdf06c2712`|
|Canonical table|`6c0fff966c4409eb726e634d6d5753552e198da0f8c7bfe7fc39ec0151f1de7a`|
|Source sites|`17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba`|

The table has 215 working states and 430 binary transition rows. Its sole external target is the halt label. Every working state is reachable in the directed transition graph; this statement does not claim that every state occurs on the blank run. Canonical labels are 0 through 214, with halt 215. Native start is 0, dispatcher 84, and halt 254.

Relative to the **public Partial Selector 216** table, the new allocation deletes native state 185, adds no state, and changes 36 retained rows. This count is computed directly from both literal tables. It includes the state 81 helper repair.

## Source semantics

The new source has 202 distinct DAG nodes, 4,751 primitive occurrences, maximum depth 47, and maximum zero run 6. The independent checker reconstructs its complete binary tree and computes its guarded control graph twice: once using binary increment/cut arithmetic and once using subtree intervals and outward ancestor traversal. Both computations agree.

Its primitive word and every guarded successor agree with the credited **public Permuted Commands 216, permutation 210** source. The comparison covers 6,175 guarded successor edges and 6,176 successor/initial-location obligations. Relating configurations with equal primitive ordinal and equal natural-register store gives a strong step-for-step source bisimulation: operations, guards, register updates, halting, and successors agree. This is an all-natural-store theorem, not a finite register experiment.

The source comparison transfers the public permutation construction's command semantics and its inherited numerical-calculus calibration. It does not rely on the separate new projector-family or retained-residual proposals in this research packet.

## The two marker folds survive exactly

The independently reconstructed unfolded composition has 217 working states. Folding 69/400 produces a 216-state precursor; folding 164/183 then produces the exact 215-state table above. In both cases every unaffected row commutes with the stated state map, and the only incoming edges establish the required left markers.

| Fold | Marker 1 entry | Marker 0 entry | Selector | Marker 0 provider/target | Marker 1 provider/target |
|---|---|---|---:|---|---|
|400→69|`53/1 = 1R69`|`135/0 = 0R400`|213|92→104|90→105|
|183→164|`163/1 = 1R164`|`205/0 = 0R183`|201|195→150|196→77|

On read 1, each pair has the same ordinary row. On read 0, the folded state moves left, reads and preserves the incoming marker, returns right to the corresponding provider, and executes the correct old continuation. The two visited cells are restored and no other cell is inspected. One old step therefore corresponds to one or three new steps, with complete tape, head, and mapped state equality at the boundary. Neither merged role is an initial state, so the incoming-edge invariant covers every entry from state 0 on an arbitrary initial tape. Positive bounded blocks preserve halting and infinite execution in both directions.

Fresh window-proof replays, including corruption controls, independently confirm these literal lemmas:

| Stage | Inductive contexts | Nontrivial contexts | Old/new block lengths |
|---|---:|---:|---|
|217→216,69/400|27,451|32|1/1 or 1/3|
|216→215,164/183|27,475|48|1/1 or 1/3|

Both deliberately corrupted initial-halt transitions were rejected. These all-tape claims concern the reconstructed precursors and their local quotients; they are not a claim that the original public machines and the new composition are equivalent on every arbitrary tape.

The replacement `81/0: 0L92 → 0L111` was also checked separately for both possible bits immediately to the left. Each old and new fragment takes exactly three transitions, ends in state 123 for marker 0 or state 21 for marker 1, moves the head right by one, and preserves the entire tape. Other uses of the reallocated decoder are discharged by the full primitive-runtime replay.

## Full primitive runtime

The fresh inherited symbolic engine proves all 6,176 guarded cases for the exact new source and exact new table. An independent receipt inventory confirms exact ordered coverage, with no duplicate or missing cases, including both guards at each of the 1,425 decrement leaves. All 430 native rows occur directly in the proof records.

The replay uses 1,698,790 symbolic rules: 1,443,432 literal rules, 251,558 unary-loop rules, and 3,800 list rules. Every duration is an affine expression in 12 natural variables with nonnegative coefficients and a strictly positive constant; the smallest constant is 6. Thus the finite proof-construction process certifies positive finite primitive execution for unbounded natural register values, gap, first spare value, and finite remaining spare list. It is not a bounded simulation of those values.

The independent inventory checks the fresh replay's records, identities, coverage, and clocks. The universal symbolic replay itself was run separately. The inspected generic proof engine is unchanged from the earlier reviewed engine; the differing old source pins and default CLI paths are outside the imported proof routines.

## Complete blank initialization

An independent dense byte-array simulation reproduces every transition in the fresh 95,726-step sparse startup trace. A second dense simulation uses the literal canonical table after verifying the complete state-label bijection. Both end at the same complete tape:

* native dispatcher 84, canonical dispatcher 83;
* head coordinate −8;
* additional gap 1;
* logical registers `(4,0,0,0,0,0,0,0,0)`;
* 40 spare blocks, every value 1;
* 95 one-cells, with every other tape cell zero.

The dense simulation visits coordinates −18 through 199, strictly inside its initially zero buffer; all unvisited infinite exterior cells therefore remain zero. Decoding independently checks the complete finite support, root source pointer, header, register block order, spare blocks, and exterior condition. Merely matching the nine register values would not suffice.

This seed has current theorem, cached theorem, theorem stack, command parameter, scratch registers, and proof cursor all zero, with next-candidate value 4. The inherited cofinal candidate-enumeration argument allows this finite initial cutoff. Soundness starts from truth-only accessible theorem data; completeness eventually reaches a refuting command word if a native refutation exists.

## Conclusion and attribution

Exact startup enters the source simulation invariant. The complete unbounded primitive replay transfers machine execution to the new source. Its all-natural bisimulation transfers execution to the public calibrated command source. The inherited soundness/completeness and native-calculus/ZFC calibration then yield the intended ZFC-provable equivalence between blank halting and existence of a finite ZFC refutation, and hence between blank nonhalting and `Con(ZFC)`.

The partial-selector construction, command-specific input/permutation construction, state 81 helper reuse, dominated-rho8 theorem, calculus, and runtime infrastructure are credited upstream. The new construction is their compatible source composition and constrained physical allocation to 215 states, together with fresh verification of its exact bytes. This is an ordinary mathematical result supported by executable certificates, not a claim of absolute consistency, state minimality, priority over all other work, or a newly kernel-checked Lean/Rocq theorem.
