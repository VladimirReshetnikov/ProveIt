# Formula-set graph through two recursive histories

The positive formula-set graph now has a candidate-PRA client that expands both of its arity-zero syntax subgraphs. The `isUFormula` path uses Foundation's `fixpointDefΔ₁`, whose relevant time is the formula index plus one. The BV path instead uses `fixpointDef`, which has separate existential time and sequence witnesses. The BV result is taken at value zero, as required for an arity-zero semiformula.

`PRABVFixpointBound` handles the BV fixpoint's positive membership graph using the established bit majorant, given a time, a sequence and a bounded actual `limSeqDef`. `PRABVGraphHistoryBound` binds that result through the intermediate BV recursion graph into the exact zero-valued `bvGraph`. `PRAFormulaSetTwoHistoriesBound` connects both graph paths to the actual positive formula-set syntax. `PRAFormulaSetExplicitPairBound` further replaces the BV pair-code witness with the concrete polynomial `(p*p+p)^2`.

The final closed sentence is proved in candidate PRA through all-model IOpen reasoning and completeness. For every relevant formula index it still assumes suitable universal-formula and BV history codes, bounds on both actual `limSeqDef` graphs, and the listed size and bit-membership conditions. It does not construct or bound either recursive history uniformly. Further derivation-rule and refutation predicate obligations also remain, so this is not the requested HA equivalence proof.

The source-current eight-module validation packet is `reviews/pra-two-histories-explicit-pair-author-replay`. Its parent includes the post-merge 103-module graph; the packet records the completed independent parent replays and names inherited Foundation boundaries.
