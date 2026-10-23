# Wave 9 baseline review

## Scope and provenance

The six incoming archives are pinned by ../../INCOMING_PINS.json, arrival commit 7331974b696693a8eed2aa5f0f64f1c19d9569f0, placement beb0192cb8dc36f78c369c080f2adfbc1887a486. All original archive and extracted-source trees were preserved. SOURCE_PINS.json authenticates the current repository documentation and formalization commit metadata reviewed here.

## Independent finite checks

After inspecting imports and process-launch surfaces, each original root replay was executed in a fresh temporary copy with Python optimization disabled and bytecode writes disabled. All six passed (REPLAY_RESULTS.json); the slowest was calibrated-carry at 100 seconds. Original source hashes remained unchanged. Integral-root and congruence-norm drivers update runtime receipt files in their copies; this is not a changed mathematical artifact. No package installation or network action was run by the replays. EXECUTION_SURFACE.json records the inspection, not a formal security proof.

count_frontier.py independently parses 72 selected circuit DAGs, checks operand topology and all-gates-live conditions, and counts charged binary additions/subtractions/multiplications and declared variables. All pass. Degree numbers in FRONTIER_COUNTS.json are inherited metadata/certificates, not inferred from the operation count; their supplied exact-degree checks are covered separately by the original root replays. pareto.py computes the selected-set comparison. These audits cannot establish the universal mathematical equivalences or correctness of imported literature.

## Comparison, before new wave-9 constructions

The strongest incoming nine-positive point remains our preceding degree-separated packet: degree 1,910,404, 473 operations. It dominates all selected nine-positive alternatives in these six packets on both degree and cost. Thus a new composition should compare with this point, not the older package-52 target used by the current Lean development.

Ten unrestricted integer points are a real degree/cost tradeoff: 8,317,400/544 (Separated Degrees), 8,469,528/533 (our prior packet), and calibrated-carry's larger-degree 24,369,008/519, 25,355,280/517 and 25,838,224/513. The Congruence Norms packet's 9,152,284/586 is dominated numerically, but its two-root congruence norm is a useful structural ingredient. All these ten-integer forms use the Sun reduction, whose imported theorem must remain explicit.

The Integral Root packet improves the moderate-degree fifteen-positive frontier to degree/operations 24/90, 26/88 and 30/79. It extracts divisibility of the supplied main Pell roots rather than introducing powers of a scaling variable in the roots. The Separated Degrees packet's two separate norms give twelve-positive 242/94 and 258/89. Its thirteen-positive 132/83 trades with our 126/91. The fourteen-positive point is 52/79. The thirteen-unrestricted-integer point without Sun is 11,543,632/518.

The selected fifteen-positive frontier is 24/90, 26/88, 30/79, 44/75, 46/74, 54/73, 64/72, 78/71, 80/70, 91/69, 101/68, 125/67, 157/66. The final selection explicitly includes the inherited source47 gap_minima75.json incumbent at degree44/75; its75 operations are independently counted. The prior selected44/76 point is dominated and is not an incumbent. No single member wins all measures. In particular, do not call a lower-degree new form the shortest circuit while 66 operations remains available. Domains, variables and coefficient sizes also matter; positive and unrestricted integer unknowns cannot be interchanged in this comparison.

Useful independent ideas are free-coordinate absorption, degree-separated coefficient extraction, two-root norms justified by congruences, integral-root desaturation, and calibrated binary carry. Their composition is not automatic: each source's coefficient tuple, domain guards, strict inequalities and completeness witness construction must survive unchanged or be reproved.

## Formal status at the baseline pin

Commit dabf4e39f1039a7f77056517ecbb01d6db1a8ced reports a successful 3709-job umbrella Lean build and audits using only propext, Classical.choice and Quot.sound. It formalizes package 52's literal 60-gate/22-row quadratic source, its 136 shifted coefficient records and 71 active pairs, exact position kernel degree 7516, product degree below 7865, corrected coefficient height, arbitrary-position low-mask decoding (including the weight-zero input and excluded dummy position 81), cofinal bounds, exact ratio reparameterization, and margin-first finalizer.

This is substantial local kernel-checked progress, not a complete new endpoint. The assembled source adapter, actual native-port calibration, closed replacement equation and internal ZFC equivalence remain expressly open. Existing closed ExplicitZFC and NativeZFC endpoints are retained; an existence-based nine-variable polynomial is not a materialized numerical circuit certificate for the new packet. The current documentation separately distinguishes external equivalence and object-language ZFC provability. This audit read those declarations and commit evidence but did not rebuild Lean. None of the fresh numerical audits upgrades the six incoming ordinary mathematical proofs to end-to-end Lean proofs.

## Findings and limits

No replay failure, dead-gate inflation or selected operation-count discrepancy was found. This is not a proof that every mathematical argument in all six reports is correct. The new report should import only the precise compiler/Pell interfaces it needs and explicitly prove the new composition, especially sign and positivity constraints. No global simplicity minimum is known or claimed.
