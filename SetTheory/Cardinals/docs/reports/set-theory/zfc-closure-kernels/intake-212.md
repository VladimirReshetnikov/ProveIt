# Batch 212: checked affine cores and the CM215 endpoint

Source 179 is **K215: Checked Affine Cores and a Completed CM215 Endpoint**, from `6f0d42d368506bc29c70ace1c992ed88b2651346`. Placement `9740f2bd137313755f8b133be4717c77e8be9fb5` preserves the exact delivery and retires its ZIP. This is an addition to the existing report, using the reconciliation-note option; the base article and its label set remain unchanged. The collection still has 290 reports. Sources 165–166 and the independent mathematical reconciliation of upstream batches 209–211 remain pending.

The useful contribution is a generic proof that complete register-draining loops can be replaced by their exact affine effects, together with literal source-to-graph bindings and recorded integration checks for the existing CM215 machine. Ordinary source review found no mathematical defect in these arguments. **No supplied program or proof compiler was executed at this intake.** The submission's Coq and Lean successes are evidence for its recorded snapshot, not a fresh check of the current maintained endpoint.

## Provenance and recovery

The delivery is pinned to `56e487ce8fa4cf63ad169ffe0cd2944e9fc62dd3`. Its [attribution notice](179-affinecm-0003-NOTICE.md) credits the existing calculi, calibration, machines, normalized certificates, affine decomposition and CM215 design. It attributes the new generic drain/contraction proof, literal source binding, integration work and search audits to this packet. Existing licenses are retained.

The [placement note](intake212-placement.md) and [member map](data/intake212-placement.json) account for all **862 members / 11,367,916 expanded bytes**: 338 new ancillary files, 462 immutable Git aliases, 24 delivery aliases and 38 arrival-only members. The latter are six main manuscript/README/PDF files and 32 raw logs excluded by the existing Git ignore rules. Every ignored log, including failed attempts, remains exactly recoverable from the committed arrival. The [recovery helper](code/intake212-recover.py), positive control and both rejection controls cover every member. No checksum-manifest contents were validated or normalized.

The [ordinary review and own literal checks](data/intake212-review/README.md) preserve the review boundary and the first own parser correction. The portable reader independently checks the finite graph and rank facts, both location-tree domains, and all 430 old CM table actions. It does not execute the delivery's source-segment checker, simulator or compiler.

## What the affine proof establishes

A graph vertex tests register r, decrements it on the positive branch, and applies a finite list of nonnegative increments. When the positive successor is the same vertex and those increments add nothing to r, a starting value k gives exactly k positive steps followed by the zero branch. The resulting register file is

- r becomes the zero-branch increment b_r;
- each other register i becomes R_i + k a_i + b_i.

The argument allows repeated entries in the increment list and arbitrary natural-valued register files; unused registers are preserved. [DrainCore.v](code/179-affinecm-0008-DrainCore.v) carries pointwise equality explicitly. Its finite normalization theorem preserves halting for any fuel. The separate rank data establish that six drain hops suffice for this particular graph.

[CoreContraction.v](code/179-affinecm-0007-CoreContraction.v) requires a genuine graph step before each normalization. This positive progress is essential for reflecting finite halting, and its induction uses the original finite halting budget. [SourceGraphBridge.v](code/179-affinecm-0015-SourceGraphBridge.v) checks the exact tested register, branch address and increment counts. Address equivalence is used at the proved segment boundary; it does not discard a prefix before the segment has run.

The concrete data have **1,426 vertices, 1,059 drains and a 367-vertex retained set**, comprising 366 tests and one halt. Our restricted literal reader confirms those counts, unique sorted keys, closure of both successors, rank at most six, and the six-hop normalization property. Both location tables cover all 1,426 vertices. The delivered formal checks additionally establish the 2,852 literal bindings to `p215` and `dagPerm`; this latter claim was read, not replayed. The [delivered proof receipt](data/179-affinecm-0012-PROOF_RESULTS.json) records 17 Coq 8.18 modules, 25 closed assumption reports and recursive checking. It is an auxiliary source/core proof, not a new production Rocq binary/ZFC build.

This is promising for comparing future programs with different implementations of transfer, copy or clearing loops. The existing normalized correspondence is already a direct proof for the current pair. The generated graph and location tables total **284,987 bytes**; the retained graph does not itself establish a smaller proof archive, faster full build or fewer binary machine states.

## CM215: existing transport, new integration evidence

The seven CM215 implementation modules are exact aliases of the earlier [transport proposal](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/k215-transport/README.md). The new [typed audit](code/179-affinecm-0091-CM215Audit.lean) and submitted integration receipts attach that design to the old dependency snapshot. The inherited wrapper's older standalone-check limitation is preserved as historical text rather than silently edited.

Our literal read confirms that its old table is the current exact 430-action dense K215 table. Its alternative also has 215 working states and differs in six rows. The transport invariant is over arbitrary function tapes: state 52 has a one immediately to its left; state 170 either reads one or has zero to its left; state 151 has a one immediately to its right. It holds at initial state 0 for every tape and head. A noninjective map identifies old state 170 with 52, and the marker distinguishes the exceptional three-step paths. Other simulated steps take one transition.

The generic positive-stutter theorem proves both directions of halting from terminal agreement and strictly positive finite simulation blocks. The core bridge separately handles the standard machine's absorbing halt and the partial transition relation's terminal `none`. The resulting endpoint transfers the already established old-machine ZFC calibration; it neither assumes a new axiom nor proves unconditional nonhalting. Ordinary source review found these distinctions correctly represented. The packet reports eight checked modules and 14 axiom reports for this integration, with the standard Lean axioms listed explicitly. No current-provider CM215 kernel check was run at intake.

## Comparison with the maintained proof

The packet's older 188-file snapshot must not replace the current shorter proof. Its seed-model patch and memory batching remain attributed historical experiments. Current shared seed semantics occupy 311 lines / 13,793 bytes across `KSeed222` and `KSeedModel222`; the latter alone is 116 lines / 5,148 bytes. The submitted seed-model variant is 234 lines / 10,436 bytes. Its four certificate overlays split old 140-entry checks into four 35-entry lemmas, adding 100 generated lines; this repairs a recorded memory failure rather than shortening those proofs. The original exit-137 attempt and failed initial CM audit remain recoverable.

Two decoder gaps described by the manuscript have since been closed in the maintained phase-nine proof:

- [`DecoderSourceBinding.lean:30`](../../../../../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/DecoderSourceBinding.lean#L30) states `sourceTree sourceNodes 203 sourceRoot = KSource215.t215`; its routed source-path results follow at lines 61 and 76.
- [`KDecoderPrefix215.lean:154`](../../../../../../Computability/BusyBeaver/Lean/BusyBeaver/ZFC/KDecoderPrefix215.lean#L154) gives one exact routed leaf port followed by `∀ n vs, ∃ steps`, preserving the full prefix and register frame.

The remaining simplification is the exposed primitive/return suffix family. It still needs arbitrary register values, exact full-prefix languages, and the relevant zero/nonzero guards. Neither a physical state alone nor two preceding bits is a sufficient general leaf interface. The current full proof retains all **4,751 leaf occurrences and 6,176 guarded branch checks**; these prefix results do not replace them by 97 complete contracts. See the [maintained phase-nine checkpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase9/README.md) and [subsequent generic-core checkpoint](../../../../../../Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/phase10/README.md) for their actual formal boundaries. This intake changes none of those sources or producers and makes no new PA claim.

## Failed 214-state experiments remain useful negatives

The no-append experiment changes native row `66/0` from `1 R 198` to `0 L 54` and deletes state 198. The submission reports a quantified symbolic success for 1,900 increment occurrences, using 672,539 rules, but it also supplies a decisive zero-decrement contract failure. At source index 2, address `0100`, with all nine registers zero, gap zero and spare suffix `[0]`, the parent returns in 640 transitions. The edited machine returns in 3,966 transitions with different continuation bits and registers `[0,0,0,0,0,1,0,0,2]`. The positive increment result does not validate the machine.

The separate relaxed-spare screen has 24,824 tables and 59 short survivors: 50 wrong outputs and nine exact cycles. The coordinated-provider family has 639 tables: 338 wrong outputs, 223 outward blank rays, five cycles, two unexpected halts and **71 bounded failures**. The last category remains bounded; it is not promoted to a divergence proof. Providers 95, 188 and 213 match first decoded frames but later fail at source indices 4,578, 4,572 and 4,560. Their bad finite prefixes precede all register-dependent cells, which explains the claimed all-register obstruction at those addresses.

The parent source's eventual gate visitation is an ordinary argument using inherited total macros and literal mapping. It does not prove that a modified physical machine reaches that gate, or that it has the wrong blank-tape consistency behavior. These records rule out the stated uniform-runtime contracts and bounded families, not every possible 214-state construction. No verified machine with 214 or fewer states, minimality theorem or state-count lower bound is claimed.
