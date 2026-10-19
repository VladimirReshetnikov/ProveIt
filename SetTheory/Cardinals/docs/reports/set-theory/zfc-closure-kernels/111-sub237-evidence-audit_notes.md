# Independent audit of the inherited 237-state candidate

Audited package: `intake/archive3/zfc237-research-20261019`.
Auditor output directory: `audit_work`.

## Conclusion

The 238-to-237 local reduction is sound as an ordinary all-tape halting-equivalence theorem. The fresh finite/source/local/startup replay passed. A fresh complete unbounded runtime replay of the exact inherited-label 237-state table also passed; every deterministic proof field and all 8,386 per-case bytes agree with the shipped evidence. No gap was found in the stated three-rule affine/list engine or the new local fold.

The endpoint is an ordinary mathematical proof formalizable in ZFC, with the earlier logical-calibration argument explicitly inherited. This audit does not claim to have built the ancestor Lean dependency closure or produced a kernel-checked final binary endpoint or an internal ZFC proof object.

## Exact identities and fresh evidence

* Inherited-label 237-state table SHA-256: `a3c4407f30e2e2139af87c6a91948c518134855841a28eb85b1d81bcfd026c9a`.
* Canonical 237-state table SHA-256: `7eda1da1fcda629cae86d22b01d3faf419552cf04ed4179f0c045ad0adf2c1a6`.
* Fresh complete runtime: 8,386 guarded cases, 2,261,369 symbolic rules, all 474 literal rows, minimum positive instruction duration 13.
* Fresh full runtime summary: `universal237_fresh.json`; case array: `universal237_fresh_cases.json`.
* Case-array SHA-256: `573e2d88400030c9457ab028c701102205124875f69aedd6acfa7f9341cd8c25`, byte-identical to inherited evidence.
* Finite replay receipt: `replay237_quick/replay.json`, status `PASS_QUICK_REPLAY`; all 11 constructor/bootstrap/source/local stages pass.

The complete runtime took approximately 268 seconds in this environment; elapsed time is operational metadata, not mathematical evidence.

## Local all-tape proof audit

Let M denote the inherited 238-state table and N the 237-state table, in inherited labels. Delete 235; map old 235 to retained 98; redirect 139/1 and 156/1 accordingly; change 98/0 to 0 L 240 and 240/1 to 1 L 87. The remaining 470 retained rows are unchanged.

The old-run invariant is:

* At 98 or 240 the immediate left bit is 0.
* At 139 or 156 the immediate left bit is 1.
* At 235 both the immediate left bit and the next bit left are 1.

The invariant is vacuous at start 95 on every binary tape, and every implication follows inductively from the complete incoming-edge inventory. No valid-frame premise, empirical window-completeness assumption, or blank-run-only inference is needed.

The exceptional simulated old rows are 98/0, 235/0, and 240/1. They correspond to paths of length 3, 5, and 3. Every write on these paths preserves the read bit; every read is at a position fixed by the old invariant and old read bit. Every endpoint has the old head displacement +1 and exact old target 113, 231, or 99. All 473 other old rows commute through the state map in one step. Positive finite blocks and absence of interior halts imply two-way halting equivalence, including the infinite-run direction.

Both packaged local checkers were freshly replayed. The second uses partial-assignment entailment and is independent of the first Boolean-window implementation.

## Why the runtime induction is unbounded

The symbolic state stores left and right tape words at a moving boundary and a direction indicating which side contains the head. Reversing direction while leaving the just-written cell on the same side is consistent with one-cell head motion. The independent affine motion variable accounts for physical displacement and is checked at nonhalting endpoints.

The engine has three execution rules:

1. A literal finite-table transition consumes one certainly present cell. A run with unknown natural length cannot supply that cell unless its constant term is at least 1.
2. A homogeneous-run shortcut is permitted only when the literal row is a self-loop moving in the scan direction. Induction on run length proves it, including length zero. It writes the correct symbol to the entire traversed run and accounts for exact length in clock and motion.
3. An opaque finite spare-list traversal is permitted only after the one-block schema has been rederived on the exact table. Each schema holds for an arbitrary natural block value and arbitrary exterior contexts, preserves the entry control and scan direction, and uses exactly v+2 steps. Structural induction on the arbitrary finite list proves the list shortcut. The list width variable denotes the sum of these block widths; treating it as nonnegative is sound and only weakens constraints.

Normalization combines adjacent homogeneous runs, deletes zero-length runs, absorbs finite zero runs in an infinite zero exterior, and uses the identities C(A)1=1B(A) and their reversals. With B(v)=0 1^(v+1) and C(v)=1 0 1^v, the one-block identity is direct and its finite-list extension follows by induction.

All nine register values are independent natural variables. A decrement guard splits into zero or one plus an arbitrary natural variable. The extra gap, first spare value, and entire finite spare tail remain arbitrary. Every nonhalting endpoint must equal the full symbolic frame, including spare list, exterior zeros, control, and head orientation; its clock has nonnegative coefficients and positive constant. Every halting source instruction must reach actual halt state 254. The 4,000-rule cap limits certificate discovery, not register values or machine running time.

## Calibration scope

The retained `CalibratedRotation240.halts_iff_zfc_refutation` identifies the exact calibrated register program and `LogicalSeed246.initial` with finite derivability of falsity from the actual `ZFCax_s` theory. The source-interface and source-graph checks identify the changed leaf list with that program and seed.

The reported ZFC formalizability is based on the mathematical content of the ancestor arguments: finite syntax, a quotient and internally well-founded part, first-order soundness/completeness, and the constructible submodel for ZF/ZFC equiconsistency. It does not infer a theorem of ZFC merely from the fact that a Lean theorem exists. The finite-tree derivation representation has the usual effective coding of first-order proofs. The detailed ancestor proof is cited, not reconstructed here.

The equivalent statement itself needs no consistency assumption. Under Con(ZFC), nonhalting follows and is unprovable in ZFC by the usual second-incompleteness argument. Bare consistency does not establish unprovability of halting; that stronger conclusion needs an additional arithmetic-soundness assumption.

## Comparison of incoming candidates

Archives 0, 1, and 5 all contain exactly the same inherited-label 238-state table: SHA-256 `069942be27db9736875ea042320e51ac3b1eac7116cbe01cdce520fa6056f78c`. It is already the input of the 237-state reduction. Their apparent multiplicity contributes no further state savings.

Archive1 has a separately explored source of maximum depth39, still with224 distinct subtrees; it is not compiled into its certified238 table. Archive5 has a713-bit finite equational packet, not a charged complete binary interpreter. Neither number is an additional TM state reduction. Archive0's relational-congruence theorem also does not license deleting a numerical logical row without a new complete-calculus argument.

## Completed initial search families

A direct shifted-head family mapped a deleted state q to a retained p at offset plus or minus2, flipped the common incoming direction, and left all other retained rows unchanged. On the inductively closed radius5 state-window abstraction from arbitrary tapes at start95, 93,113 windows and48,616 eligible pairs yielded no candidate with old/new block caps65. The search code and log are in `shifted_fold_search.cpp` and `shifted_alltape237.log`.

A larger empirical search allowed both retained rows to be synthesized and encoded q by flipping the old tape bit immediately opposite its common incoming direction. Each q-entering transition flips its written bit and enters p. This searched49,324 ordered pairs and93,123,712 row choices against the radius5 empirical profile, yielding no candidate. Code/log: `tag_toggle_domains.cpp`, `tag_toggle237.log`. This is only a negative result within that bounded search family, and the empirical windows are not a proof of all runtime contexts.


## New independent proof checker

`verify_representation.py` is a new independent implementation. It builds the least fixed point of the old table's finite window transition relation, starting from every radius-R window at state95. Newly exposed exterior bits are branched both ways. This is an inductive overapproximation of every old execution on every initial binary tape.

For every admitted nonhalting checkpoint window, the checker proves equality between the mapped endpoint of a positive old block and the exact endpoint of a positive new block. Both runs are prohibited from reading outside the represented window, and any representation-dependent cell must be represented. Thus equality of finite tape integers proves equality of whole tapes with arbitrary common exterior. Halt stops a block; no accepted block contains an interior halt. Induction over corresponding positive blocks proves two-way halting equivalence.

The representation supports a constant state merge, a head shift, a toggle of one nearby tape cell, and a split in which a tape bit selects one of two new states. In the split case the old alternate state is an internal helper and is excluded from checkpoints; the checker verifies every incoming edge to it originates in the deleted state or that helper itself. Hence no unaccounted ordinary checkpoint can enter the omitted helper.

Fresh results:

* The 238-to237 fold passes with radius2, old-block cap1, new-block cap5:3,282 admitted cases (3,266 of length1/1,12 of length1/3,4 of length1/5). Receipt:`independent237_representation.json`.
* The preceding 240-to239 contextsplit passes with radius2, old-block cap3, new-block cap5:3,248 admitted checkpoint cases;16 additional old-helper windows are excluded only after checking its incoming-edge condition. Receipt:`independent239_contextsplit.json`.
* Restoring helper240/1 to its old1R99 action in the237 table is rejected at old235 with local window11000. This is a negative control of the local certificate, not a claim that the mutated blank run halts. Receipt:`negative_helper_receipt.json`.

The code accepts inherited-label tables without a start header because the theorem checked explicitly starts at95. If a start header is present, it must also say95. It rejects table incompleteness, duplicate rows, extra/missing ordinary states, an invalid halt target, and disabled Python assertions.


## Completed tape-tag/helper searches

The larger tape-tag search was also completed with one helper substitution chosen from the 601 individually neutral row substitutions. It searched 49,324 ordered pairs, 93,123,712 row choices, 1,118,565,120 helper checks, and 1,889,504,012 context tests, yielding zero candidates. Its radius-5 empirical input has 28,414 state/windows; old and new block caps are both 65. Runtime was approximately 527 seconds.

After the new source product invariant was independently checked, the same representation/helper family was rerun on a source-constrained profile, restricted to ordered pairs involving at least one of the affected states 113, 172, or 204. This profile includes the exact blank initializer and contains 29,192 state/windows. The focused search completed 1,326 ordered pairs, 2,503,488 row choices, 28,551,112 helper checks, and 42,587,093 context tests, yielding zero candidates in approximately 9 seconds.

The complete audit search counters are:

| Family | Ordered pairs | Row checks | Helper checks | Context tests | Candidates |
| --- | ---: | ---: | ---: | ---: | ---: |
| Unchanged-row head offset, inductive all-tape radius 5 | 48,616 | — | — | 51,136 | 0 |
| Neighbor tape tag, empirical radius 5 | 49,324 | 93,123,712 | — | 129,187,531 | 0 |
| Neighbor tape tag plus one neutral helper | 49,324 | 93,123,712 | 1,118,565,120 | 1,889,504,012 | 0 |
| Source-constrained focused tape tag plus one helper | 1,326 | 2,503,488 | 28,551,112 | 42,587,093 | 0 |

All four search sources, exact input hashes, completed logs, empty candidate files, and compile/run arguments are staged under `research/binary_search`; the authoritative audit receipt is `audit_search_receipt.json`. These are completed searches of specific finite families. They prove no lower bound and do not rule out transformations outside the representations, helper options, windows, and block bounds searched.

## Independently checked source product invariant

`verification/check_source_product_invariant.py` is a new standalone standard-library checker which imports no discovery implementation. It independently rebuilds the complete prefix-free source tree and all register-program control-flow edges, then checks the supplied annotation is a post-fixpoint containing the actual seed (3,0,0,0,3,0,0,0,0). A least-fixed-point calculation is unnecessary for soundness: seed inclusion and every guarded transfer inclusion suffice by induction on source execution.

The threshold-16 one-register domain has singleton atoms 0 through 15, the even tail E={16,18,...}, and the odd tail O={17,19,...}. A nine-register annotation is the Cartesian product of nine unions of these atoms; bottom marks no reachable register valuation. The checker derives the concrete action of increment and positive decrement on the corresponding arithmetic progressions, computes their covering atoms, and checks every inclusion. This is a sound abstract transfer, not an exact representation of all concrete single-register images. For example, the image of 15 under increment is {16}, which is abstracted to all of E; incrementing O omits 16, although the abstraction is again E. This precision loss is harmless for the post-fixpoint argument.

The checked graph has 6,455 leaves, initial leaf 0, maximum path depth 48, and 6,452 nonbottom annotations. There are 8,380 enabled nonhalting edges (2,595 increments, 1,929 positive decrements, 1,931 zero decrements, and 1,925 jumps), plus one halting leaf. The independently checked facts establish:

* Leaf 6314, path `111010010110001110`, can execute only with logical register R6 equal to zero.
* Leaf 6429, path `111111000`, can execute only with logical register R1 equal to zero.
* Leaves 6315, 6430, and 6431 are unreachable from the calibrated seed.

The receipt is `evidence/source_product_k16_independent.json`. Source, annotation, summary, checker, and independent graph hashes are recorded there. Negative controls reject omission of the seed's R0=3 and reject widening the forced-zero R6 annotation to allow 1 when its positive successor remains bottom.

This finite certificate proves unbounded source reachability facts; it is not merely a trace observation. The facts can justify ignoring unreachable source leaves or disabling impossible source guards. They do not by themselves license removal of a binary machine state.

## Source-restricted unbounded binary runtime bridge

`verification/check_source_restricted_runtime.py` connects these inductively proved source facts to the inherited affine/list binary engine. It first runs the independent source annotation check, validates the literal table interface and census, rederives every opaque-list schema on that table, and cross-checks the engine's path arithmetic against the independently rebuilt source graph at every leaf.

For each admitted leaf and source guard, the wrapper covers each register's atom union by an affine family m+d*N. Here m is its least allowed value and d is the greatest common divisor of every finite difference from m, including 2 when an infinite parity tail is present; d=0 represents a singleton. Every concretely permitted value is in the resulting family by integer divisibility. Decrement guards are restricted before this enlargement, so a zero guard remains exactly zero and a positive guard has a positive lower bound. The register variables stay independent and all other frame components remain arbitrary.

The ordinary literal-step, self-loop, and finite-list induction rules are unchanged. For each enlarged affine frame the wrapper proves the exact source instruction endpoint, entire tape, control, head position, and a positive actual step count. The enlarged affine families need not be invariant: the source post-fixpoint supplies the narrower concrete invariant at successive source checkpoints. This separation is what makes the restricted universal checks sound.

A fresh run on the unchanged 237-state table passed all 8,381 enabled instruction/guard cases, using 2,249,105 symbolic rules, with minimum instruction duration 13. All 474 literal rows were still used directly. The summary and full case array are `evidence/restricted_runtime237.json` and `evidence/restricted_runtime237_cases.json`. The case-array SHA-256 is `b359d39135f4cb12323b28a05ea5651314a96d10afc8da52dfa3bd5ff8741e9d`.

The exact blank initializer remains an explicitly separate proof obligation, already checked for the inherited 237-state table. With that initializer, induction over source checkpoints gives source/binary equivalence from the blank tape. These source facts and the restricted wrapper are suitable for certifying future dead-subtree or forced-zero modifications, provided the checked live source interface and exact initializer remain valid. No state reduction follows merely from the smaller guarded-case count. The endpoint is an ordinary mathematical proof with executable certificates; this work has not produced a kernel-checked final TM theorem or a serialized internal ZFC derivation.
