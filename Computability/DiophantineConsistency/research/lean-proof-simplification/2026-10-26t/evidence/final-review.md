# Independent review of the surviving simplification proposals

Source commit: `6f46a5e3480a2fa2e45993b8090826f256aeaa56`.

This is a read-only review of the proposed Lean changes and their evidence. The reviewer inspected source, diffs, proof statements, accounting files, and the authors' compilation/axiom receipts. The reviewer did not run another Lean build. The final integrated-overlay receipt records ten changed modules, candidate and baseline axiom audits, and the boundary-example check, all with exit status zero. The reviewer matched all ten module hashes against the final source metrics. Lexical declaration-header comparisons are recorded in `static-independent-review.json`; those comparisons are not a substitute for elaborating the declarations.

## Overall conclusion

Four structural directions survive the conservative novelty comparison: exact library list-encoding adapters together with parent-checker specialization; a common local coefficient-fibre theorem; a shared first-failure boundary theorem; and absolute-coordinate reasoning in the fundamental Pell-unit proof. These are claims of additional proof-engineering opportunities relative to the audited corpus, not claims of new mathematics or global novelty.

The `ForkCertificate` candidate is deliberately omitted. Its final short implementation uses `simp` and `omega` across natural/integer casts, a mechanism already recommended in the incoming review. A different theorem target alone would not make that mechanism additional. The aligned-cell additive equivalence, quotient-modulus residue API, and other previously proposed families are also excluded. The authoritative decisions are in `candidate-novelty-review.json`, with the broader 60-family exclusion ledger beside it.

The four retained directions have different payoffs. The quadratic and Pell patches reduce source locally. The first-failure theorem reduces duplicated reasoning in the callers while increasing helper-inclusive source length. The final encoding packet separates its small core improvement from an optional further reduction with an explicitly reported classical axiom dependency; see below.

All savings are measured against exact pinned source witnesses. They are not a measured whole-project reduction after mechanically applying every earlier report. The requested assumption that earlier ideas have already been applied was used to exclude their mechanisms. Targeted patches should be rebased onto such a branch; copied complete source snapshots are replay references and should not overwrite earlier adopted changes.

## 1. Library list encoding and the parent checker

The proposed identification preserves the literal existing numeric code. The workspace recurrence is zero for the empty list and `Nat.pair x codeTail + 1` for a cons; the library encoding has the same recurrence. Equality is proved by list induction. The attempted `rfl` proof failed, so the report must say **extensional equality**, not definitional equality.

The parent-checker proof follows from an existing stronger theorem. `check_raw_iff` reconstructs an encoded parent list from an arbitrary natural input. After moving it above `check_lists`, encoded-list injectivity removes the existential witness. No decoder, fuel convention, raw acceptance criterion, or literal encoding is changed. The old `check_lists` theorem's hypotheses and conclusion are preserved.

The separate table-length adapter uses `Encodable.length_le_encode` after mapping `rowCode`; it is valid mathematically. Axiom auditing found a material distinction: the old `length_le_tableCode` uses `[propext, Quot.sound]`, whereas the direct library-instance adapter adds `Classical.choice`. The old and new parent `check_lists` use the same standard three axioms. This is a library dependency, not a new custom axiom or an unsound oracle, but it must not be described as unchanged per-theorem axiom usage. The final packet correctly resolves this by retaining the encoding/parent change as the core patch and placing the length-bound adapter in a separate optional patch with the exact difference disclosed. The rejected `rfl` experiment and obsolete candidate files are absent from that deliverable.

The final core patch measures 360 to 356 physical lines across its two files, including the import and equality helper: **4 net physical lines saved**. The optional patch saves 4 more, making the combined three-file total 461 to 453. Relevant core proof bodies go from 13 nonblank lines to 5 including the helper body. All three complete after-modules of the combined variant have exit-status-zero receipts with final source hashes, and the standalone adapter file also compiled. The canonical packet is `checker-work/deliverable/`; earlier experimental metrics are not interchangeable with these final metrics.

## 2. Common local coefficient-fibre theorem

The new `QuadraticFiber.coeff_square_at_isolated` isolates exactly the mathematical condition needed for one coefficient. For a weight map `w`, only the fibre of `w i + w j` is constrained: it consists of `(i,j)` and `(j,i)`. Other exponents may collide. The diagonal branch counts its one ordered pair once; the off-diagonal branch yields `2 * u i * u j`. The theorem works over any commutative semiring, including characteristic two, and does not smuggle in global Sidon injectivity, an order on indices, or characteristic-zero assumptions.

The existing global-Sidon and selective theorems become specializations of this common lower theorem. The public statements and old executable definitions remain unchanged. `MultiQuadraticCoding.coeff_row_eq_zero_of_outside` additionally specializes the existing selective off-target theorem; its residual numerical noncollision proof still uses all required support/target bounds.

The dependency description must be precise. This is a common lower theorem plus specialization. `SelectiveQuadraticCoding` still imports `QuadraticCoding`; `MultiQuadraticCoding` now imports `SelectiveQuadraticCoding`. It is not a wholesale reversal of the dependency graph. The broader import is acyclic, but no elaboration-speed benefit was measured.

Final accounting includes the entire 32-line helper: **413 to 393 physical lines**, **306 to 281 nonblank/noncomment code lines**, and **17,062 to 16,632 UTF-8 bytes**. Thus the measured net saving is 20 physical lines, 25 code lines, and 430 bytes. The four-module validation script/receipt now includes `MultiQuadraticCoding`, with exit status zero for all four modules. The five selected changed theorem axiom lists match their baselines exactly: `[propext, Classical.choice, Quot.sound]`.

The independently checked mixed-product prototype is optional. It is not a required dependency or part of those savings, and the existence of a more general prototype alone does not justify expanding the production API.

## 3. First failure and initializer-strip walls

`FirstExit.exists_first_failure` correctly returns a first failing index between supplied bounds, its failing predicate, a good interior, and the disjunction `k = a ∨ P (k - 1)`. The disjunction is necessary: an immediate failure at the starting index, including start zero, must not fabricate a predecessor fact. In the noninitial branch, `a ≤ k` and `k ≠ a` give the positivity and subtraction bounds needed by the final two `omega` steps.

The left-wall caller uses start 1 and bound `N`; the right-wall caller uses start 2 and bound `N+1`. Their positive-period hypothesis supplies the corresponding bound condition. The original periodic departure witnesses remain in each caller. Tile-edge orientation and seam classification remain local and unchanged. The helper replaces only the duplicated least-failure and predecessor reasoning. Existing public theorem signatures are unchanged.

No further statement change was identified that improves clarity and materially reduces proof work. Returning the predecessor as a disjunction lets each caller use one direct case split. A structure, additional notation, or condensed conjunction formatting would mostly change presentation.

The production client shrinks from 148 to 133 lines, but the new helper has 28 lines: **148 to 161 production lines overall, an increase of 13**. A separate 12-line validation example file is outside that production count. Moving validation examples or comments between files is not a mathematical source saving. This direction should be presented as simplification by centralizing two minimality arguments, with an explicit helper cost. Any future break-even claim needs actual further call sites rather than hypothetical savings.

The recorded checks cover the helper, two boundary examples, and the changed `WangTiles942InitialStrip` module, each with exit status zero. The final optional first-exit patch and combined patch include the new-file hunk for `FirstExit.lean`, resolving the earlier packaging condition. The combined patch likewise contains the new `QuadraticFiber.lean` helper hunk.

## 4. Pell fundamental-unit minimality

The changed theorem preserves the exact hypothesis `0 < Q` and the same fundamental unit `(2Q+1, 2)` for discriminant `Q(Q+1)`. For a competing solution with first coordinate greater than one, the existing Pell theorem supplies nonzero second coordinate. Assuming its square is below four gives `0 < |y| < 2`; discreteness yields `|y| = 1`, hence `y² = 1`. The norm equation then places the positive first coordinate strictly between consecutive integers `Q` and `Q+1`. This contradiction establishes `4 ≤ y²`; the original comparison of nonnegative squares finishes the first-coordinate bound.

This removes sign enumeration while retaining the square-gap argument and all positivity conditions. It does not assume that every Pell solution has positive second coordinate. The positivity of `Q` is essential and retained. There is no new helper or import in the production patch.

Final file accounting, with the original whitespace separation retained, is **671 to 663 physical lines**, **577 to 569 code lines**, and **32,947 to 32,518 bytes**: 8 lines and 429 bytes saved. Earlier 9-line claims included a removed blank separator and should not be used. Exact original and replacement declarations, together with the exact `firstUnit` definition, were compiled under the same narrow imports; their standard three-axiom lists match. The later final integrated-overlay run also compiled the complete changed `NativePellBootstrap` module with its production imports and final source hash `e8caed370201e33f2c41a5a26f43d09e3fbe0a279ebb47d5416c0de8f7d654bf`, with exit status zero. Thus the final evidence covers the complete replacement module as well as the earlier extracted-declaration check.

The optional generic minimal-y-square criterion is a useful architectural prototype but adds code. It is not required for the production patch and is not counted as a reduction. If adopted later, the existing private consecutive-square-gap lemma in `MinimumNorm.lean` should be exposed or relocated rather than copied again.

## Evidence and presentation conditions

- Keep the canonical patches, new helper files, exact dependency pins, source hashes, compilation commands/receipts, and selected axiom logs together. Empty compiler logs need their exit-status receipt to establish success.
- Distinguish baseline dependency compilation, changed-module compilation, and extracted-declaration compilation. A baseline `.olean` does not establish that a replacement module was checked.
- Present code counts with their definition and include new shared helpers. Optional prototypes and validation examples should be clearly identified and excluded from production counts consistently.
- Do not describe a proof as definitionally equal, all axioms as unchanged, or a complete module as validated when only a weaker fact was checked.
- The archive audit inventories 329 files and 400 members of five incoming ZIPs. Eleven principal manuscripts were inspected by sections and supplementary material was searched. This is not a claim that every incidental copied source snapshot, binary, or transitively linked historical report was independently read.

## Final integrated evidence reconciliation

The final ten-file overlay agrees with every recorded after-file hash, UTF-8 byte count, and physical-line count in `evidence/source-metrics.json`. With both optional patches selected, totals are 1,693 to 1,670 physical lines, 1,359 to 1,319 code lines, and 76,582 to 75,864 bytes: reductions of 23, 40, and 718 respectively. Without first-exit factoring, reductions are 36 physical lines and 43 code lines. Without either optional patch, reductions are 32 physical lines and 39 code lines. These are the exact selected local production-file sets, not whole-project estimates.

The final baseline/candidate axiom logs agree for every inspected pre-existing declaration except the explicitly optional `AnnotatedRename.length_le_tableCode`, which adds only `Classical.choice`. The three new helpers have the standard three-axiom dependency set. The final receipt is `evidence/final-validation.json`; reviewer reconciliation confirms all thirteen recorded checks succeeded and all ten production module hashes match the metrics.
