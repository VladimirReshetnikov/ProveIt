# Novelty audit for a further DiophantineConsistency Lean review

Reviewed 26 October 2026. Final source baseline: `6175dff9a15491497c7a3c1bda4f6a62a6349c74`.

## Corpus and scope

The current `docs/incoming` directory has two files: its README and `diophantine-lean-simplification-2026-10-26.zip` (300,573 bytes, Git blob `065a4cbf9fde2ef0b15db9898920e84d7a3b49fb`). I read the whole incoming README for relevant entries, unpacked the current ZIP, read its report/README, inspected the Lean prototype declarations and independent reviews, and also read the earlier DiophantineConsistency simplification packet explicitly linked by the incoming README.

The earlier packet is at `Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/`. Its arrival was `151a732b91`; its `PLACEMENT.md` says the original archive was retired after placement and all content was retained except 14 ignored log files. The README's link to `ADOPTION.md` is unresolved at this baseline. No adoption state should be inferred from that missing link. Both reports themselves reviewed the older code baseline `60e9c5d620c6c387d932876cfa2d9376f64ea56c`.

The audit treats ideas stated only in source notes, uncompiled proposals, or "further questions" as already proposed. Completing their implementation would be useful engineering, but it would not satisfy a claim that the idea is new to this incoming-review corpus. The audit is not a claim of mathematical novelty in the wider literature. Historic BusyBeaver simplification packets are indexed by the README too; this review does not exhaustively open their hundreds of ancillary files. Their visibly summarized general ideas (shared recursion/quotient syntax, shared implication successors, semantic bridges, invariants and automatic certificates) are not claimed as new either.

Source shorthand:

- **A**: placed packet `research/lean-proof-simplification-20261026/`.
- **B**: current archive `docs/incoming/diophantine-lean-simplification-2026-10-26.zip`.
- Source module paths below are relative to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## Excluded ideas: exact scope and pointers

| ID | Existing idea | Targets and prior pointer |
|---|---|---|
| E01 | Transport equality under `Nat.rec` directly; reusable recursor congruence instead of repeated induction | `ScalarPRCode.Realizes.prec`, `PRCode.Realizes.prec`, `ScalarPROptimizer.eval_optimize`; A report, "Rewrite under primitive recursion"; A `lean/RecursorCore.lean` and `checked-modules/`. |
| E02 | Replace private successful-lookup/membership inductions with core `List.mem_of_getElem?` / `List.getElem?_of_mem` | Seven declarations in `AnnotatedProofChecker`, `AnnotatedRename`, `AnnotatedBound`, `AnnotatedRuleSide`, `AnnotatedAssumption`; A/B exact `lookup-api.patch`. |
| E03 | General assignment naturality for `natAssignment` under `Sum.map`; use `Expr.eval_rename` | `Representation`, `QuarticCompiler`; A assignment patch; B report section "Witness layouts" and `lean/WitnessLayout.lean`. |
| E04 | Split and recombine existential `Fin (m+n)` witness blocks via `Fin.castAdd`, `Fin.natAdd`, `Fin.addCases` | Conjunction/disjunction and intended reindex/existsBlock clients; B `WitnessLayout.exists_split_witnesses`. |
| E05 | Move constructor projection/witness-count laws to an earlier import layer | `RepresentationSize` laws already available too late for `DirectComposition`; B report "Move existing projection lemmas to their natural home". |
| E06 | One invariant-preserving checked-history fold with distinct Line/Judgment types, append/soundness/Produces laws | `AnnotatedRename`, `AnnotatedBound`, `AnnotatedProofChecker`; B `lean/ValidatedFold.lean`, report section "Checked histories". |
| E07 | Generic scanner iteration equations, fixed-state/zero absorption and invariant laws | Four/five annotated scanner modules; A `lean/ScannerCore.lean`; B `ValidatedFold.scan_succ` / `scan_fixed`. |
| E08 | Share the encoded-list to typed-fold simulation using `step_cons`, acceptance, update, terminal/rejection encodings | `AnnotatedRenameScan`, `AnnotatedBoundScan`, `AnnotatedLineScan`, `AnnotatedAxiomContext`; B report "Separate recurrence from encoding". Zero vs one terminal encodings explicitly discussed. |
| E09 | Dynamic-seed/input-dependent primitive-recursive iterator `iterateFrom` | `DirectScalarArithmetic.iterate`, `AnnotatedContextPR`, `AnnotatedBoundScan`, `AnnotatedLineScan`, `AnnotatedRenameScanPR`; B report "A better primitive-recursive iterator interface". |
| E10 | Shared numeric tag dispatch and Boolean reflection to exact 0/1 value | `AnnotatedRenameLocal`, `AnnotatedBoundLocal`, scanner `step_cons`; A `BooleanCore.lean`; B report "Share tag dispatch and Boolean reflection". |
| E11 | Central sum-of-squares zero criterion and syntax evaluation/cost/degree API | `ShortSystem.residualSum`, `DAGQuartic`, `NaturalDAGQuartic`, `QuadraticRegisterSystem`, `QuarticCost`; A/B reports and `CompilerCommon.lean`. |
| E12 | Parent exponent labels + existing `run_power` to replace generated pure-power chains | `GapCircuitSteps66`, `SplitCircuitSteps59`; reuse/move `SplitJointPower59` labels; A generated candidate and B two power certificates. Sharding/profiling also already proposed. |
| E13 | Circuit-specific helper for `run_node_equation`, on-demand specialization or thin compatibility wrappers | 999 generated local-step declarations; A generated candidate; B `CircuitDispatch.lean`. Preserve semantic cut points and avoid recursive global expansion. |
| E14 | Share topological induction via indexed invariant to obtain uniqueness, degree and nonnegativity | `ArithmeticDAGSemantics`, `ArithmeticDAGDegree`, `NaturalDAGQuartic`; A `CircuitInvariant.lean` / `CircuitRefactoring.lean`. |
| E15 | Commutative local node relation, accepting swapped add/mul operands; generic circuit-translation skeleton | Exceptional Gap row 421 / Split row 452; A `NodeRelCommutative.lean` and report "Translation certificates". |
| E16 | Move existing syntax-degree interface earlier; derive unweighted from weighted degree at weight 1 | `QuadraticRegisterSystem`, `WeightedExpressionDegree`; A/B reports. Preserve cancellation-sensitive normal forms/exact degree. |
| E17 | Extract generic register-append topology, allowed-node and evaluation lemmas | `NaturalRegisterProgram`; A report and circuits-review.md section 7. |
| E18 | Extract gate data early; specialize existing semiring completeness/soundness instead of duplicate natural induction | `QuarticCompiler`, `GatesSemiring`, `NaturalExpressionSemiring`; B `SemiringSpecialization.lean`; includes moving polynomial rename laws early. |
| E19 | Exact half-radix formula replacing 4/16-case splits | `NativeCyclicRotation.shiftDigits_half_bound`, `shiftDigits_half_parity_89`; A/B checked arithmetic. |
| E20 | Project stronger coefficient congruence at modulus 2048 down to modulus 16 | `CurrentClause2011.reflected_weight_mod` to `CurrentEarlyPadding2011.reflected_mod_sixteen`; A modulus-reuse patch; B report. |
| E21 | Place padding witness under the middle-phase condition, eliminate dummy zero witness | `NativePreliminaryCount2011.total_le_one_all_phases`, `CurrentCount2011`; A conditional-padding patch. |
| E22 | Exact digit/carry decomposition API for quotient, residue, zero carry | Several Clause/EarlyPadding/PhaseParity clients; A `NormalizationArithmetic.lean`; B `NativeRefactorCore.lean`. |
| E23 | Drop redundant stored carry recurrence and derive from digit bound + decomposition | `CurrentPolynomialWindow2011.Facts`; A digits-review section 3; B CarryCertificate and report. Preserve accessor API. |
| E24 | Shared cyclic field-residue calculation for aligned offsets, arbitrary wrapped shifts, off-origin mask lookup | `CurrentClause2011`, `CurrentReflectedGeometry2011`, `CurrentCellTranslation2011`, `CurrentPhaseParity2011`, `CurrentEarlyPadding2011`; A digits-review section 5; B report. |
| E25 | Decode literal source-register/Pell equations once into semantic arithmetic facts | `NativePellBootstrap`, `NativePellPower`; B report "Decode source-register equations once". |
| E26 | Generic finite block/tail dispatcher and data-driven assembly retaining checked leaves | `WangTiles942Data.action_eq_decoder`, rail cache; `CurrentKernel2011` partial sums; B `forall_lt_by_chunks` and report. |
| E27 | Shared four copied-field bounds / finite descriptor carrying offset, width, packed shift | `CurrentCellLabels2011`; B report "One copied-field bound interface". |
| E28 | Definable-induction transport with an explicit formula witness | `ObjectAdditionLaws`, `ObjectMultiplicationLaws`, `ObjectDistributivity`; A report/source notes. Does not permit induction on arbitrary external predicates. |
| E29 | One all-model validity to sealed derivability bridge and shared model-axiom extraction | Many `Object*` endpoints; A/B reports. Additional semiring instance is explicitly already existing, not new. |
| E30 | General closed-sentence/environment transport across arbitrary expression arity | `ObjectQuarticCompiler`, intended `ObjectPolynomial.sat_noZeroForm_at_iff`; B report "Generalize closed-sentence transport across arity". |
| E31 | Generic no-borrow decrement at the origin of a cyclic word | `CurrentHighDigits2011.high_mask_word`, `NativeHighPort54.mask_word`; A source_notes/digits-review.md section 6 (lines 205–228). |
| E32 | Expose physical `Fin 942` sum identity directly instead of prefix-sum round trip | `CurrentClause2011.selectorCount_eq_prefix`, `CurrentOneHot2011`, `CurrentFieldOffsets2011`; A digits-review section 7 (230–247). |
| E33 | Share restored canonical source/window extraction while preserving one coherent `N` | `CurrentSparseDigits2011`, `CurrentHighDigits2011`, `CurrentCarrierArithmetic2011`; A digits-review section 8 (249–267). |
| E34 | Generic profiling/import-layer hygiene/certificate granularity as standalone recommendations | Both reports discuss explicit simp boundaries, source/time/proof-size distinctions, axiom audits, chunk granularity, local `simp only`, and API layering. Such process advice is useful but not a fresh idea for this user. |
| E35 | Aligned cells identified with `ZMod N` to simplify reindexing | B report "Share physical-field residue calculations", just before "Decode source-register equations once": explicitly proposes "A later equivalence between aligned cells and ZMod N could simplify reindexing." A subgroup implementation is a refinement of that old direction, so should not be a fresh headline. |

## Novelty tests for subsequent candidates

1. A candidate should identify a *different repeated argument or theorem interface*, rather than give a renamed version of one of E01–E35.
2. A substantially stronger theorem may qualify if it removes an independent hypothesis, handles a new semantic boundary, or proves a distinct correctness principle. Explain the difference precisely and cite its nearest old proposal.
3. Compiling an old source-only proposal is a new validation result, not a new simplification idea. Do not count it as one of the requested new ideas.
4. Reusing existing public semantics to collapse an entirely different proof can qualify; the old broad advice to "share semantic APIs" does not prohibit all abstraction. The concrete old clients/interface, not a vague slogan, define overlap.
5. Count new helper lines before claiming net savings. This requirement itself is already in the prior reports.

## Provisional gaps worth checking in maintained sources

The two packets are concentrated on representation layouts, scanners, DAG certificates, native field/carry geometry and object-model administration. They do not specifically analyze (a) proof by uniqueness of functional arithmetic graphs to eliminate repeated existential witnesses; (b) reconstruction/projection equivalences for split encodings beyond ordinary witness concatenation; (c) deriving feasibility/zero-set equivalence endpoints by relation algebra rather than fresh bidirectional witness proofs; (d) generic natural-difference bounds or order embeddings used outside the discussed cyclic field geometry; or (e) specialized induction principles for syntax-recursive pair encodings. These are search directions, not verified proposals or novelty claims. Every chosen concrete implementation still needs comparison with the exclusion matrix and its actual upstream source.

## Artifacts inspected locally

- `research-notes/incoming-audit/prior.zip`: exact current archive downloaded through GitHub's base64 file API.
- `research-notes/incoming-audit/extracted/diophantine-lean-simplification-2026-10-26/`: unmodified extraction.
- `research-notes/incoming-audit/incoming_README.md`: full README at final pin.
- `ProveIt/Computability/DiophantineConsistency/research/lean-proof-simplification-20261026/`: placed prior report, source notes and artifacts.

The current directory files have the same Git blob identities at the initially inspected `e73fa2e...` and final `6175dff9...` pin.

## Candidate-specific review

- **Signed congruence up to sign:** the proposed `NativePellStepDown.index_residues` refactor via transitivity of `a ≡ b (mod m) ∨ a ≡ -b (mod m)`, plus `natAbs` transport and `SignedPellResidue` clients, is not covered by E25. E25 decodes literal source-register identities; it does not abstract signed modular arithmetic or replace its four-case compositions. Search of both reports/source notes/prototypes found no signed-congruence/natAbs proposal. Suitable fresh concrete direction, subject to compilation and theorem-preservation review.
- **One-hot support from a library theorem:** replacing `CurrentCellLabels2011.sum_le_one_cases`' manual proof with `Finset.sum_le_one_iff` is distinct from the earlier sum-of-squares, copied-field and physical-sum ideas. No earlier `sum_le_one` refactor found. Suitable fresh concrete direction, subject to checking the library theorem's exact type and edge cases.
- **Aligned-cell subgroup equivalence:** excluded as a fresh direction by E35. A compiled implementation would be new work, but the idea was already mentioned.
- **Shared guarded Euclidean certificate:** the new `ArithmeticCertificates.divMod_certificate_iff` and exact wrappers replacing the literal duplicate `RegisterDivMod` / `QuadraticDivMod` declarations are distinct from E22/E23. Those normalize a supplied carry decomposition; this shares the existential positivity/slack specification between two backends and checks uniqueness of the full quotient/remainder/slack tuple. The source engineering is new to the reviewed packets; the underlying arithmetic is standard. Prototype compiled and patch applies; see `research-notes/certificates/README.md` for exact scope and four-line net saving.
- **Inverse Nat.pair projections:** a generic inverse-equivalence/product-projection principle, applied to certificate-backed Nat.pair inverses, is distinct from E03/E04 (assignment renaming and concatenated finite witness blocks). Its concrete applications must still preserve every witness coordinate and statement. No prior pairing-projection simplification found in the inspected reports/prototypes.
- **Affine sum budgets / max-plus depth:** `GraphSizeBounds`' three `thin_compose` arguments and the numerical depth recurrences of `BoundedForallDepth` are not identified in the prior proposals. These concern amortized depth versus total witness budget, rather than E11's sum-of-squares syntax cost or E16's polynomial degree. Suitable fresh direction if tied to actual callers and the helper overhead is reported.
