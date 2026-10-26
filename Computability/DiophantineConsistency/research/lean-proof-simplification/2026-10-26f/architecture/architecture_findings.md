# Architecture-level simplification findings

**Strongest low-risk proposal:** factor the exact duplicated nine-coordinate packaging proof over its scalar evaluator. **Strongest medium-risk proposal:** parameterize the Split/Gap degree-gap estimates, retaining all numerical specializations and leading-coefficient conditions. **Most valuable current-carrier cleanup:** one shared, normalized source/window bridge, placed below the thirteen-coordinate completeness layer.

Scope: read-only source review at commit `60e9c5d620c6c387d932876cfa2d9376f64ea56c`. All line numbers below refer to `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`. Candidate files are **uncompiled proposals**, not verified patches. Static counts describe current text, not measured savings, runtime, or proof-term size.

## A1. Abstract the exact nine-coordinate packaging duplicate (priority 1; low risk)

**Evidence.** `SplitSourceExistence.lean:98–157` and `GapSourceExistence66.lean:53–112` are byte-identical: 60 lines and 2,292 UTF-8 bytes each, excluding a trailing newline. They define `positiveVars`, `positiveValue`, `naturalVars`, `naturalValue`, and prove positive/natural existence equivalences. See `repetition_evidence.json` for the digest and reproducible scope. The scalar source evaluator is the only information supplied by the surrounding namespace.

- [Split block](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitSourceExistence.lean#L98-L157)
- [Gap block](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/GapSourceExistence66.lean#L53-L112)

**Existing simplification.** Gap already reuses Split's cofinal-cap lemmas (`GapSourceExistence66.lean:12–15`); this proposal concerns the still-duplicated coordinate packaging, not that existing reuse.

**Proposed boundary.** Parameterize a helper namespace by

```lean
abbrev Evaluator := ℕ → ℕ → FreeCarrierRatio.FreeVars → ℕ → ℤ
```

Prove the two equivalences once for an arbitrary evaluator. Retain the original public definitions and theorem statements; their proof bodies become, conceptually,

```lean
exact NineCoordinatePackaging.exists_natural_zero_iff_hasZero
  (GapSourceExistence66.value d a)
```

The delivered `NineCoordinatePackaging.lean` is the complete proposed generic proof; `NineCoordinatePackagingCompatibility.lean` contains four original-statement compatibility examples, two per package. Neither has `sorry` or added axioms.

**Preservation obligations.** Positive tuple order remains `b,g,h,s,w,C,i,j_plus,n`. Slot 7 stores `j+1`, but `FreeVars.j` itself is an unrestricted natural; the natural tuple does not add one to this internal index. Do not impose `0 < v.j`, and do not drop positivity of `g` or `n`. The generic theorem assumes no source correctness or zero-existence equivalence, so it cannot circularly prove one. Keep the helper below both source packages, importing only `FreeCarrierRatio` and required foundational utilities.

**Payoff/risk.** One proof of tuple bijection instead of two, and fewer opportunities for a slot shift to diverge. Migration adds a small generic interface and compatibility wrappers; the 60-line duplicate is an observed opportunity, not a promise to delete 60 net lines. Compile the helper and all four compatibility checks before replacing existing proof bodies.

## A2. Parameterize the Split/Gap numerical degree profiles (priority 2; medium risk)

**Evidence.** `SplitWordBounds.negative_layers_lt` and `source_pos` (`76–123`) have a 48-line counterpart in `GapWordBounds66.lean:31–78`. `source_upper_scaled` repeats the same weighted degree calculation at `SplitWordBounds.lean:149–200` and `GapWordBounds66.lean:81–132`.

- [Split positivity](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/SplitWordBounds.lean#L76-L123)
- [Gap positivity](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/GapWordBounds66.lean#L22-L78)

**Existing simplification.** Gap already aliases `sourceValue`, `powerSum`, `lowMask`, `packedS`, and `packedT`, and imports generic geometric lemmas (`GapWordBounds66.lean:11–20`). The remaining numeric proof skeleton is the new target.

**Proposal.** Introduce an explicit degree profile `(d0,d1,d2)` plus the genuinely used inequalities

\[
 d_1 < d_2+116,\qquad d_0 < d_2+232.
\]

Retain `D2.coeff d2 = 1`, each degree bound, each coefficient-height bound, `B = 4096*H*b^2`, and `B^116 ≤ U`. Prove lower-layer domination and positivity once. Specializations use `(1719,2027,1929)` and `(1627,1941,1850)`; closed arithmetic side conditions can be discharged separately.

Before: a second `negative_layers_lt` unfolds the same argument at 1850/1941/1627. After (schematic, not exact API):

```lean
exact degreeProfile_negative_layers hk.profile hH hb hscale hU
  (by decide : 1941 < 1850 + 116)
  (by decide : 1627 < 1850 + 232)
```

Extend to the common upper bound only after the lower-bound abstraction is useful. A generic target exponent `d2 + 233` preserves the existing 2162 and 2083 exponents, with the corresponding comparisons for the lower layers. Avoid making a huge record containing final conclusions; store degree data and elementary numerical inequalities, then derive source positivity and packing.

**Critical non-shortcut.** Gap's `KernelBounds` is **not** merely a stronger Split `KernelBounds`: the required leading coefficient is at 1850 rather than 1929 (`SplitWordBounds.lean:20–27`, `GapWordBounds66.lean:22–29`). Coercing one into the other would be invalid. Neither should the final sharp packing bound be replaced by a weaker larger exponent to make abstraction easier.

**Payoff/risk.** Removes maintenance duplication in a mathematically meaningful family, while preserving independent concrete certificates. Risks are a too-general API, slower elaboration of symbolic exponent arithmetic, and losing the sharp numeric constants. Measure both specializations, not only the generic theorem.

## A3. Share the current-carrier source/window extraction (priority 2; low-to-medium risk)

**Evidence.** `CurrentSparseDigits2011.polynomial_zero_reconstructs:118–130` and `CurrentHighDigits2011.polynomial_zero_mask_test:141–153` repeat the same pipeline: convert polynomial zero to `Carrier65.value`, restore a canonical parent, call `Carrier66Source.canonical_window`, rewrite `core_restore`, normalize `(2^width)^N` to `radix^(N*2011)`, and recover the repunit equality. The more complete `CurrentPolynomialWindow2011.polynomial_zero_window:81–105` reconstructs the same parent/source bridge again because it needs the actual source assignment.

- [Low extraction](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentSparseDigits2011.lean#L111-L138)
- [High extraction](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentHighDigits2011.lean#L135-L159)
- [Full window](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPolynomialWindow2011.lean#L78-L119)

**Existing simplification.** `Carrier66Source.canonical_window:376–394` is already the generic scalar window theorem, and `positive_carrier_zero_source:398–416` already proves a source lift. `CurrentPolynomialWindow2011.Facts:27–68` already uses named fields and one coherent source/window. Do not replace these with a parallel proof framework.

**Proposal.** Add a direct `Carrier65` positive-zero-to-source certificate with the existing natural source, positivity, rows, preserved outer coordinates, and the proved `sourceQ_eq`, `gap_eq`, `nativeRank_eq` equalities. Its proof composes the existing restoration results. Add one current-mask specialization that normalizes radix/width and exposes both mask tests together. Low/high/full-window consumers project the needed fields rather than repeating the restoration sequence. Keep the same `N` and source assignment across all fields.

Before: each caller performs the thirteen-line restoration/normalization preamble. After (schematic):

```lean
obtain ⟨N, hN, facts⟩ := current_zero_window_facts K hK v hv hz
-- Low decoder uses facts.C_pos, facts.C_split, facts.low_mask.
-- High decoder uses facts.high_mask; both share facts.q_window and facts.J_window.
```

**Preservation obligations.** This helper must be proved from positivity and the actual polynomial zero; never add a source-zero, canonical-parent, no-carry, or already-decoded-window hypothesis to the public theorem. Preserve high port's single beta shift and both origin corrections (`+1` low and `−1` high). Separate source lift, scalar window, and later carry/digit facts so the helper does not import its consumers.

## A4. Move the current base interface below thirteen-coordinate completeness (priority 3; low risk but build benefit unmeasured)

`CurrentCarrierArithmetic2011.lean:1–2` imports `CurrentMasks2011` and `ThirteenCarrierComplete`, even though its low/high digit clients only need the four-port bounds, `polynomial65`, and the carrier-to-source arithmetic bridge. The thirteen-coordinate definitions/equivalences appear at `45–52` and `60–132`.

**Proposal.** Extract a lower module, e.g. `CurrentCarrierBase2011`, importing `CurrentMasks2011` and `Carrier66Source`; place `beta_ge_thirty_one`, `portBounds`, `polynomial65`, and A3's scalar interface there. Keep `CurrentCarrierArithmetic2011` as the compatibility facade importing the base plus thirteen-coordinate completeness. Point low/high digit modules at the lower module. No change to statements or formulas is necessary.

**Static evidence.** Local import-graph reachability from the current arithmetic facade covers 37 modules in this Lean project. The proposed base's two existing imports cover 31; adding the new base itself gives 32. The five avoidable existing modules are `SignedPellResidue`, `ThirteenCarrier`, `ThirteenCarrierComplete`, `ThirteenCarrierSoundness`, and `ThirteenFreshSeed`. This is **not** a measured build-time reduction; external import transitive closures were not traversed. See `import_analysis.json`.

**Risk.** A facade preserving names and imports is essential for existing consumers. Explicitly avoid importing `CurrentSparseDigits2011`, `CurrentHighDigits2011`, or `CurrentPolynomialWindow2011` back into the base: those depend on it. This refactor should follow A3's interface design, not precede it blindly.

## A5. Give conjunction certificates stable named accessors (priority 1 small cleanup; low risk)

`Carrier66.Canonical:153–156` is a seven-part conjunction, and `Carrier66Source.canonical_strong_error:180` accesses `hc.2.2.2.2.2.1`; `source_pos:227` accesses the index factor via another positional chain. This is fragile if a fact is inserted or reordered.

- [Canonical definition](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier66.lean#L153-L163)
- [Positional use](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/Carrier66Source.lean#L167-L191)

**Proposal.** First add projection lemmas such as `Canonical.Z_eq_delta`, `Canonical.index_eq_one`, and `Canonical.rank_pos`, retaining the exact definition. Before: `rw [hc.2.2.2.2.2.1, sub_self] at hid`. After: `rw [hc.Z_eq_delta, sub_self] at hid`. Named structures in `Prop` are an optional later migration, with `Canonical ↔ CanonicalFacts` compatibility; do not immediately break all `obtain`/`rintro` patterns for cosmetic gains.

Extend only where useful: a derived `PortBounds.beta_pos` avoids repeating `have := hp.beta_min; omega`; a compact derived core-positivity API can reuse `Carrier65.scales_pos:175–183` in `Carrier66Source.source_pos:198–218`. Do not replace actual derivations by new positivity assumptions. Existing `CurrentPolynomialWindow2011.Facts` is the local design precedent.

## A6. Generate coefficient naturality from a single arithmetic representation (priority 4; medium-to-high migration risk)

**Evidence.** `NativeNinePolynomial52.lean:93–404` is a 312-line region of option directives, 22 `mapRowCoefficient*` lemmas, and dispatch. Each helper repeats both the original and mapped coefficient expression (`hleft`/`hright`), then uses the same ring-homomorphism simplification. The authoritative table itself is `NativeQuadraticParent.rowCoefficient:155–177`. Gap has analogous coefficient-map cases in `GapNinePolynomial66.lean:99–283`.

- [Native map proof region](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeNinePolynomial52.lean#L93-L404)
- [Authoritative coefficient table](https://github.com/VladimirReshetnikov/ProveIt/blob/60e9c5d620c6c387d932876cfa2d9376f64ea56c/Computability/DiophantineConsistency/Lean/DiophantineConsistency/NativeQuadraticParent.lean#L155-L177)

**Checked scope.** In that `rowCoefficient` table, coefficient expressions use fixed port indices, integer numerals, negation, ring subtraction/addition/multiplication, and a fixed natural exponent 2. Branches compare a `PairIndex` to fixed indices, independently of ring values. There is no natural truncated subtraction on coefficient data, division, `toNat`, or ring-dependent branch/index. Thus these expressions admit a generic ring-homomorphism interpretation. The natural exponent subtraction in `kernelValue:64` belongs to fixed layout metadata, not ring coefficient arithmetic; it must remain fixed under the transport theorem. Do not extrapolate this claim to arbitrary natural evaluators elsewhere.

**First try the cheaper option.** Replace repeated `hleft`/`hright` spellings with a focused local simp set / generated case tactic while retaining the table. Grouped `map_*` simplification may deliver most of the benefit without changing definitions. Measure time/heartbeats because current local options suggest reduction cost matters.

**Larger proposal.** Store small coefficient expressions once as computable ring syntax, or reuse the existing arithmetic-DAG evaluator where that does not overcomplicate a tiny coefficient. Prove naturality of the evaluator once; the table's transport lemma is then an instance. Keep a proved equality to the old authoritative table and compatibility aliases. A schematic pattern is `rowCoefficient ports k p := eval ports (coefficientExpr k p)` followed by `eval_map`.

**Existing simplification.** Ring-polymorphic literal evaluation and `value_map`/`eval_polynomial` are already pervasive: `Carrier65.lean:155–167`, `Carrier66.lean:137–150`, `NativeNinePolynomial52.lean:406–454`. `ArithmeticDAG.lean:48–103` already proves evaluator naturality and polynomial evaluation. The new recommendation is to eliminate duplicated coefficient proof data using those ideas, not invent a second generic DAG framework.

**Risks.** Replacing the ordinary integer evaluator by noncomputable `MvPolynomial` evaluation would violate an intentional design boundary (`NativeNinePolynomial52.lean:9–13`). A computational AST avoids that but adds syntax, generators, rewrite lemmas, and an equivalence proof. Any sparse table refactor must preserve repeated-term accumulation, row order, supports and corrections. It must still prove equality to `GapSource66.rows` / the existing literal source, not define source and certificate from a replacement table so their agreement becomes vacuous. Keep the present public map theorem's general `CommRing` statement.

## Suggested implementation and validation sequence

1. Compile A1's standalone helper and all four original-statement compatibility checks; replace only proof bodies. Add A5's named accessors without changing definitions.
2. Introduce A3's source/scalar-window interfaces, refactor the two simple digit clients, then the full window theorem. Confirm the same actual polynomial and source assignment appear in endpoints.
3. Perform A4's import split, retaining the old facade; compare the dependency graph and build all affected downstream modules.
4. Parameterize A2's lower-bound proofs, keep concrete wrappers, then consider upper packing estimates. Preserve every numeric ceiling and leading coefficient.
5. Attempt A6's local simplification first. Undertake AST migration only if measured generated-proof and maintenance savings justify it.

For every step: compare old/new declarations and hypotheses, build the original public endpoints, inspect `#print axioms` for those endpoints, record Lean/toolchain and dependency revisions, and measure elapsed time/heartbeat use on the same environment. No candidate in this architecture review has been compiled, benchmarked, or integrated. Do not claim verified line savings or speedups from these source observations.
