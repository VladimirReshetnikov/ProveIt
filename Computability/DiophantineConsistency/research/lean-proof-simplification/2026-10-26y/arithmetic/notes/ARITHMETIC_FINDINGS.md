# Arithmetic findings after prior-proposal exclusion

## 1. Prune all nonextremal rows before consulting any support table

Target: `NativeQuadraticPositions.index_span`, pinned source lines 23--114; public wrapper `encoding_span`, lines116--119. Snapshot553a5f7a463cbaab8800ff8148fef0bc5a9e1b22. Definitions and every public signature are unchanged by the proposed patch.

Write E(k,i)=349(k+1)-W(i), with truncated natural subtraction. For every k<21, E(k,i)<=349*21=7329<7516 regardless of W(i). Thus these21 rows require no support-membership theorem, finite enumeration, lookup certificate, isolated-pair fact, or knowledge of weights. Only the final rowk=21 reaches target7678. Its exact supported indices are59,18,64,21,0; their W values are271,204,267,200,162; E values7407,7474,7411,7478,7516.

The five remaining checks establish the same sharp ceiling7516. The later `kernel_top_coefficient=2` and `kernel_natDegree=7516` theorems are unchanged. The final-row support guard is essential: index7 would give7597>7516, but index7 is not in that row's support.

### Increment beyond the excluded work

Packet f's inventory (INVENTORY.md:53) already suggests a support-membership/indexed-support interface for this exact module. Assume that interface exists. It would compress the syntax of all136 obligations; the new mathematical argument discards131 of those obligations altogether. It consequently remains useful after prior finite checking and membership normalization are applied. Source-line savings are only measured against the raw pinned source, not the hypothetical fully-refactored tree: the private theorem declaration decreases92 to11 physical lines, and the full file258 to177, a net81-line candidate reduction.

### Reviewable implementation

`extremal-span.patch` changes only this private proof. `DiophantineConsistency/NativeQuadraticPositions.lean` is the full proposed module. `IndexSpanFixture.lean` imports mathlib only and copies five source definition chunks verbatim: PairIndex; pairWeight; weights+activePair; rowSupportIndices+rowSupport; target. It proves the exact private statement and public encoding_span wrapper. `fixture-extractions.json` records every copied byte span and SHA256; this is stronger than a hand-transcribed toy table, but narrower than a full production-module rebuild.

The final exact-data fixture passed Lean with exit0. The public encoding_span theorem reports only propext, Classical.choice, and Quot.sound. Validation results are in `fixture-check.json`. Do not infer a successful full-module rebuild from a fixture check. A clean rebuild of the20-project-module dependency closure was started; its first SidonPositions module succeeded, then the optional expensive rebuild was stopped under machine contention. `dependencies.json` verifies all20 source files against the pinned git blob SHA. The mathlib manifest pin is81a5d257c8e410db227a6665ed08f64fea08e997; Lean4.32.0 compiler commit8c9756b28d64dab099da31a4c09229a9e6a2ef35.

## 2. A small Sidon arithmetic-domain normalization candidate

Target: `SidonPositions.weight_sum_eq_iff`, lines67--92. Once equal position sums have supplied equal first and second moments, transport the full arithmetic goal to integers at one boundary, using `simp only [Fin.ext_iff]` and `zify at hsum hsquares` plus the goal. Use the deterministic identity

  2(a-c)(a-d)=(a^2+b^2-c^2-d^2)+(a-b-c-d)(a+b-c-d)

rather than deriving a natural product equality, casting it separately, constructing two Fin.ext witnesses and casting their projections back. After both moment differences vanish, the domain property gives a=c or a=d, and omega supplies the other coordinate. The `SidonMomentCheck.lean` demonstration uses the actual sums_of_weight_sum_eq theorem from the freshly compiled pinned SidonPositions module.

This is a modest local cleanup. It is not a new general Nat/Int transport strategy: earlier reports already discuss arithmetic-domain boundaries. The specific Sidon/Vieta polarization step was not found in the audited prior corpus. The exact replacement theorem passed (sidon-check.json), and the entire modified SidonPositions module passed separately (sidon-full-check.json). The exact theorem decreases26 to17 lines; two added tactic imports make the whole module168 to161 lines. These are raw-source local measurements, not an incremental mathematical gain over every prior general cast-normalization suggestion.

## Excluded or rejected directions

The audit located prior proposals for signed-congruence orbits, `odd_index_of_base_dvd` reuse, integer half-binomial quotient recovery, natural perturbation estimates, positive-pair Pell recurrences, rational-root-preserving integral descent, integer equal-power divisibility in MinimumNorm, negative-Pell obstruction reuse, minimum-sum saturation, and small-ordinate Pell minimality. None is counted here as a new idea.

Finite polynomial interpolation at port values was not found in the exclusion corpus, but is not recommended without evidence: a multivariate evaluation grid can cost much more than existing sparse symbolic normalization. It would need an exact degree certificate and binding to the independent source polynomial; merely testing values cannot certify equality.
