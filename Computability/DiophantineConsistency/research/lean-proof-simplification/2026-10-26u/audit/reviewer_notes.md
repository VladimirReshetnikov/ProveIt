# Independent review of the new candidate mechanisms

Reviewed against ProveIt commit `4b3dd4efb10f1af27143a6142380322131968726` and the candidate files in `semantic_work`, `arithmetic_work`, and `root_work`. This review is separate from the prior-proposal exclusion audit. It checks mathematical meaning, signature preservation, novelty boundaries, and the scope of supplied compiler evidence. The reviewer did not launch an additional repository build or broad test suite.

**Closing novelty correction:** a refresh at `23f631ea07fff8632eb8cd92286f7621bbe051c0` found four additional incoming archives. One already replaces `firstUnit_fundamental` completely by a uniform small-ordinate Pell criterion. Therefore the sign-free Pell cleanup reviewed below is **withdrawn from the retained recommendations**, despite being mathematically sound and compiled. Its review is retained here only to explain that decision. The five remaining main ideas plus the trace rewrite survive the refreshed comparison.

## Conclusions

No mathematical counterexample was found in the centered integer induction, bounded first-failure lemma, sign-free Pell argument, scale-dependent ratio estimate, sharper rank envelope, or absolute-value trace rewrite. Nine historical theorem-header checks are byte-identical after omitting only the declaration name; see `review_signature_checks.json`. Two concern the now-withdrawn prototype and integrated Pell fundamental-unit study. The **seven retained header checks** are both interval variants (one is optional), both ratio wrappers, both existing rank corollaries, and the trace theorem; their current-file hashes and statuses are in `active_signature_checks.json`. This count is of checks, not seven distinct proposed changes. The comparison alone is not a compilation or proof of integration.

The shared-edge row is a sound checked generic construction, but its equality with the maintained Wang row and its membership in the actual finite tile language are still implementation obligations. The proposal has explicitly addressed a subtle premise issue by using a configuration whose state is overwritten with the supplied operating state.

The optional centered integer eliminator adds `Classical.choice` to the proof's axiom footprint. The delivered complete Wang candidate uses the checked shifted-zero-induction alternative, which preserves the original footprint. This distinction between the chosen edit and its shorter alternative should remain visible in the deliverable.

## Interval propagation

The maintained statement concerns the open interval `l < x < r`, with the known point `x₀` strictly inside it. The centered induction uses the motive `l < x → x < r → P x`. In a successor case, the index is at least `x₀`, so the lower interval membership required for the predecessor follows from `l < x₀`. In a predecessor case, the index is at most `x₀`, so its upper membership follows from `x₀ < r`. These are exactly the side conditions the old two natural-number inductions reconstructed. No closed endpoint, nonempty interval, or extra global closure premise has been introduced.

`IntervalPropagationBefore.lean` and `IntervalPropagation.lean` have checked receipts. Their printed axiom sets are respectively `[propext, Quot.sound]` and `[propext, Classical.choice, Quot.sound]`. `IntervalPropagationNoChoice.lean` also has a successful printed axiom receipt and retains `[propext, Quot.sound]`. It translates by `x₀`, then uses integer induction around zero. This choice-free version is the actual complete-module candidate: `WangTiles942ResetRows` and its original `WangTiles942ResetRowsChecks` client both compile. The client prints `[propext, Quot.sound]` for the actual exported `interval_propagate` theorem.

Measured saving for the delivered choice-free version: the proof body changes from 26 to 14 physical lines; with the explicit import the module changes from 162 to 151, saving 11 lines. The optional centered version has a 9-line body and a 146-line module, saving 16 lines. The absence of a `sorryAx` dependency does not mean that optional centered proof has the same axiom footprint as its baseline.

## Bounded first failure and wall endpoints

`first_failure_between` is valid when `lo = hi`, including `lo = hi = 0`: the least witness is the endpoint and its strict prefix is empty. It does not assume `P lo`. This matters because the required object is the first failure at or after the starting index, not a transition after a known success.

The left call uses `lo = 1`, `hi = N`, and `P j := T (-j) = tileInitLeft`; the right uses `lo = 2`, `hi = N+1`, and `P j := T j = tileInitRight`. The original `0 < N` premise supplies the needed bounds in both cases. The geometric endpoint cases `L = 1` and `R = 2`, their different edge colors, and all subsequent tile classification arguments remain in place. No left-right symmetry of the tile language is assumed.

The generic helper, the complete modified `WangTiles942InitialStrip` module, and its original `WangTiles942InitialStripChecks` client all have successful receipts. The two local administrative blocks change from 20 lines total to 4. Including the new helper, comment, spacing, and import, the whole module saves only 2 lines, so this is chiefly a contract-sharing and readability proposal.

The combined Wang receipt `semantic_work/full-module-validation.json` records ten successful module checks: two modified modules, six unchanged supporting modules, and two unchanged focused Checks clients. Four reused cached dependency sources were compared by hash with the pinned source and match. This supports the stated local integration checks; it is not a clean build of the entire repository.

## Shared-edge row: what is automatic, and what remains to prove

For any north, south, and edge functions, the record

`(west = edge (x-1), north = north x, east = edge x, south = south x)`

has matching horizontal edges because `(x+1)-1 = x`. A bridge located at `min(oldHead,newHead)` gives the correct old-head and new-head edge pairs for a move by exactly one cell. Outside those two positions both adjacent signals are zero. The generic checked file proves these identities for both directions.

This does not prove `Allowed`: an arbitrary north/south choice and signal may not occur in the 942-tile language. The production instantiation must use `rail d target` for the actual direction and target and invoke the existing `action_target_mem` fact in the receiving case. Target 215, which represents entering halt, must remain included. The ordinary three cases still prove row equality or membership once; sharing them is the intended benefit.

There is an important API boundary. Existing `stepTile`, `stepTile_allowed`, and `stepTile_horizontal` do not assume `cfg.state = some q`. Choosing vertical fields directly from `color cfg` and `color (machine.step cfg)` would make equality with the existing row depend on that hypothesis. The semantic proposal correctly uses `liveCfg := { cfg with state := some q }`: its tape and head are unchanged, its supplied action is the same, and north/south interpretation specializes through the original `hq` premise. Keeping the existing executable definition and deriving fields through one equality preserves the original public contract.

The provided `EdgeTile` is intentionally separate from the repository `Tile`. Its field order matches the source (`west,north,east,south`), but the checked generic kernel is not evidence that the repository equality or `Allowed` proof has compiled. No total line saving should be assigned until those clients and the equality have been implemented.

## Ratio estimate with a scale parameter

Writing `ξ = (U+1)^(2r)/U^r` and `ε = 9/(Y(U+1))`, the shared growth proof bounds the ratio by `ξ(1+2rε)`. The existing numeric assumptions give

`(Y+1) * (2rε) < 1/2`.

Thus `ξ < κ(Y+1)` and `κ > 0` imply `ξ * (2rε) < κ/2`. This justifies the additive error `κ/2`, rather than a fixed error or an incorrectly squared scale. `κ=1` yields the existing half-unit estimate; `κ=2` yields the native unit estimate. The argument is valid for arbitrary positive real `κ`, including values below one when the envelope premise is satisfiable.

The original public wrapper keeps its `hYr : U^r ≤ Y` parameter even though the common helper does not use it. Both old public theorem headers are byte-identical. The common theorem belongs before the original wrapper in `PellRatio90` or another suitable lower module; `NativeHalfBinomial` already imports that module. A standalone module importing the old theorem would not itself demonstrate a valid production dependency arrangement. The current candidate takes the suitable lower-module approach.

The standalone generalized theorem and both wrappers have successful compiler/axiom receipts. The complete modified `PellRatio90` and `NativeHalfBinomial` modules also now have exit-zero receipts, and the subsequent endpoint audit prints only `propext`, `Classical.choice`, and `Quot.sound`. The two source modules change from 716 to 646 physical lines. Applying the previously proposed `set` cleanup to both old proofs first gives a 712-line counterfactual baseline, hence 66 newly saved lines rather than 70.

Novelty credit belongs to sharing the scale-dependent inequality and removing its duplicated nonlinear derivation. Replacing trivial existential definitions by `set` was already proposed in the excluded corpus and must not be counted as a new idea or an incremental saving beyond the assumed baseline.

## Withdrawn candidate: Pell fundamental unit without sign branching

For any integer `y`, `y² < 4` implies `y² = 0 ∨ y² = 1`. This certificate allows the minimal-unit proof to operate on `y²` without separately carrying `y=-1,0,1` through the main argument. Negative second coordinates are fully covered.

For a competing Pell solution with `b.x > 1`, the zero-square case forces `b.x²=1` and is impossible. The unit-square case forces `b.x²=Q(Q+1)+1`, which lies strictly between `Q²` and `(Q+1)²` for `Q>0`. Positivity of `b.x` then puts an integer strictly between `Q` and `Q+1`. Therefore `b.y²≥4`, and the Pell equation implies `b.x²≥(2Q+1)²`; positive coordinates give `b.x≥2Q+1`. The `Q>0` hypothesis is preserved and essential to the strict upper comparison.

The actual target is `NativePellBootstrap.firstUnit_fundamental`, not `FirstPellCarrier`. The checked prototype has the exact old theorem type and identical `firstUnit` formula, under a different namespace. The complete modified source module has an exit-zero receipt, and its public theorem signature is also byte-identical. Including the helper, the module changes from 671 to 668 physical lines, a net saving of 3. No new classification or stronger fundamental-unit theorem is claimed.

This saving is no longer eligible as a new recommendation. Archive `additional_lean_simplifications_2026-10-26.zip`, member `additional_lean_simplifications_2026-10-26/report/additional_lean_simplifications.tex`, lines 283–370, already replaces the target by `isFundamental_of_y_le_three`. Under the user's assumption that every prior proposal has been applied, the old discriminant-specific square proof no longer remains to simplify. The earlier proof's different mechanism does not rescue the current proposal's novelty.

## Stronger shared native-rank envelope

The source facts give positive integers `F`, `α`, and `C=q-F-α`. Thus `q≥3` and `q-F≥2`. For `G=(q-1)(q-F)+α`,

`G ≥ 2(q-1)+1 = 2q-1`.

With the nonnegative mask term and the exact source target equality, this yields

`(2q-1)(q²-1) ≤ nativeRank`.

At `q≥3`, the lower product is at least `5*8=40` and exceeds `3q`. The old `24≤nativeRank` theorem remains a valid compatibility wrapper. The existing `3q` theorem retains its natural/integer conversion and identical source signature. The supplied patch introduces no additional port or positivity premise.

The generic arithmetic lower envelope is attained at `q=3,F=α=C=1` and zero mask. This does not establish that the full source polynomial system has a witness with those values; sharpness should be stated only for the abstract arithmetic assumptions. The final candidate changes the combined two-module size from 769 to 765 physical lines, a raw snapshot saving of 4. This final improvement uses `Int.lt_toNat` to simplify the natural/integer boundary. Since prior E38 already proposed sharing rank conversions, the four cast-related lines should not be advertised as an independently novel saving beyond every assumed prior API. The stronger shared bound is the distinct new mathematical proposal.

Both complete rank candidate modules, `NativePellBootstrap` and `NativePellScaleBounds`, have exit-zero receipts in `root_work/rank-checks.json`. The final shorter ScaleBounds version, the rank endpoint/40-bound axiom audit, and the trace endpoint audit also pass in `root_work/final-checks.json`. Their printed axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. These receipts check the rank candidate independently of the separate fundamental-unit patch; any combined integration has its own validation boundary.

The excluded E38 source-facts API already proposed carrying known rank bounds. Merely giving the facts a new record would repeat it. The distinct idea here is the improved factor `2q-1` derived from the positive transport gap and reuse of this one stronger result in two formerly separate nonlinear arguments.

## Trace bound

`le_abs'.mp hx` converts the existing assumption `(t : ℤ) ≤ |x|` into the disjunction accepted by `run_read_outside`. The source theorem header is unchanged. Both complete copied modules have successful receipts. This is a small standard-library rewrite, with a six-line body replaced by one line; it should be described at that scale. The recorded elapsed times are single build observations, not a performance benchmark.

## Final reporting constraints

- Distinguish exact declaration checks, complete candidate module checks, and generic kernels with integration pending.
- Keep the centered-induction axiom difference visible and include the choice-free alternative.
- Count helper definitions and imports when claiming net line savings.
- Treat prior `set` cleanup, general source-facts packaging, and existing finite controller suggestions as already applied.
- Do not infer actual finite-tile membership from horizontal matching alone.
- Do not infer full source-system sharpness from the abstract rank-envelope equality example.

