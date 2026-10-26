# Independent review: outer-seed `hKr` reuse

## Result

**Retain as a small, uncompiled, optional local cleanup after the closing-manuscript screen.** The one-line replacement has a direct source-level proof fit and preserves every byte outside the specified local proof. No overlap was identified with the exact nearest prior Pell mechanisms after accounting for their broad advertised follow-ons and the four closing manuscripts. This is **not a new mathematical theorem, general Pell mechanism, or independently compiled result**. It should not be promoted into a major fresh research direction.

Review scope: frozen repository source `7ba7d102822df1eff376cbca913727d9d588ab4e`; `research/outer_seed/candidate.patch`, its complete candidate module and metrics; the imported helper and a complete source path to it; exact closest prior reports; inherited semantic exclusion ledger and current new-manuscript exclusions. The broader corpus rebinding remains the baseline worker's evidence rather than a claim that this independent reviewer personally reread every historical artifact.

## Exact change and preservation

Target: `NativeOuterSeedConstruction.exists_outer_seed`, local `hKr`, original lines 208–218.

```lean
  have hKr : r+1 < K := lt_yn_of_two_le hP (by omega)
```

- Source SHA-256: `fd437b7d7d64c3371f4d0f2bc234d9e620526b0b1b3c4558ab6fbb47d6573159`.
- Source Git blob: `c02b1abb2c0b9c9c75b63ddd618c5ff678f0911b`.
- Candidate SHA-256: `201491d6c852eb0d5debf5ed3f852e4a640efe3dae636acd7c77ced3d7edaec5`.
- Local fragment: **11 → 1 physical lines**; complete module: **279 → 269**. Net deletion: 10 lines. No new helper is introduced.
- Exact replacement replay and independently reconstructed unified diff agree with the supplied patch. All imports, definitions, public declarations, other proof regions and comments remain byte-identical.
- `hRX` is deliberately retained, even though the removed proof no longer needs it. Neither its potential deletion nor the neighboring `hcX` argument contributes savings to this patch.
- This is textual accounting, not a claim about proof-term size, build time, or transitive dependencies.

## Proof fit, domains and guards

The existing repository theorem is in `dependencies/Computability/HilbertTenthProblem/Lean/Diophantine/Common/PellMod.lean:313–325`, under `namespace Diophantine` and the variable declaration `{a : ℕ} (a1 : 1 < a)`:

```lean
theorem lt_yn_of_two_le {n : ℕ} (hn : 2 ≤ n) : n < yn a1 n := by
```

The consumer already has `open Diophantine Pell Jones1982 Jones1980` (line 14), so the unqualified name resolves through its existing open namespace. The intended instantiation is exactly `a := P`, `a1 := hP`, and `n := r + 1`.

| Required fact | Existing source evidence |
| --- | --- |
| Natural base and index | `u R r : ℕ`; natural `P` and `K` local definitions |
| `1 < P` | `hP` at line 168, proved from positive `Q` |
| `2 ≤ r + 1` | `hr : 4 ≤ r`, the second component obtained at line 155 from `population_sizes`; its statement is at lines 21–23 |
| Target ordinate | `let K := yn hP (r+1)` at line 169 |

Thus the new conclusion is definitionally the existing goal `r+1 < K`; the only tactic obligation is elementary natural linear arithmetic. No signed-to-natural cast, natural absolute value, index truncation, exponent manipulation, positivity of a denominator, new classical choice, witness construction or extra hypothesis is introduced.

The helper's `n ≥ 2` condition is substantive: `yn a1 0 = 0` and `yn a1 1 = 1`, so strictness fails at both smaller indices. The retained local `hr` is stronger than needed. The base guard `1 < P` is also retained; there is no claim for arbitrary integer bases or for the degenerate base one.

The helper already proves its generic bound with `pow_le_ψ_succ`, a comparison with `3^(n-1)` and induction. Reusing it removes a duplicated client argument; it does not remove exponential reasoning from the theorem's transitive proof dependencies. The declaration is source evidence, not a newly validated compiled object.

## Import and circularity review

The already-present path is:

`NativeOuterSeedConstruction` → `NativeHalfBinomial` → `NativePellScaleBounds` → `NativeBinaryScale` → `NativePellPower` → `NativePellFirstIndex` → `NativePellBootstrap` → `NativePellStepDown` → `SignedPellResidue` → `Diophantine.Common.PellInt` → `Diophantine.Common.PellMod`.

The replay verifies every source edge and its frozen manifest SHA-256/Git blob. `PellMod` imports lower `Diophantine.Common.Pell` plus Mathlib modules; `Common.Pell` imports Mathlib's Pell sequence implementation. The reused theorem has no reference to the consumer or `DiophantineConsistency`. The patch introduces no import edge and no recursive theorem dependency. A complete Mathlib checkout, full transitive closure and axiom audit are not available and are not claimed.

## Strict assumed-applied baseline

The baseline includes all historical proposals and explicit follow-ons, not just their literal patched targets. A new filename, client, adapter or shorter tactic is not itself novelty. Exact nearest texts are bound by `baseline_audit/NEAREST_PRIOR_BINDINGS.json`.

1. **`l`, lines 378–458 and 600–616; `r`, lines 169–255 / inherited V19.** These compare two Pell bases through simultaneous positive recurrence, then compare indices from a genuine coordinate gap. The broad follow-on places that base-monotonicity layer lower and weakens source base-separation callers. That complete outcome is assumed available. It does not identify an index itself with a second Pell coordinate or supply the assertion `n < yn a1 n`; taking equal bases merely gives identity or an index-to-index comparison. The V19 ledger phrase “independent exponential comparisons” must be read with that actual contract, not expanded into a universal API for all growth inequalities.
2. **`z`, lines 143–184 / inherited S01.** The old mechanism fixes an ordinate anchor and transports it by index monotonicity: `A(A²−1)² < A⁵ ≤ x_A(5) ≤ y_A(6) ≤ y_A(p)`. It expressly describes a small fixed-index deletion, not a general threshold library. A neighboring `hcX` rewrite via index two is a new client of that old mechanism and is excluded. In contrast, `hKr` has the variable index itself on the left and directly reuses the existing exact universal theorem; it is not an index-two or index-six fixed-threshold argument.
3. **`zc` / inherited C02 and broad normalized-growth direction.** The exact report at `baseline_audit/inherited/round6/nearest_sources/normalized_growth.tex:305–404,570–583` includes common-base substitution and threshold shifts leaving a scalar growth inequality. Those advertised generalizations remain excluded. This patch performs no common-base normalization or threshold shift and adds no scalar induction or infrastructure.
4. **New incoming families M01–M06.** The current `NEW_MANUSCRIPT_REVIEW.md` grants the full rotation-period, strict-slack capacity, internal quotient cancellation/order, row-dependency zero-test, fixed-affine endpoint and source-row guard-recovery mechanisms, including optional APIs and future named clients. None supplies this exact source-free single-sequence index/value bound. Conditional source-guard recovery is not being presented again as a positive-source construction.

**Novelty boundary:** no new Pell result is claimed; the retained residual is exactly the previously unproposed local use of an already available precise theorem. The broader baseline audit supplies exclusion coverage across all six previous delivered rounds. If the deliverable requires several substantive new mechanisms rather than a small local cleanup, this candidate alone does not meet that ambition.

## Closing-screen concurrence

The single closing cutoff is `3b51c69d42ff99bc420698532af3fe1d1f9bd356`, dated `2026-10-26T19:32:32Z`; the proof source remains frozen at the original pin. `provenance/CLOSING_target_binding.json` records the same target Git blob `c02b1abb2c0b9c9c75b63ddd618c5ff678f0911b` at both pins. No later-head freshness claim is made.

I read the complete closing adjudications in `baseline_audit/CLOSING_A_REVIEW.md`, `baseline_audit/review_notes/CLOSING_B_REVIEW.md` and `baseline_audit/CLOSING_C_REVIEW.md`, inspected their distinct coverage boundaries, and additionally read the most relevant full-exponent-growth report section and its further question directly. This corroborates, but does not misrepresent as my own complete-file rereading, the specialist full substantive review of all four incoming manuscripts.

- **A / Positions–Rank–Rephase and Shape–Windows–Growth:** grant fixed-affine position arithmetic, every full-exponent growth client, exact rephase field transport, bitwise disjoint-add reuse, raw split-shape/scalar metadata, all monotone half-open-window adapters and the notes-only directions. The growth follow-on explicitly concerns a final `b^(k*u)` and a desired linear bound in `u`, normalizing the full exponent before the library growth theorem. That is not the exact single-sequence `n < yn(a,n)` reuse here. No shape, window or transport mechanism supplies it.
- **B / Rank–Zero-Test:** grant sharp native-rank upper deficit and all window clients, cancellation-based zero-test selection without idempotence, actual controller base-unit parity proof and all advertised follow-ons. These conditional source-rank, semiring and coprime/unit facts do not provide this source-free Pell sequence lower bound.
- **C / Proof Simplification Review:** grant actual scalar-realizer certification reuse and dependency split, equal-boundary dummy conservation including fresh-zero compatibility, joint discrete shifted-numerator envelope, and classical constant-predicate computability/r.e. plus proof-irrelevance variants. Their complete contracts and real-client adapters do not contain this Pell index/value cleanup.

**Closing result:** the optional ten-line cleanup survives this union; no substantive new mechanism is claimed. The separate possible `SelectiveCoefficientBounds.abs_coeff_combined_le` reuse is **excluded**, not an optional recommendation: exact `baseline_audit/nearest_sources/injective_placement.tex:427–434` already advertises injective sparse lookup-at-image and coefficient bounds. Changing its local representation or citing a same-file helper does not evade that broad prior scope. The logical endpoint and neighboring `hcX` alternatives likewise remain excluded.

## Reproducible checks and limitations

Run from any working directory:

```sh
python /path/to/lean_simplification_round7_20261026/independent_review/check_lemma_reuse.py
python -O /path/to/lean_simplification_round7_20261026/independent_review/check_lemma_reuse.py
python /path/to/lean_simplification_round7_20261026/independent_review/selftest_lemma_reuse.py
python -O /path/to/lean_simplification_round7_20261026/independent_review/selftest_lemma_reuse.py
```

Evidence: `lemma_reuse_normal.json`, `lemma_reuse_optimized.json`, `lemma_reuse_guard_replay.json`.

Both modes passed; results agree except for the recorded optimization level. All checks use explicit errors, with an AST check rejecting reliance on Python `assert`. Six negative-control replays deliberately changed source, candidate or helper bytes, once in each mode; all six exited 1 with the expected hash-mismatch error. The original files were not modified by these tests.

The additional finite natural Pell recurrence sanity check covers 253 valid `(a,n)` pairs with `2 ≤ a ≤ 12`, `2 ≤ n ≤ 24`, plus 22 excluded index-zero/index-one boundary cases. It is **not** an exhaustive proof, Lean elaboration, kernel checking, or a full-module build. It is not used as a novelty certificate.

**Never run:** Lean compilation, `#print axioms`, downstream module builds, full transitive dependency validation. `lean`, `lake` and `elan` are absent from `PATH`; installation and desktop execution are outside the assigned authority. No escalation or installation was requested, no permission was denied, and no upstream state was modified. Exact remaining action for an authorized Lean environment: compile the changed production module and its actual downstream checks at the frozen repository/toolchain revision. Current status is **uncompiled**, not failed compilation.
