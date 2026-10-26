# Tail cutoff duality and conditional normalization

## Result

The prepared proof-only patch removes 13 physical lines from `CurrentSelectorTail2011.lean` at pin `89226e3921bce3e8949fadd12d3efb6914c7630c`: 335 to 322. It changes exactly two proof bodies, preserves both declaration headers, adds no declaration or import, and changes no executable data. `git apply --check` succeeds on that snapshot. This is a pinned-source measurement, not a measurement of a hypothetical combined application of all previous packets.

The theorem `tail_position_iff` occupies lines 229–243 in the original source. Its declaration becomes 10 physical lines instead of 15. The private theorem `selectorTail_succ` occupies lines 260–271 and becomes 4 physical lines instead of 12.

## Mathematical reason

For natural numbers, the strict comparison

`p < c ↔ q < w`

immediately gives the weak comparison

`c ≤ p ↔ w ≤ q`

by negating both propositions. The existing `physical_lt_iff_weight` proves exactly the strict comparison needed when comparing a non-Start tile to the fixed cutoff tile 866. Its right side reverses the order because the physical position sorts by decreasing selector weight. The current proof then reconstructs both implications by contradiction. The replacement applies `not_congr` once and simplifies `Nat.not_lt`; `weight_le_cutoff_iff` supplies the last link to the South-coordinate predicate.

The Start tile is still handled separately. Its position is zero, and it does not belong to the suffix starting at 459. There is no changed assumption about injectivity, cutoff uniqueness, the actual table, strict ranking or the exceptional Start slot.

The successor corollary is conditional transport. Rewrite the guard `459 ≤ physicalPosition j.succ` by the just-proved iff, discharge `j.succ ≠ 0` with `Fin.succ_ne_zero`, unfold the existing `lowMass` definition, and distribute multiplication by two through the conditional. The old proof's two cases and local four-line nonzero argument disappear. In the restricted `simp only` set, `ne_eq` is necessary; its absence was caught during the standalone check and repaired before preparing the final patch.

## Exact candidate bodies

For the non-Start branch of `tail_position_iff`, after retaining the two existing lines that define and normalize `hr`:

```lean
    rw [and_iff_right hi, ← weight_le_cutoff_iff]
    simpa only [Nat.not_lt] using not_congr hr
```

For `selectorTail_succ`:

```lean
  simp only [selectorTailTerm, tail_position_iff, ne_eq, Fin.succ_ne_zero,
    not_false_eq_true, true_and, lowMass, mul_ite, mul_zero]
```

`Fin.succ_ne_zero` is in Lean 4.32.0 `Init/Data/Fin/Lemmas.lean` (lines 418–419). The production tree already uses mathlib's `mul_ite` in `NativeClauseBits54.lean` (line 72). No new API or typeclass is introduced.

## Non-repetition comparison

No prior proposal for these two declarations, for negating the strict rank/weight comparison to obtain this suffix classifier, or for this selector-tail conditional normalization was found in the pinned 23 placed packets plus four incoming archives. The following nearest precedents are explicitly assumed:

- Packet m, `report/additional_lean_simplifications.tex`, section “Optional: recognize the physical permutation as a positive tail”, proposes `Fin.cons_injective_iff` for `physicalPosition_injective`, plus composition for `nonStartWeight_injective`. That changes the injectivity proof. The present patch assumes the existing strict comparison and changes only two cutoff clients.
- Incoming `proveit-lean-structural-simplifications-2026-10-26.zip`, P3 “certify signal masses through sufficient color statistics”, changes how the signal-family counts and masses are obtained. The present patch leaves every count, mass, table, and their certification untouched.
- Earlier finite-table and coefficient-envelope proposals are assumed available. This patch does not introduce another finite enumerator, weighted fibre theorem, rank construction, mass certificate or coefficient bound.
- Packet s's main formula-specification normalization and optional closure results do not propose these tail proofs. General recommendations to keep simplification boundaries narrow are existing engineering advice, not claimed as new here.

The new contribution is a small exact application at a previously unaddressed pair of declarations. Negating an iff and distributing a conditional are ordinary Lean reasoning, not mathematical or library innovations.

## Validation boundary

`TailCutoffCore.lean` imports only `Init` and checks the exact order-negation pattern, the full exceptional-Start proof pattern with the actual `Fin 942`, cutoff tile 866 and cutoff position 459, and the successor conditional-normalization pattern. Its tile facts are explicit theorem hypotheses; it does not prove them from the repository's tile table. A tiny elementary `mul_ite_nat` lemma substitutes for mathlib's `mul_ite` because only `Init` is available. All four printed axiom sets are `[propext]`; no `sorryAx` occurs in the final checks.

The complete production candidate has **not** been compiled. In particular, the standalone check does not certify the imported declaration binding, production axiom closure, or downstream `CurrentEarlyPadding2011` consumers. The patch and full candidate are ready for the normal pinned-project check. The standalone core is validation evidence and does not belong in production; its lines must not be charged as a proposed production helper.

## Suggested adoption

Apply the patch in a disposable checkout at the pin, compile `CurrentSelectorTail2011`, its existing checks and its direct consumers, and compare the public axiom reports. If other proposals have reorganized the same source, rebase these two proof-body changes rather than replacing the whole file. The full candidate is a review/replay reference.
