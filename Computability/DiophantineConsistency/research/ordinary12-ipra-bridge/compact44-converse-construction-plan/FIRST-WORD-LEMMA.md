# First proposed model lemma: a compact word from a halted run

This is a source-only staged plan, not a new Lean theorem or a claim that a
build has succeeded. It stops at a definable cyclic word; it does not prove
packing, the graph zero, coefficient binding, or an iPRA derivation.

## Lemma with explicit dimensions

For a type `V` with `[ORingStructure V]` and
`[V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]`, let `T w H : V`. Assume

* `ArithmeticCantor.first (ArithmeticMachineRun215.run T) = 0`;
* `2 * T + 5 ≤ w`, `T + 2 ≤ H`, and `4 ≤ H`.

Define `a := ArithmeticTilingBand.word T w H` and
`b := fun j => CompactTableLookup.rowLookup (a j)`. The proposed conclusion is
`𝚺₁-Function₁ b ∧ CompactMarkedTransport.CompactWord b (w * H) w`.
Thus the period is positive, all entries in the period are below 943 and
different from row 1, position 0 is the marker, and the specified east and
south matches hold at the cyclic neighbors, including wraparound. The model
and its time `T` may be nonstandard. The function/definability conjunction is
an external Lean statement about the model; it is not itself a formula proved
inside iPRA.

The intended proof is direct composition of source interfaces:

1. `ArithmeticTilingWord.marked_word` supplies the old `MarkedWord a (w*H) w`
   from exactly the four assumptions above; `ArithmeticTilingBand.word_definable`
   supplies `𝚺₁-Function₁ a`.
2. `CompactWordDefinability.forward_composition a` supplies definability of
   `b`, and `CompactMarkedTransport.forward_marked_word` supplies its
   `CompactWord` property. Its extra-row exclusion is retained; one may
   weaken it to `CompactCyclicBridge.RawCompactWord` by taking the other five
   fields.

The two compact lemmas have author-only exploratory evidence described in
the [word definability](../compact44-word-definability-prototype/RESULT.md)
and [forward word](../compact44-row-transport-prototype/MARKED-RESULT.md)
records. Their application to the halt construction is proposed here, not a
reported compilation. No `ArithmeticPackingCells.LocalNormalization`
assumption is used at this stage.

## Dimensions compatible with the compact controller

As a subsequent specialization set `p = 581197`,
`w = power p (T + 1)`, `H = power p (T + 3)`, and `m = 2*T + 3`.
Prove in the same model that the three dimension inequalities above hold and
that `w * H = power p (m + 1)`. The proof of
`ArithmeticTilingWord.dimensions` provides a pattern, but is specialized to
`120199` and cannot be invoked unchanged for `p`.

For the controller's explicit size premises, prove separately
`w ≤ power p m` and `2 * (590069 * 581197) < power p m`.
`ArithmeticPow.power_mono_exponent` handles the first from `T+1 ≤ m`, and
the second follows from `3 ≤ m`, the same monotonicity, and the finite
inequality `2 * (590069 * 581197) < 581197^3`, with the model-power
representation checked using `power_succ`. These are proposed proofs, not
existing exported results for these dimensions.

After a coherent provider rebuild, `controller_choice m w θ` could be applied
for any model `θ`; its conclusion includes a Σ₁-definable Boolean map,
explicit support bounds and a block-sum congruence. The stronger
`rank_calibration m w R0 Γ Γi` additionally requires the explicit unit premise
`(Γ * Γi) % (590069 * power p (m + 1)) = 1 % (590069 * power p (m + 1))`.
Neither controller theorem proves that its safe support is safe for the
as-yet-unconstructed compact packing, or supplies the actual Γ or its inverse.

## Provider boundary

The smallest lemma imports the halting/word construction and compact-word
transport only. Rebuild all required source and dependencies together on one
coherent word-side provider and check the named theorem and assumptions;
existing author-only observations do not establish that this combined client
has compiled. Do not mix the exploratory word overlay with the graph overlay:
their `ModelDifferenceRing` objects conflict. Controller observations are a
separate paired artifact with their documented historical-provider limits;
they do not establish compatibility with a newly assembled word client. A
later combined controller client also needs its own coherent source rebuild
and checks. Neither stage needs the unresolved retained K-byte binding.
