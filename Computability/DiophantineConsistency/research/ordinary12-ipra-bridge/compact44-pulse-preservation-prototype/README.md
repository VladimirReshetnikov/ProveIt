# Packing preservation from a single dummy pulse

The canonical perturbed cell word is `X1 j = X0 j + 2^(67*1063) * δ j`.
The checked `CompactPulsePreservationRetry.packing_of_pulse` reconstructs the
full 13-field `PackingInput` for `X1` from the base packing and these explicit
additional conditions:

* `δ j ≤ 1` for every `j`, and `δ j ≠ 0` implies `0 < j`;
* **single-pulse low-mask safety**: for every `0 < j < N`,
  `NoCarry (X0 j + 2^(67*1063)) MC`;
* five conditions for the actual perturbed word: its per-cell kernel-product
  bound, cell-plus-block bound, positive origin block, and origin and non-origin
  high-mask no-carry facts.

The proof uses the positive support to show `δ 0 = 0`, so the base `origin`
and `low_origin` fields apply unchanged. The five scalar fields come from the
base packing. For each non-origin cell, Booleanity yields either the base
low-mask fact or the explicit single-pulse fact. The latter is a sufficient
condition at every non-origin cell, including cells outside the controller's
support; it has not been proved for the compact cell and mask. The five
product/block conditions are also not proved here. In particular, the
existing sparse target-block no-carry theorem does not establish them.

The pointwise theorem compiled successfully using the same incremental
symbolic-controller provider as the canonical perturbation client; the first
attempt's ambiguous `lt_irrefl` error and the checked retry are retained. The
result is a theorem about models of IΣ₁ and functions, not an internal iPRA
proof. It does not establish the base packing, pulse safety, block facts,
physical dummy safety, retained-byte binding, or a graph zero. The direct
input object hashes, command, dependency list, log and terminal status are in
`observations/`; package/transitive/dynamic ancestry and between-check
limitations are inherited.

A separate chosen-rank client retains the single-pulse premise and quantifies
the five product/block conditions uniformly over every admissible selector.
Its first attempt failed because it lacked the `CompactRankVariation`
namespace. The corrected `CompactPulseChosenRankRetry.lean` compiled without
warnings or `sorryAx` in tool session `87886`; its theorem produces the
chosen calibrated packing under those same explicit pulse and uniform
product/block premises. The source, failed attempt, successful log and
terminal observations are retained. This is an incremental author-side build
with the same inherited provider limitations.
