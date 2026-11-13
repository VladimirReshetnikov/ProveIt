# Compact44 `PackingInput` obligations and current evidence

This is a source-level map, not a construction or a Lean proof of a compact
`PackingInput`. Fix `B = 2^590069`, symbolic `K = paramKernel rho`, native
low and high masks `MC = lowNat`, `HP = highNat`, `N = w*H`, and
`w = 581197^(T+1)`, `H = 581197^(T+3)`. In the graph's symbolic port tuple
the high port is `beta+highNat`; the local `PackingInput.HP` below is the
native `highNat` used by its repeated-mask convention. The Lean identity
connecting every notation must be checked on the eventual common provider.

The earlier [chosen controller](../compact44-chosen-controller-calibration-prototype/README.md)
constructs an abstract selector. The conditional
[realization client](../compact44-controller-realizable-bridge-prototype/README.md)
still assumes a valid base packing and a valid modified packing for every
admissible selector. The following are the actual fields of
[`PackingInput`](../../../Lean/DiophantineConsistency/ArithmeticPacking.lean),
and the status of their compact instances:

| Field | Needed compact fact and current evidence |
| --- | --- |
| `N_gt` | Prove `1 < N` for the selected powers. The [geometry client](../compact44-packing-static-fields-prototype/README.md) checks it on the documented exploratory mixed overlay. |
| `s_lt` | Prove `w < N`. The same checked geometry client derives it from the chosen controller's width bound and one extra power. |
| `hi_lt` | For each cell word `X j`, prove `K*X j < B*B`. The natural symbolic K digit theorem gives an upper bound, but a model cell-word bound and the exact cast/product comparison are still needed. |
| `MC_lt` | Prove `lowNat+1<B`. The [separated static-field client](../compact44-packing-static-fields-prototype/README.md) checks the exact symbolic bound on the documented mixed overlay. |
| `HP_pos` | Prove `1≤highNat`. The same client checks the exact native-mask positivity. |
| `HP_lt` | Prove `highNat<B`. The same client checks the bound from the symbolic beta/mask inequality. |
| `cell_sum` | For all `j<N`, prove `X j + blk j < B` for the actual `K`, cell and cyclic neighbors. This needs a constructed compact cell, local product bounds and no-carry/normalization of **all** contributing columns; the selected aggregate alone is insufficient. |
| `origin` | Prove `1≤X 0`. The compact word has the designated origin row, but its actual packed cell and the selector digit at zero must still be constructed and identified. |
| `blk_pos` | Prove `0<blk 0` for the actual normalized block. The sparse target has occupied digits, but equality of the full normalized product/neighbor block to that target has not been proved. |
| `low_origin` | Prove `NoCarry (X 0-1) (MC+1)`. This special origin condition needs the exact origin cell and increment/subtraction behavior; ordinary low-mask disjointness does not by itself supply it. |
| `low` | For all non-origin `j<N`, prove `NoCarry (X j) MC`. This requires a constructed physical cell, including the two dummy positions, and support/disjointness for the selected dummy bits. |
| `high_origin` | Prove `NoCarry (blk 0) (HP-1)`. The special high-mask decrement must be handled explicitly; no-carry against `HP` alone does not imply it. |
| `high` | For all non-origin `j<N`, prove `NoCarry (blk j) HP`. The checked sparse target block has no carry against `highNat`, but it has not been identified with the full `blk j` including foreign band, bare terms, temporal term and incoming carry. |

For context, the [word-cell client](../compact44-word-cell-author-rebuild/README.md)
constructs definable selector and payload functions and proves the selected
finite coefficient aggregate is `1+2^51`. The
[target no-carry result](../compact44-word-target-nocarry-prototype/README.md)
proves no-carry for a deliberately sparse target block, not for `blk`. The
[product-column result](../compact44-word-product-column-prototype/README.md)
relates the selected aggregate to two cyclic product digits only under its
explicit packed-digit and carry hypotheses, and retains all other column
contributions. These results therefore do not discharge `cell_sum`,
`blk_pos`, `high_origin`, or `high` on their own.

The two low dummy slots at phases 1063 and 1064 must be treated separately
from ordinary selector/copy slots, and the selected `δ` must leave every
local mask, neighbor match and carry bound valid. The nonwrapping controller
support only rules out the two global wrap regions; it is not the missing
per-cell bit safety or the proof that the perturbed word satisfies
`PackingInput`. The rank-variation theorem then applies to the same base
and perturbed packing, after these obligations have actually been supplied.
