# Reverse 90-to-80 construction: source-level plan

This is a read-only theorem and definition survey, not a checked reverse
implication. The target is an existential result in each stated IΣ₁ model:
from a positive zero of `FreeJDirectMainGraph.graph p` (the selected 90 Lean
graph), construct a positive zero of `TenPositive80Graph.graph p` at the
**same** four-port tuple, under whatever explicit port assumptions the proof
requires. A pointwise inverse is not required. The already checked 80-to-90
output theorem proves only the other direction.

## Shared data and a necessary distinction

In [DirectMainGraph.lean](../../research/ordinary12-direct-main-probe/DirectMainGraph.lean)
the 90 inputs at indices 0,1,2,5,6 are J,F,α,w,s and the graph defines
`q=1+βJ`, `X=q*w`, `Y=q*(q*q)*s`. The [80 graph](../../research/ten-positive-80-model-binding-prototype/Direct80Graph.lean)
uses the same J,F,α,w,s and defines the same q, X and Y. Thus **q³ divides Y
by definition in this specific 90 graph**. The theorem
[`FreeJRootBinding.first_factor_forces_Y_divisible`](../../research/ordinary12-ipra-bridge/free-j-first-divisibility-prototype/FreeJRootBinding.lean)
is useful for a different earlier 95-gate literal whose Y is an independent
coordinate; it must not be applied directly to these 90 variables without a
proved adapter.

The first Pell bases nevertheless differ. The 90 theorem
[`DirectMainFirstQuotient.first_root`](../../research/ordinary12-direct-main-probe/DirectMainFirstQuotient.lean)
uses `P=X*Y²`; the 80 theorem
[`TenPositive80Pell.first_and_doubled`](../../research/ten-positive-80-pell-prototype/Direct80Pell.lean)
uses `P80=X*(μY)²`, `μ=q²+1`. The 90 root and its k,c,η,ζ cannot simply be
copied into the scaled 80 chart. The checked 80-to-90 proof explicitly
constructs a **fresh unscaled** pair; reverse construction needs a fresh
scaled pair and compatible witnesses.

## Reusable Lean ingredients and missing clients

1. [`DirectMainWindow.graph_early`](../../research/ordinary12-direct-main-probe/DirectMainWindow.lean)
   yields the 90 first and main Pell indices and norms from the actual
   positive zero, under its explicit β>0, low<β, high<2β assumptions. The
   bounded-port [`DirectMainEquivalence.positive_zero_iff`](../../research/ordinary12-direct-main-probe/DirectMainEquivalence.lean)
   transfers existence to the 91 graph; its proof uses
   [`DirectMainGap.graph_gap`](../../research/ordinary12-direct-main-probe/DirectMainGap.lean)
   and a positive inverse changing coordinate 11. An existence theorem alone
   does not automatically preserve each outer coordinate for the new client.
2. The rank formula and radix bound needed for construction must be recovered
   for the same chosen 90 witness. The 80-side
   [`rank_gt_three_radix`](../../research/ten-positive-80-canonical-bounds-prototype/Direct80CanonicalBounds.lean)
   uses β≥31 and positive J,α,w but no 80 zero; it can be applied after an
   explicit coordinate projection and rank identification. Rank phase,
   `X=2^R`, the 90 first-index alignment and suitable binomial/floor facts
   still need a coherent 90-witness client at the intended ports.
3. To reconstruct scaled k,c and positive η,ζ with the **same Y**, a
   promising route is to derive the shared floor remainder from the 90
   unscaled pair and transfer it to the new scaled Pell pair. The existing
   model lemmas [`split_floor` and `transfer_floor`](../../research/ten-positive-pell-sandwich-floor-prototype/PellSandwichFloor.lean),
   [`sandwich_of_interval`](../../Lean/DiophantineConsistency/ArithmeticHalfBinomialSandwich.lean),
   [`lower_of_gap` and `shifted_coefficient`](../../research/pell-scaled-sandwich-prototype/PellScaledSandwich.lean),
   and [`upper_of_bounds` and `shifted_upper_coefficient`](../../research/pell-scaled-sandwich-upper-prototype/PellScaledUpper.lean)
   are relevant. The latter upper theorem has explicit positivity,
   perturbation and crude-power premises; a reverse client must actually
   establish them. The existing 80-to-90 floor theorem starts from an 80
   zero and cannot itself be used as the reverse implication. After this
   survey, [generic scaled-interval](../../research/ten-positive-scaled-from-unscaled-prototype/README.md)
   and [fresh scaled-witness](../../research/ten-positive-scaled-witness-from-unscaled-prototype/README.md)
   author checks constructed this pair under explicit unscaled interval,
   power and size hypotheses. Those hypotheses are not yet bound to a 90
   zero and the remaining carrier construction is still separate.
4. [`ArithmeticPellPigeonhole.ordinate_dvd`](../../Lean/DiophantineConsistency/ArithmeticPellPigeonhole.lean)
   constructs a **positive internal index** whose Pell ordinate is divisible
   by an arbitrary positive internal modulus. Applied to `c_scaled²*τ_scaled`,
   it supplies the period/divisibility ingredient described in the ordinary
   [doubling proof, §8](../../research/ten-positive-doubled-product-square/PROOF.md).
   [`double_x` and `double_y`](../../Lean/DiophantineConsistency/ArithmeticPellPeriodicity.lean)
   and [`TenPositiveDoubling.doubled_trace`](../../research/ten-positive-ipra-doubling-prototype/TenPositiveDoubling.lean)
   are reusable arithmetic components. Fresh positive 80 i,T,n, the exact
   doubled strong/auxiliary equations, transport and carrier identities,
   positivity of the unshifted T and n, and the final **actual 80 output**
   zero remain to be assembled in Lean. In particular the formal shears
   `n_old=n_new-s` and `T_old=T_new-α` do not by themselves preserve
   positivity. The [unshifted ordinary construction](../../research/ten-positive-unshift-t-square/PROPOSAL.md)
   is a mathematical guide, not an all-model Lean theorem.

## Port and provider boundaries

[`DirectMainHalt.positive_model_iff`](../../research/ordinary12-direct-main-probe/DirectMainHalt.lean)
is fixed to the **original** symbolic compact kernel. It is not a theorem for
the different direct-BFS kernel merely because the masks agree. Similarly,
any route through a machine halt must first prove the intended tuple/color
binding or stay within the exact original-kernel specialization.

The arbitrary-modulus Pell pigeonhole object exists at the inspected
`/tmp/direct90-ipra-join-b66u_qqo/lib/DiophantineConsistency/ArithmeticPellPigeonhole.olean`
path, a symlink into a separate nine-iPRA author provider. Its presence is
not proof that its transitive project objects, package objects or dynamically
loaded dependencies are coherent with the selected 80/90 providers. A fresh
join must independently check exact selected paths and compatible ancestry,
or rebuild a coherent closure, and preserve the recorded source/object
limitations. This survey makes no Lean replay, external byte-equality,
machine-equivalence or internal iPRA claim.
