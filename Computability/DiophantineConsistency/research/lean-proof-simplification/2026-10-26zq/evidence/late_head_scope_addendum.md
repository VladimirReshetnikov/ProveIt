# Late-head compatibility of the fixed-cardinality subset proposal

Reviewed refresh: `f00ba53b331833c6cb64707bd90e48489e5610f5`.

This addendum updates source scope only. The generic proofs in
`RestrictedSubsetSums.lean` and the root affine adapter were developed
against the earlier pinned baseline. The newly added physical modules were
read through the GitHub connector; no fresh full-project build or
kernel-checked migration of those modules is claimed here. The late-arrival
exclusion audit is maintained separately by the novelty reviewer.

## What the new source already proves

The refreshed repository now has actual controller subset construction,
safe physical position geometry, one-dummy mutation, ordinary nonwrapping
transport, and its rank decrement. Statements that physical safety or
single-update rank transport have not yet been proved must therefore be
qualified to the earlier baseline.

| New module | Relevant declarations and source lines at the refresh |
| --- | --- |
| `CurrentControllerSubsets2011.lean` | `exists_normalized_subset` 36; `exists_shifted_subset_block` 66; `subset_modulus_transport` 80; `exists_shifted_subset` 93 |
| `CurrentControllerPositions2011.lean` | `position` 13; `position_budget` 24; `position_stride_lt` 53; `position_injective` 79; `support` 112; `support_card` 121; `support_safe` 142; `cyclicSupport_card` 163; `cyclicSupport_safe` 169 |
| `CurrentDummySafety2011.lean` | `safe_increment_bound` 84; `normalized_nonwrap_of_safe` 139; `safe_normalized_increment` 154; `exists_safe_normalized_increment` 169; `safe_rank_decrement` 192 |
| `CurrentDummyMutation2011.lean` | `source_increment` 113; `normalized_increment` 126; `exists_normalized_increment` 146; `rank_decrement` 167 |
| `CurrentPackingRank2011.lean` | `rank` 23; `fourBlocks_cast` 51; `rank_gt_twice_window` 88; `fourBlocks_population` 102; `packing_rank_population` 123 |

All are under `Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

## The principal new client is still Boolean-based

`CurrentControllerSubsets2011.exists_normalized_subset` obtains the proved
actual power-coordinate equivalence and calls
`ControllerResidueLift.exists_subset_boolean_sum`. Its output is

```
epsilon <= 1, 0 < a, a < d*auxiliary, |S|=a,
sum (B^((auxiliary-1)*j.val)) + epsilon*B = target.
```

The new unrestricted fixed-cardinality theorem replaces that call with
the root Boolean-free affine coverage endpoint. The resulting actual
orbit statement has `0 < a`, `a <= d*auxiliary`, and the ordinary power sum
equal to the target. The optional term and its nonzero-prime-residue proof
disappear. Actual power-orbit and base-unit proofs remain in use.

The subsequent `B^2` normalization remains valid: apply the new normalized
statement to the target multiplied by the inverse of `B^2`, and distribute
`B^2` through the sum. The separate `epsilon*B^3` term is no longer present.
The opaque modulus transport is still useful, with its strict cardinality
bound widened to a non-strict bound and its Boolean fields removed.

This is an explicit interface change, not a claim that the new theorem has
the exact old signature. The zero-projection target still requires the
endpoint cardinality `a = d*auxiliary` in general.

## The new physical-position proofs apply to arbitrary subsets

The physical position map is

```
position k j = 2 + (auxiliary-1)*j.val.
```

`support_safe` and `cyclicSupport_safe` quantify over an **arbitrary**
`Finset (ZMod (auxiliary^k))`. They do not assume that its indices form an
interval, that its cardinality is coprime, or even an upper bound on its
cardinality. Their geometric premise is `rw < k`.

Consequently the new staircase subset can reuse these theorems directly
by setting the old optional parameter to zero. The existing definition
then reduces to `S.image (position k)`. Existing injectivity and canonical
representative bounds remain valid for every chosen index. In particular,
the widened arithmetic cap `a <= C0` does not violate a hidden strict cap
in the inspected physical geometry.

The worst-case physical population is also unchanged. The existing
`support_card` and `cyclicSupport_card` give `|S| + epsilon`. The old bounds
`a < C0` and `epsilon <= 1` imply `a + epsilon <= C0`; the new bounds
`a <= C0` and `epsilon = 0` give the same cap.

If the compatibility API is retained, these safety facts can simply be
specialized at zero. If the optional-support API is retired, the proof
path can remove its branch through cell three: `optional_next_lt`,
`optional_stride_lt`, `three_not_mem_image`, and the optional cases in
support membership and safety. Their removal should follow a whole-repo
consumer check; this addendum does not claim they have no other clients.

## What still needs checked composition for this proposal

`CurrentDummySafety2011` already constructs a safe one-dummy update from
the physical inequalities and `dummy j = 0`. It proves the ordinary
normalized-word increment and the signed rank decrement. These are useful
existing ingredients, not new obligations to re-prove.

To adopt the Boolean-free subset endpoint, compose those ingredients for
the chosen finite support, preserving the unused-dummy premise at each
step and binding the finite sum of actual increments to the new power
sum. Distinctness is supplied by the finite subset and the existing
position/cell injections. This read-only compatibility review does not
claim that this full finite-update composition has been migrated and
kernel-checked with the new endpoint.

`CurrentPackingRank2011` supplies actual rank binding and population
facts; it does not consume the strict arithmetic subset-cardinality bound
in any inspected declaration. No new rank-population theorem is proposed.

## Source identities

| File | Git blob SHA |
| --- | --- |
| `CurrentControllerSubsets2011.lean` | `d5c37dc55427da3ea971baed4eef5654c1427565` |
| `CurrentControllerPositions2011.lean` | `779f72b283b44a1947f9083b9f887dbc7cb97b41` |
| `CurrentDummySafety2011.lean` | `682d07cfe3cb1cf79db277e491e7a569119a1505` |
| `CurrentDummyMutation2011.lean` | `b42c2b0ae3106b060244e40363bf8a98a3ded94e` |
| `CurrentPackingRank2011.lean` | `d71fff2ced7817e3d3278bbdb3724a48f9e2e22a` |

For exact source links, append the listed relative path to
`https://github.com/VladimirReshetnikov/ProveIt/blob/f00ba53b331833c6cb64707bd90e48489e5610f5/`.
