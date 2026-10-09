# Focused review of the occupancy-filtered search variants

## Scope and source identity

The following two later variants were compared line by line with the previously reviewed top-six source. No logical error was found in the changes. This is a focused manual source-diff audit; it does not claim a new independent regression batch or a rerun of any large impossibility computation.

| Snapshot | SHA-256 |
|---|---|
| `rainbow_filtered.cpp` | `fb6f36feae7967419939f69e3f3e167295738ab5830c42c21d0a3e904abba909` |
| `rainbow_prefix_filtered.cpp` | `43928be3b2fcb6a2e5d740f1cc80d6c11472bc89dbc606c9b3200c61f3f476f4` |

The unchanged original side-eight proof source remains the snapshot with SHA-256 `321fd408db85b0e91543dbac68838d784fd8ee16032aabfc52d4d6b2939ca64d`. The later variants must be associated with their own source hashes and complete run records for any further exact upper-bound claim.

## 1. Filtering before each diameter case

`rainbow_filtered.cpp` adds one stage to the diameter case loop. It computes the number of exact palette members in each residue class modulo four at or below the proposed squared diameter D. It then keeps only occupancy vectors whose required residue counts fit those capacities.

Every pairwise distance of a configuration with diameter D belongs to this capped palette. The residue requirements are determined exactly by its eight coordinate-parity class populations. Failing these capacities therefore proves that the whole diameter case is impossible, before any additional edge choices need be examined.

The implementation copies the original occupancy IDs into an immutable `global_occupancies` vector before the case loop. At the start of every case it rebuilds `all_occupancies` from that global copy. Consequently, exclusions for a previous case cannot leak into a later case with a larger or differently placed diameter.

Every filtered-out diameter case still produces an explicit UNSAT case row. The complete case indices and coverage remain unchanged. There is an additional `mod4_filter` explanatory line, so log readers intended for these variants should recognize or ignore that line rather than applying the original run's fixed line-count parser verbatim.

## 2. Filtering at each processed-edge prefix

`rainbow_prefix_filtered.cpp` adds `filter_prefix`, invokes it before entering or extending the processed-edge prefix, and passes the surviving occupancy IDs to descendants and the ordinary search. The original prefix enumeration and its symmetry groups are unchanged.

Let S be the selected set, s its size, C the candidates, and h the number of further points needed. The new preliminary conditions are:

1. `|C| >= h`, because a completion must choose h different candidates.
2. The union of candidate-to-S radial colors has at least s*h members, because those s*h edges of a valid completion have distinct lengths.
3. Each final coordinate-parity class population lies between its selected count and selected-plus-candidate count.
4. Its four exact residue requirements fit the available color capacities.

All four conditions are necessary. Their use before a branch has been explored may save work but cannot remove a valid completion.

The fourth condition uses the color set

```text
used selected-edge colors  UNION  {whole-cube palette colors <= current cap}.
```

This is a safe superset of every possible completion's colors. In particular, `used` retains all processed longer edges, so lowering the cap does not incorrectly delete those colors from the capacity calculation. Every as-yet-unselected edge must be at most the current cap under the prefix invariant. The set may include impossible colors; that weakens the pruning but preserves soundness.

## 3. Propagating occupancy IDs and symmetry

The parent list contains every occupancy vector of a possible completion of the parent prefix. The child list removes only vectors that violate necessary conditions of the child's selected set, candidates, or color superset. Induction therefore preserves every possible completion's occupancy vector.

The active cube subgroup fixes each processed unordered edge, hence its union of selected endpoints and the complete candidate conditions. A symmetry used to canonicalize the next edge maps a valid completion to another valid completion of the same prefix. Its occupancy vector therefore remains among the allowed parent IDs by the same necessary-condition argument. Filtering does not invalidate the existing symmetry reduction.

Before each diameter case, the global occupancy list is reset as in the first variant. The initial prefix filter's `move(initial_allowed)` affects only that case. Recursive prefix filters hold separate local `allowed` vectors and pass them by const reference during descendant calls; their lifetimes cover those calls and sibling filtering starts from the correct parent list.

## 4. Base cases and disabled modulo-four option

For a valid selected set that already has the target size, h=0. The candidate-count and radial-count tests are then vacuous, and its true occupancy passes the other necessary conditions. Applying the filter before the success base case cannot remove a valid solution.

With `USE_MOD4=0`, the filter performs only the candidate-count and radial-union tests, then copies the parent IDs without using them to reject the state. The original ordinary search also bypasses occupancy pruning in this mode. Empty occupancy-ID lists under that compile option are consequently harmless.

No new distance-mask or vertex-bitset indices were introduced. The original n<=10 bounds continue to apply.

## Review conclusion

These diffs add necessary tests and move existing necessary tests earlier; they do not alter the exhaustive choice of diameter or edge-prefix representatives. Complete results from these variants can use the same mathematical completeness argument, with the additional filter proof above, provided the matching source snapshot, full outer case coverage, and completed execution record are retained.
