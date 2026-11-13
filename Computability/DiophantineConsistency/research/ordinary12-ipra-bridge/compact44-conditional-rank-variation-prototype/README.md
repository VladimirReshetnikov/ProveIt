# Conditional compact44 rank variation

`CompactRankVariation.rank_variation` proves the exact compact-width rank
identity in any model of IΣ₁, for an arbitrary model coefficient `K`. It
requires **both** the original and modified cell words to satisfy the full
`PackingInput` conditions for the same `K`, masks, period and stride. It
also requires the exact cell-change equation

```
X1(j) = X0(j) + 2^(67*1063) * δ(j),  j < N,
```

Boolean `δ`, and the nonwrapping bounds `j+1<N` and `j+s<N` whenever
`δ(j)≠0`. Under those explicit hypotheses it proves

```
windowRank(X1) + Gamma(K,N,s) * bsum(590069,δ,N) = windowRank(X0).
```

`calibrated_rank` additionally assumes the controller congruence for that
**same** `δ` and derives `windowRank(X1) ≡ 590069*s (mod 590069*N)`.
Neither theorem constructs the modified word, establishes its packing or
mask/no-carry facts, proves physical dummy safety, or connects the selector
chosen by the previous calibration theorem to such a word. In particular,
the generic `K` has not here been identified with retained bytes or the
displayed equation. No graph zero or iPRA theorem follows from these clients.

The build recompiles `ArithmeticPacking` on the same symbolic controller
provider, then adapts `ArithmeticConstructionVariation` by replacing its
old-controller import and two generic helper references with the corresponding
compact-controller helpers. `check_adaptation.py` confirms the exact source
substitutions and namespace change; it is an external source comparison.

The first two modules compiled successfully. `ArithmeticPacking` emitted five
unused-section-variable linter warnings, all retained in its log; the adapted
variation module was warning-free. The initial compact client failed because
`zero_lt_one` was ambiguous; its source and output, including the error-recovery
`sorryAx` report for the unproved final theorem, are preserved. After qualifying
that name, the incremental retry exited 0 in 2.990 seconds without warnings;
both final declarations report `propext`, `Classical.choice`, and `Quot.sound`,
with no `sorryAx`. Commands, direct object hashes, source hashes, logs and
terminal receipts are in `observations/`.

This is a single-author incremental same-provider build, not a paired replay
or a fresh authenticated project/package closure. Inherited earlier linter
warnings, transitive and dynamic provider ancestry, and between-check
limitations remain.
