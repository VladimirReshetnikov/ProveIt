# One-dummy physical safety: author receipt

Frozen, freshly checked, 2026-10-26. Author: `controller_certificate`.
I read both entire final sources before their first capped builds, which both
passed without changes. This is an author audit, not an independent review.
I authored the reused kernel, word, clause, and top-bound modules;
`circuit_reduction` authored the independently reviewed dummy-mutation and
rank-variation modules, and ROOT authored the carry construction. No accepted
source, shared documentation, or Git state was changed.

| New file | Lines / bytes | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/CurrentDummySafety2011.lean` | 213 / 10682 | `31f92f372076071c75ece964cb418c118fa051694057556c004d74a7353e7c00` |
| `Lean/DiophantineConsistency/CurrentDummySafety2011Checks.lean` | 81 / 4028 | `0ff01ecb9c436f6f7043449c666d2473687725067e9aa5bd7729af39a6f7efe7` |

## Exact scope and derivation

The numerical theorems assume only the literal canonical position inequalities

```
j.val + 1 < N,       j.val + s < N.
```

They place the spatial and temporal destinations inside the whole word. They
do not assert that a normalized increment is already safe, supply a desired
ordinary F equality, or assume a tableau, mask, source tuple, or controller
orbit. Stride zero is allowed. The first inequality itself implies N is at
least two; N=1 and a final-cell update are correctly excluded by the stated
inequality, rather than by a hidden extra premise.

Write `rho = 2^47`, `m = 2011*N`, and
`delta = rho^977*(rho^2011)^j.val`. Every one of the literal kernel's term
exponents is at most 2020, including the spatial bare term. The previously
checked complete coefficient mass is 7659829036801887, which is less than
`rho^2`. A generic finite-sum bound, requiring neither support injectivity nor
collision analysis, therefore proves

```
K <= 7659829036801887 * rho^2020 < rho^2022.
```

The actual displacement is `47*(2011*s)`, so
`2^displacement = rho^(2011*s)` without modular reduction. The two position
inequalities give exact natural-exponent margins:

```
K*delta < rho^(2999+2011*j.val) <= rho^(m-1023),
2^displacement*delta = rho^(977+2011*(j.val+s)) <= rho^(m-1034).
```

All subtractions are controlled by the separately derived `4022 <= m`.
Both terms are bounded by `rho^(m-3)`, at least the first strictly. Since
`2 <= rho`, `safe_increment_bound` proves

```
0 < (K+2^displacement)*delta < rho^(m-2).
```

`safe_increment_div_bound` identifies the last bound with the actual natural
quotient `rho^m/rho^2`. The proof is deliberately coarse but retains all
kernel terms; it does not silently omit the spatial monomial or rely on
an external finite certificate.

For any actual assembled tile word with independent Boolean dummy and marker
maps, `normalized_nonwrap_of_safe` uses the original carry `Facts` and the
proved top bound `F < rho^(m-1)` to derive

```
F + (K+2^displacement)*delta < rho^m-1.
```

The generic arithmetic helper proves this from the two strict short-word
bounds, not from transport congruences. The old F and its carry solution are
unchanged. `safe_normalized_increment` applies the accepted mutation theorem
to any two actual normalizations and obtains their ordinary F equality.
`exists_safe_normalized_increment` constructs the new normalization, retains
its `Facts`, and returns **both** ordinary C and F equalities. It additionally
requires `dummy j=0`, exactly because updating an already enabled bit is not
an increment. No nonwrapping hypothesis remains at these endpoints.

`safe_rank_decrement` gives the full signed rank identity using the same
ordinary changes, with fixed generic MC, already shifted source MF, and J.
It retains the actual coefficient
`rankGamma (rho^m) (K+2^displacement) (rho^977)` and factor
`(rho^2011)^j.val`. It does not claim rank positivity, prescribed residues,
or a whole finite-subset controller.

## Checks and bounded builds

The checks cover the maximum exponent2020, strides0 and1, a repeated integer
cast into ZMod3, the last permitted update cell, N=1 impossibility, and the
spatial/temporal exponents that would cross the whole-word boundary if the
corresponding condition were dropped. A construction example starts with an
arbitrary two-cell tile assignment and arbitrary Boolean marker values,
constructs the initial normalization, enables the zero dummy at cell0, and
constructs the new normalization with both ordinary word equalities. It assumes
no matching, marked origin, high mask, old F, or desired increment. The
already-enabled-dummy exclusion remains explicit.

Both new files set `Elab.async false`. The two sequential author commands were
run from the repository root using Lean4.32.0:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentDummySafety2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentDummySafety2011.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentDummySafety2011Checks.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentDummySafety2011Checks.olean
```

Both first builds exited zero, with no warnings or errors. Main: 6.38 seconds,
3,287,312 KB peak RSS. Checks: 3.52 seconds, 3,257,304 KB. All 13 printed axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`, or a
subset. No cap was raised, no prerequisite build was launched, and no unsafe
evaluation or extra axiom was used. These are fresh builds of the two new
modules against existing accepted imports, not a full dependency replay.

| Artifact | SHA256 |
|---|---|
| Main `.olean` | `987d72a91d4496ebe5273b9be53576455f04ba7340fb18c12991520ab5f3fcd6` |
| Checks `.olean` | `031d186efa0644193edcb75ceb561d5104a04476926c168b681491b2d8f0e0c3` |
| `/tmp/current-dummy-safety2011-main.log` | `7cce3863ba628e1405e0885a8a224935a33dac024d6267b584963883151e0efa` |
| `/tmp/current-dummy-safety2011-checks.log` | `6fc75b4fc3edfd5246844d076166bad568a3ef4ea110a1d4371f52a8fc4b558b` |

Direct source imports are pinned as follows:

| Dependency | Source SHA256 |
|---|---|
| `CurrentDummyMutation2011` | `7bddcd9b7380e296a524ef229b467d4875e81a609dd4a4c5a7b126804a424f96` |
| `CurrentWordTopBounds2011` | `7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f` |

The literal coefficient bound also uses the unchanged `CurrentKernel2011`
source `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55`.
The imported main objects of these three dependencies respectively have
hashes `b5957a17097df06225d106560bec2918217a91f86f27e9cecbffa0b06069aa38`,
`e9a8ad9d137e9493351a846ea4946714f6d0a3878b2e39a596ae30334df911ac`,
and `149b7322775beeda97e66e0272d9f4869e66bd1489a2da6c8c80df7b1bb698c2`.

This packet closes physical safety for one actual unused dummy update. A
separate finite-support composition is still needed to accumulate many updates
and realize a controller sum. Neither that composition nor the converse
polynomial/Con(ZFC) endpoint is claimed here.
