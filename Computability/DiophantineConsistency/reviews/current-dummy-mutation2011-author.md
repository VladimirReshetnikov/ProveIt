# Exact dummy mutation: author receipt

The packet proves an actual one-slot source update, its exact positional
increment, and the resulting ordinary transport and rank increments under an
explicit nonwrapping bound. It does not assert that arbitrary dummy positions
are safe or that the bound has been discharged. This is an author receipt,
not an independent review.

## Frozen files

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/CurrentDummyMutation2011.lean` | 193 | `7bddcd9b7380e296a524ef229b467d4875e81a609dd4a4c5a7b126804a424f96` |
| `Lean/DiophantineConsistency/CurrentDummyMutation2011Checks.lean` | 91 | `12a960efd87d6596b6be56aab02176e18ddbe776ca07e8a305c498338ce45f25` |

Direct imports are:

| Module | SHA-256 |
| --- | --- |
| `CurrentWordHighMask2011` | `f14b90ec3d4210c75dce2e4ece4de6f50bb1b2069e26b9329309eadd1c7da74a` |
| `NativeRankVariation` | `46c226eba0018eb15eaec66bb31b2ea8af7682fbef76d0245ee45c6aa236ef73` |

The first import supplies the exact quotient/remainder `cell_representation`,
not a high-mask assumption. Reused construction interfaces are
`CurrentWordConstruction2011` (`9455d6c2015906a8f76ff2be5275a95cae5340f0ca3e8dc16666ffc6bab2b5b8`),
`CurrentCarryConstruction2011` (`6efd60cd1ce0f40aa48e68ec7d9c2b2c680bbdc0aa289488c268e79fa68a026a`),
and `CurrentWordClause2011` (`df93b7dc684693e23097e5bfdba9aa3a9121595574b6026832d2a4f3f2fd24dc`).
The author also authored `NativeRankVariation` and separately reviewed the
high-mask composition and constructed-word interfaces. Those roles do not
constitute an independent review of this new packet.

## Exact result and premises

`word_update_dummy` proves equality of the complete functions: updating dummy
cell `j` to 1 updates exactly physical position `base j + 977` of the assembled
word to 1. `word_update_unchanged` exposes preservation of every other physical
position. Both statements permit arbitrary natural dummy and marker values;
they do not assume Boolean controls, a zero old value, or tile matching.
Canonical quotient/remainder reconstruction handles the last cell and `N=1`.

With the separate premise `dummy j = 0`, `source_increment` proves

```
C' = C + delta_j,
delta_j = radix^977 * (radix^2011)^j.val.
```

The generic sum lemma is an ordinary finite sum identity, not a cyclic residue
identity. The exponent uses the canonical `j.val`; no place wraps around the
whole word. Setting an already enabled dummy to 1 is deliberately not claimed
to add another unit.

For Boolean controls, the actual transport factor is
`A = CurrentKernel2011.K + 2^(displacement s)`, where
`displacement s = 47*(2011*s)`. `normalized_increment` accepts the two actual
carry `Facts` and the explicit hypothesis

```
F + A*delta_j < radix^(N*2011) - 1.
```

It derives strictness of the new normalized word from the actual clause,
then uses both transport congruences and uniqueness of strict representatives
to conclude the ordinary equality `F' = F + A*delta_j`. Old strictness is not
an additional premise. `exists_normalized_increment` constructs the updated
carry solution and digits before proving this equality; it needs only the old
`Facts` and the same explicit bound. No tiling, marked-origin, high-mask,
safe-position, or desired-update-equality premise appears.

Only after deriving both ordinary equalities does `rank_decrement` apply the
accepted ring identity. For `q = radix^(N*2011)`, `D = radix^977`,
`B = radix^2011`, it proves the exact integer decrement
`-rankGamma q A D * B^j.val`, with `rankGamma q A D = D*(q^2-1)*(1+q*A)`.
The mask parameters `MC`, source `MF`, and `J` stay fixed and generic; no second
high-mask shift is inserted. The theorem does not claim positivity of either
rank, actual front-witness construction, a closed controller orbit, or a
complete consistency equivalence.

## Fresh checks

All new source and checks were read before execution, and the final main was
read in full after corrections. Both files set `Elab.async false`; builds ran
sequentially with the bounded direct commands:

```sh
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentDummyMutation2011.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentDummyMutation2011.olean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentDummyMutation2011Checks.lean -o .lake/build/lib/lean/DiophantineConsistency/CurrentDummyMutation2011Checks.olean
```

Both passed with no diagnostic. Main took 4.12 seconds with peak RSS
3,273,264 KiB; checks took 4.06 seconds with peak RSS 3,258,780 KiB. All 11
axiom reports contain only standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) or no axioms. No `sorry`, added axiom, or `native_decide` occurs.
Existing prerequisites were reused; no dependency replay or mutation is
claimed. No frozen source, shared documentation, maintained equation, or git
state was changed by this task.

Checks include arbitrary numeric digit updates, the already-enabled negative
control, canonical source positions 977 and 2988, repeated cell casts at `N=1`,
an actual source update with marker value 23, preservation of the actual marker
slot, and the `q=1` zero-Gamma control. The modular-wrap counterexample has
`A=7`, `C=1`, `C'=2`, `F=2`, `F'=4`, modulus 5: both transports and new strictness
hold but the ordinary proposed sum is 9. A separate no-wrap example succeeds.
Thus the key bound is tested as a necessary restriction, not silently omitted.

Development fixes were only elaboration/API details: the pinned Mathlib name
`Function.update_self`, an explicit positive-radix proof, numeral-cast
normalization, explicit integer coefficient-ring arguments, and omission of
two unused section instances. No mathematical assumption was strengthened.

| Artifact | SHA-256 |
| --- | --- |
| Main `.olean` | `b5957a17097df06225d106560bec2918217a91f86f27e9cecbffa0b06069aa38` |
| Checks `.olean` | `8e911f1ca754fbef3763988155397501b3cdebe63c57be2eaaa864061a8fa88a` |
| `/tmp/current-dummy-mutation-main-stage3.log` | `20ee00d36011e2d7e00bc8e94ef877e4fafa0dcfcf588fbf25ff05d1a9ba4440` |
| `/tmp/current-dummy-mutation-checks-stage1.log` | `8205ae2dd8b4a2412589fe889182e19a281c27fe0583006f304f48d07f12d211` |
