# Current marker fractional-phase proof: author receipt

This is an author self-review and fresh Lean replay receipt, not an independent
peer review. The complete 165-line module and 49-line checks were read after
the final edits. No existing source, umbrella module or candidate was changed.

## Frozen sources

Paths below are relative to `Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentPhaseParity2011.lean` | `3abd1bc07fe430892871e13b0b066a689ef74854a45bc725ee73bfe349325eb7` |
| `Lean/DiophantineConsistency/CurrentPhaseParity2011Checks.lean` | `a920ab91be02c8880c9f5d69311a5ccd30e907a6358516b49553b7f6f0e2ac93` |

The module directly imports `CurrentReflectedGeometry2011`
(`268ecac628932a93d79593ae0b4e1c8819817db58f27ec9613c4ad23a29d60c1`),
`CurrentClause2011`
(`a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566`),
and `NativeBooleanRotation`
(`d50110d8f2a959df7da69f23e80b4df09a1aad98ba2b66c67d2445203cf81f3e`).
The checks additionally import `NativeWindowCarry`
(`df80356d4f26e30859b47aed5d39c913e4e3dfd7b876f82e816fdd4008edd589`).
The actual mask comes from `CurrentHighDigits2011`
(`ff6eb32b735f59989d7b21ed835f4c64b5a8bed206a9a4b96a54f25016c35d02`).

## Mathematical scope

For a positive cyclic length `N*2011`, the proof uses the literal kernel and
its actual convolution formula. At field `b+1004`, with `b` a cell origin,
the bare18 and2020 sources have cell residues986 and995. Neither belongs
to the actual low support. The bare1004 source is exactly `c b`; the full
reflected sum is retained. Thus

`convolution folded c (b+1004) = c b + reflected c (b+1004)`.

The repeated high mask at that field is exactly1; the subtraction of one
at the global origin does not alter it. Its disjointness test therefore
forces the normalized marker digit to be even.

For arbitrary Boolean source digits, the actual binary rotation is bounded
by `2^46`. The physical at-most-one selector count in this cell, together
with periodic sparse support, supplies the imported low-field reset at
the marker predecessor. Carry recurrence and the local radix equation then
give normalized marker parity equal to the parity of `c b` plus the actual
temporal digit. The reflected sum is even unconditionally, and reduction
by the even radix does not change parity.

For a nonzero fractional phase `W%47`, the Boolean rotation theorem makes
every temporal digit even. Hence the marker test forces `c b=0`. Applying
this at `b=0` contradicts the forced origin `c 0=1`, proving `W%47=0`.

The final theorem requires a physical at-most-one count **only at the origin
cell**. It keeps explicit the Boolean digit bound, periodic support, forced
origin, carry bound57, actual carry recurrence, local digit equation and
actual high-mask tests. It assumes no decoded labels, occupation, marker
value, prior phase alignment, tile interpretation, or consistency
equivalence. In particular, the preliminary count bound still must be
supplied by the earlier arithmetic/padding argument.

The focused checks also instantiate the result with the actual source
`NativeWindowCarry.temporalDigits 47 x c`, proving

`((NativePellBootstrap.nativeRank x).toNat - 47*(N*2011)) % 47 = 0`

under those same explicit native digit/carry hypotheses. This is a native
phase lemma; it is not the complete equation-to-Con(ZFC) theorem.

## Fresh verification

Both final commands exited0 from the repository root, with one process at
a time and asynchronous elaboration disabled in each new source:

```sh
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentPhaseParity2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPhaseParity2011.lean
lake env lean -M 6000 -j 1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentPhaseParity2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentPhaseParity2011Checks.lean
```

The final main log `/tmp/current-phase-parity-stage2.log` is empty. The final
checks log `/tmp/current-phase-parity-checks-stage2.log` contains seven axiom
reports, each limited to `propext`, `Classical.choice` and `Quot.sound`.
A source scan found no `sorry`, `admit`, added `axiom` or `native_decide`.
