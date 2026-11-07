# The source34 tuple: a Lean calibration (in progress)

6 November 2026. Claude session; not a paired replay.

## Why this tuple

Package 132's fifteen-integer 44 / 111
(`132-signed-caps-free-scales/lowdegree/equation.json`) binds the six
**source34** ports ("mixed-parity-unrounded-1064921"), not package 31's
wang943-mixed-121x8801 tuple. Its recipe is
[`source34_coefficients.md`](../../candidates/valuation-shared-norms/source/inherited/root_fusion/provenance/upstream_ordinary/source34_coefficients.md)
and its byte pins are
[`101-constructive-reductions/integer14/upstream/coefficients/BINDING.json`](../../con-zfc-diophantine-forms/101-constructive-reductions/integer14/upstream/coefficients/BINDING.json).

Shared with the [121x8801 calibration](../mixed121-calibration/README.md):
the 943 tile rows, `b = 121`, `L = 8801`, `d = 1064921`, `ρ = 2^121`, the
clause coefficients and weights `W j = 2^(10+2j)`, the anchors
`1095, 1096, 2195, 3296`, the clause targets `4393, 5495`, the padding `Z`,
and the `λ = 2341` dummy-bit controller (`Mixed121ControllerData` and
`Mixed121ControllerChoice` depend only on `d` and `λ`).

Different:

| | 121x8801 | source34 |
|---|---|---|
| bare `D_C` terms | `ρ^30, ρ^62, ρ^1100, ρ^2200` | `ρ^40, ρ^41, ρ^1100, ρ^2200` |
| `D_R` | `ρ^42` | `ρ` |
| copy track `t` (W, N, E, S) | `1023, 1013, 1003, 983` `+ j` | `1020, 1000, 980, 960` `+ 2j` |
| `MF` field targets | `1013 + j`, `1065 + j` | `1000 + 2j`, `1021 + 2j` |
| `K mod C0` | `510020909` | `2050743806` |
| `Γ mod C0`, its order | `686053463`, `5070` | `1150455639`, `334620` |

The prime-unit table of the recipe (`H0 mod p = 7, 1, 53, 594` at
`p = 11, 13, 677, 2341`) is reproduced by the numbers above.

## Finite binding

[`tools/check_recipe.py`](tools/check_recipe.py) implements the recipe from
the Lean rows `Compact44/Compact943Data.lean` and reproduces all six payloads
(β, K0, MC, MF, `cone_A = 2^1113`, `cone_B = 2^666104`) byte for byte against
both the SHA-256 pins of the binding and the gzip files in
`candidates/valuation-shared-norms/source/inherited/root_fusion/coefficients/`.
This is a finite check outside Lean.

## Remaining work

1. A `Source34/` port of the Mixed121 calibration modules: kernel, ports,
   masks, kernel residue, controller unit, then the decoding, column and
   packing layers with the stride-2 copy geometry.
2. The 44 / 111 graph and its signed (ℤ-variable) reduction, the first
   ℤ-variable endpoint of the tree.
