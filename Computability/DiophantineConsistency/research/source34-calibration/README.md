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

## Done in Lean (7 November 2026)

`Source34/Source34Kernel`, `Source34KernelResidue`, `Source34ConstructionUnit`,
`Source34Ports`, `Source34Masks` and `Source34Calibration`: the kernel and its
support facts (clause bands disjoint modulo `L`, anchor bands meeting only at
`2195/3296`), `K ≡ 2050743806 (mod C0)`, the controller unit
(`Γ ≡ 1150455639`, order `334620`), the four ports with their leaf bounds, the
five mask facts, and the chosen-dimension rank calibration. Axioms:
`propext`, `Classical.choice`, `Quot.sound`.
[`tools/check_ports.py`](tools/check_ports.py) matches the `MC` and `MF` digit
lists with the payloads.

**The `LeafFacts` halting chain at the source34 ports** (27 further modules,
`Source34Band` … `Source34Halt`): every positive valuation with
`CompactLeafFacts.LeafFacts Source34Ports.ports v` in a model of `𝗜𝚺₁` gives
internal halting of machine 215 (`Source34Halt.halts_of_facts`, same statement
as `Mixed121Halt.halts_of_facts`). Only tuple-specific declarations are
restated; generic Mixed121 definitions and lemmas, and all of `Mixed121/W121/`,
are reused under their own names, so the two calibrations share their generic
constants. The changed geometry is the stride-two field windows: the vertical
target `1000 + 2u` sees only the shift-40 source `960 + 2u` and the temporal
source, the horizontal target `1021 + 2u` only the shift-41 source `980 + 2u`
and the spatial source `1020 + 2u` (shift `8802`); `Source34Field` proves both
by `interval_cases u` (`omega` alone could not handle `2u` against `8801` with
the parity test). Every finite geometric fact was checked in Python before it
was proved.

**The converse at the source34 ports** (9 November 2026, 17 further modules,
`Source34PulseBit` … `Source34Converse`): an internal halt of machine 215 gives
a positive solution of the leaf facts at the source34 ports.

* `Source34Seeds.halt_first_gamma` is the canonical halting data. It has the
  same statement as `Mixed121Seeds.halt_first_gamma`, with the source34
  kernel, masks, constructed rank and base cell.
* `Source34Converse.converse_facts` builds the 31 coordinates of the
  31-input parent source. It reuses the generic ring identity
  `Nine121.Source31Converse.rows_zero` and the port-generic
  `Source31Facts.facts_ports`.
* `Source34Converse.halt_iff_facts` combines it with
  `Source34Halt.halts_of_facts`. In every model of `𝗜𝚺₁`, machine 215 halts
  internally iff the leaf facts have a positive solution at the source34
  ports.

The 16 ported modules are exactly the closure of `Mixed121Seeds`, minus what
`Source34/` already had and the generic Mixed121 code. Tuple-specific changes:

* the field windows are named by an index `u < 10` (`1000 + 2u`,
  `1021 + 2u`);
* the copy digit gets its own lemma `Source34Cell.trackDigit`;
* the kernel's top exponent is `8802`, so `2^1065042 ≤ K < 2^1065043`;
* the bare kernel terms are `{40, 41, 1100, 2200}`.

Axioms: `propext`, `Classical.choice`, `Quot.sound`.

## The completeness obstruction

44 / 111's guard is `G = budget − pos`, `pos = 1 + p₁² + p₂² + p₃(p₃+1)`. The
completeness direction must represent the canonical family's budget as
`pos(p₁, p₂, p₃)`, that is `4·budget − 3` as `(2p₁)² + (2p₂)² + (2p₃+1)²`,
inside every model of `𝗜𝚺₁`. That is Legendre's three-square theorem for
`N ≡ 1 (mod 4)`. No free parameter of the canonical family moves `budget`, and
the theorem is in neither Mathlib nor this tree. Soundness needs only
`pos > 0`, so the calibration below still serves the forward direction; the
iPRA equivalence also needs an internal three-square theorem.

## Remaining work

1. The per-point graphs of the source34 rows and their signed (ℤ-variable)
   reductions. The 11ℤ rows (138, 172) avoid the three-square guard. They
   need the integer toolkit of [`zrows-toolkit`](../zrows-toolkit/README.md)
   and package 132's signed soundness chain down to the leaf facts.
2. For 44 / 111 and the other `pos`-guarded rows: an internal three-square
   theorem (see above).
