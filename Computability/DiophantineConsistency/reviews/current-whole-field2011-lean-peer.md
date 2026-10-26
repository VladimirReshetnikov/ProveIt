# Current whole-field alignment: independent composition review

Date: 2026-10-26 UTC. Reviewer: `controller_certificate`. Result: **PASS**,
with no correction requested to the frozen sources.

The reviewed packet was authored by `complemented47_review`; root separately
read and replayed it. The reviewer authored the earlier doubled-clause,
cell-label, cell-translation, coarse-field-offset, and polynomial-window
modules. This receipt is an independent review of the new whole-field
composition, including its use of those dependencies. It is not an
independent authorship or fresh-closure claim for the entire proof chain.
Root authored the OneHot and DecodedWindow compositions; complemented
authored the SouthShift and generic cycle lemmas; circuit authored the
literal copy-parity module.

Exact reviewed bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentWholeField2011.lean` (156 lines) | `16c06800d326578b5898f2353229b574f2c0c8783bfadc362d517d34d2a5d079` |
| `CurrentWholeField2011Checks.lean` (60 lines) | `5a31aff2da1993be28dfb950d1a3761a73a3fd15b48375f74fa12779ab870c94` |
| `CurrentSouthShift2011.lean` | `256403c28ff13e2fb8585597a1931c1be8703f6726daaf3c5509cfbff5f8cf8d` |
| `NativeFieldCycles2011.lean` | `9cac50de2b83d3b802eab615ab4340027b842abc910586d009c4847b913f8442` |
| `CurrentFieldOffsets2011.lean` | `b44a1eb24d23bf9e744fee99531cab653c34029e41a3ab14386f95d72b60c683` |
| `CurrentCellLabels2011.lean` | `88698cd0d678d788c169b22915594b9ce37dd5d5c19c3d0069b190e0575f740d` |
| `CurrentCopyParity2011.lean` | `dc49658f1d9c448eca9ff969336cd5f64b4f64483b47b48d72f3a6bd0d928c8a` |
| `CurrentDecodedWindow2011.lean` | `fd52d069a146d13287cd7da987cc54117e19282efabba6c30c9b4a4f2a48b217` |

I read every line of the two target sources before execution. I also read
the complete SouthShift, NativeFieldCycles (including its 511-loop checks),
DecodedWindow, CopyParity, CellTranslation, FieldOffsets, OneHot, and
PolynomialWindow sources while checking the exact interfaces used here.

The principal `facts_whole_field` theorem takes the original
`Facts v N x c carry digits` alone, apart from the ambient finite cyclic
type instance. That structure contains the source equations, actual ports,
Boolean supported word, origin, normalized digits, carry bounds and mask
tests. It contains no supplied one-selector count, decoded labels,
fractional phase, whole-field alignment, occupation, or native tableau.
The endpoint derives its count and fractional phase before using the
decoded labels. It consistently retains the same `v`, `N`, source `x`,
word, carries and digits, and the same actual rank shift
`W=core.rank.toNat-47*(N*2011)`.

The Start derivation uses the exact decoded South complement510. Splitting
the nine-bit word into its low three bits shows that physical fields943
and944 are both1. The actual South-copy identities then give the temporal
sources961−t and962−t equal to1, where `t=W/47`. Independently, the actual
marker-copy identity and the origin bit give source1004−t equal to1.
No current marker value is assumed. Applying the coarse support/count
theorem yields precisely offsets0,19,20.

For offset19, SouthShift gives

```
S(b) = (2*S(theta(b))) % 512 + c(theta(b)+941).
```

The composition correctly applies the cycle theorem with the permutation
`theta.symm`, so its transition runs from the source cell to the target
cell. Booleanity and the nine-bit bound justify absorbing the final bit
into the modulo expression. The exceptional bit is the physical941
selector at that same source cell. The decoded terminal-selector theorem
forces its South value to one fixed expression determined by the actual
tile table. It does not require that fixed value to differ from511.

The generic cycle proof only excludes510 on a finite permutation. Its
three-predecessor argument makes the exceptional value511 if510 occurs;
then evenness and divisibility by4 contradict the periodic return to510.
The valid511 self-loop is explicitly preserved by the generic focused
checks. Neither uniqueness of Start nor universal occupation is used.

For offset20, the two physical selector prefix contributes
`c(theta(b)+940)+2*c(theta(b)+941)`. The actual count bound in that same
translated cell bounds this by2. The exact recurrence then uses the local
modulo4 obstruction: a value510 would require a source congruent to3
modulo4, although the recurrence at that source allows only residues0,1,2.
No invertibility, terminal-color value or occupation premise is needed for
this second exclusion.

Consequently `t%2011=0`. Combining this with `W%47=0` gives
`W%(47*2011)=0`. The final positive-polynomial endpoint obtains one original
arithmetic window and augments it by this result; it never resamples or
replaces its witnesses. Natural subtraction in `W` and arbitrarily large
cyclic shifts remain exactly those of the existing arithmetic endpoint.
The result does not yet assert that the resulting cell stride is positive.

Independent fresh replay used Lean `v4.32.0` with `-M6000 -j1`. A temporary
namespace directory contained symlinks to existing prerequisite objects,
excluding every target-module and target-check entry. The main object was
freshly compiled there; the checks imported that new object through an
explicit `LEAN_PATH` overlay. No shared source or object was modified.

```sh
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWholeField2011.lean \
  -o /tmp/current-whole-field2011-controller-peer/DiophantineConsistency/CurrentWholeField2011.olean
/usr/bin/time -f 'elapsed=%e peak_kb=%M exit=%x' lake env bash -c \
  'export LEAN_PATH="/tmp/current-whole-field2011-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentWholeField2011Checks.lean -o /tmp/current-whole-field2011-controller-peer/DiophantineConsistency/CurrentWholeField2011Checks.olean'
```

Both exited zero. Main:4.45 seconds,3275452KB peak, no Lean diagnostics.
Checks:3.26 seconds,3248196KB peak. All six reported theorem axiom sets
contain only `propext`, `Classical.choice`, and `Quot.sound`.

| Replay artifact | SHA256 |
| --- | --- |
| Timed main log | `09b339a5b920330f0ce9c9fa209a998252bf90dd841501ed6057daab4e6bab1f` |
| Timed checks log | `1084f2f26e56204af9febbef5041bb459fb7c7533e287f592796b3885ba6c565` |
| Fresh main object | `81d4a9d1638ec858e76ac0b9d1e9fd1df208a0007590f9d2bf42f9347d680476` |
| Fresh checks object | `a67c60271a88eb704fab273ea795a7aafe07ca86077e65f2721fad8dc7411787` |

This replay freshly checks the target packet against existing prerequisite
objects, not a fresh rebuild of the entire closure. The packet proves
whole-cell alignment for every actual positive polynomial zero. All-cell
occupation, matching tile assignments, machine-language semantics, the
reverse existence construction and the final consistency equivalence
remain separate obligations.
