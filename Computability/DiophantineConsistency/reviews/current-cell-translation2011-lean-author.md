# Current cell translation: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This records author inspection and fresh checks, not an independent peer
review. No frozen dependency or maintained equation file was edited.

Frozen source bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentCellTranslation2011.lean` (151 lines) | `c3e9811e9b5c60c8ed740b58277ed40569108f888347ffcbb84169ba31b5685d` |
| `CurrentCellTranslation2011Checks.lean` (59 lines) | `cdf55b1ea004d415075483ff00d1f9a500255c39f545192ca0ad26d3eebe0f03` |
| Imported `CurrentClause2011.lean` | `a76daeaa24d3b3b00cfb80e2aaa3c9082740f9f8349a8d18014c912a9001c566` |

Before implementation I read the complete whole-field alignment plan and
the imported addition/subtraction residue proofs. The complete new module
and checks were read before their final execution.

`Cell N` is exactly the finite aligned subtype
`{b : ZMod (N*2011) // b.val%2011=0}`. Its ambient modulus never changes to
2011 or to a separate `ZMod N` coordinate system. A zero cell and the
inherited finite instance are available. `wholeShift t = t-t%2011` is
proved divisible by 2011 using the quotient/remainder identity; the natural
subtraction is bounded by the standard remainder inequality.

The explicit equivalence `theta t : Cell N ≃ Cell N` subtracts the cast of
`wholeShift t`. Its inverse adds the same group element. Both maps preserve
alignment, and the inverse laws are group identities on the subtype.

For `r=t%2011`, the source theorems prove:

* if `r≤e`, the exact group equality
  `b+e-t = theta(t)(b) + (e-r)`; no upper bound on `e` is needed;
* if `e<2011`, the source's physical residue is
  `(2011+e-r)%2011`;
* if `e<r`, that residue is exactly `2011+e-r`, with no truncation;
* the optional exact wrapped equality uses
  `theta(t)(b)-2011+(2011+e-r)`, retaining subtraction of the preceding
  cell as a group operation.

All natural casts of subtractions have their nontruncation conditions
proved. The source formulas use the full cyclic residue lemmas, so they
cover arbitrary natural temporal shifts, including shifts greater than
the entire word. `theta_add_full_period` additionally proves that adding
any multiple of `N*2011` leaves the equivalence unchanged. `cell_one_eq_zero`
and `theta_one` prove the single-cell case explicitly.

Focused checks verify finiteness, both inverse laws, the actual offset19
and offset20 source formulas used by the planned nine-bit aggregation,
a wrapped source with residue1971 instead of truncated zero, arbitrary
whole-word multiples, and `N=1`. They introduce no labels, occupancy,
calibration, one-hot, phase-alignment, or native-source premise.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellTranslation2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellTranslation2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentCellTranslation2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentCellTranslation2011Checks.lean
```

Both exited zero. The main diagnostics are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`eb87bce9e788f6772f44b3e370377eb107a040e94fcef8a67302005f0db623ea`.
All seven axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound` (the divisibility lemma uses the smaller subset). There is no
`sorry`, custom axiom, or native evaluation axiom.

Development history: the first draft needed simplification of both sides
of the residue equality, an explicit coercion of the zero cell, and an
increased elaboration recursion bound for the closed single-cell instance.
The wrapped identity's unnecessary range hypothesis was removed. A focused
check subsequently needed normalization of the natural cast960. These were
elaboration/interface corrections; no required geometry claim was weakened.

Scope: this packet supplies only exact cyclic cell geometry. It does not
exclude a nonzero field offset, aggregate copy parities, decode labels,
propagate occupation, or prove native/machine/consistency equivalence.
