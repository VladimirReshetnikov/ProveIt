# Current field offsets: author implementation receipt

Date: 2026-10-26 UTC. Author: `controller_certificate`, at root's assignment.
This is an author receipt, not an independent peer review. No frozen module
or maintained equation file was edited.

Frozen source bindings:

| File under `Lean/DiophantineConsistency/` | SHA256 |
| --- | --- |
| `CurrentFieldOffsets2011.lean` (143 lines) | `b44a1eb24d23bf9e744fee99531cab653c34029e41a3ab14386f95d72b60c683` |
| `CurrentFieldOffsets2011Checks.lean` (57 lines) | `0146ee0c0e854876db4c808e88cd7d79052083c881238e288423ab0eee82c678` |
| Imported `CurrentCellTranslation2011.lean` | `c3e9811e9b5c60c8ed740b58277ed40569108f888347ffcbb84169ba31b5685d` |

I reread the complete translation module, the actual low-support definition,
and the physical-count/prefix identity before implementation. Both complete
new sources were read before the final execution.

The exact `coarse_offset` endpoint takes a natural-valued cyclic word `c`,
an arbitrary natural shift `t`, the actual periodic low support, a selector
count at most one at every aligned `Cell N`, and only these three source
equalities:

```
c(1004-t) = 1
c(961-t)  = 1
c(962-t)  = 1
```

All positions here are in `ZMod (N*2011)`. It proves
`t%2011=0 ∨ t%2011=19 ∨ t%2011=20`. A separate Booleanity premise is
unnecessary: support, the count bound, and the three actual ones suffice.
There is no decoded-label, occupation, supplied alignment, or current
marker-value premise.

The proof proceeds in three independently exported steps. First, actual
support has no field above1004 and no field in986..1003. The shifted marker
therefore forces `r≤1004` and either `r=0` or `r≥19`, where `r=t%2011`.
Second, if `r>961`, the forced961 source wraps to `2011+961-r`, which is
above1004 under the marker bound; thus `r≤961`. Both arguments use the
proved cyclic residue formulas, never truncated natural field subtraction.

Third, for `21≤r≤961`, the translation equivalence puts both forced sources
in exactly `theta t 0`, at the distinct positions `961-r` and `962-r`.
Their ranges are respectively0..940 and1..941, so both are physical
selectors. The generic finite-sum lemma `two_ones_sum_ge_two` bounds the sum
by its two-element subset. `two_distinct_selectors_force_count` transfers
this to the actual selector count through the proved physical permutation
and prefix identity. The resulting count at least two contradicts the
given bound at that same translated cell. No table enumeration is used.

Focused checks restate the exact minimal endpoint, exclude18 using only
the marker and support, and test both endpoints21 and961 of the two-selector
interval. The concrete index-pair check includes940 and941. Arbitrary large
shifts and `N=1` remain covered by the inherited translation theorem; no
bound on `t` or extra condition on `N` is added.

Fresh sequential commands, with Lean `v4.32.0`:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentFieldOffsets2011.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentFieldOffsets2011.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/CurrentFieldOffsets2011Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/CurrentFieldOffsets2011Checks.lean
```

Both exited zero. The main diagnostics are empty, SHA256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log SHA256 is
`270beb5bab02d15f94e59d060d8affc5049011c654bfdf402bd0a1b84fcfae64`.
All six axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, custom axiom, or native evaluation axiom occurs.

Development history: the first compile needed canonical normalization of
natural numeral casts before the linear arithmetic tactic could identify
the source support and residue expressions. Unused section instances were
also omitted. No mathematical assumption or conclusion changed.

Scope: the three source ones remain explicit inputs to this module. Their
derivation from decoded StartSouth510 and actual copy/marker parity is a
separate composition. Offsets19 and20 are intentionally not excluded here;
the generic cycle arguments and literal nine-bit aggregation supply that
next step. No native-language or consistency endpoint is claimed.
