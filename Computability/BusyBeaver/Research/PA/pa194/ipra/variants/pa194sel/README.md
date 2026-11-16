# PA194SEL in iPRA

[`PA194SELNative.consistency_iff_literal_nonhalt`](PA194SELNative.lean) proves
`iPRA ⊢ Con(PA) ↔ ¬Halt(PA194SEL)`. The halting sentence uses the
[delivered 388-row dense table](../../../../docs/pa194_sel_ax11gh_research_2026-11-14/machines/SEL/machine/pa194sel.tm),
with a blank start at state 0 and terminal halt at state 194. The table
SHA-256 is `5121f0b417ea025af140804b59e50a9d2fc3c461612e98b2f0ac86742c76a75b`.

The [finite certificates](PA194SELFinite.lean) check the eight changed native
rows, the dense control map, and the incoming history bits at the two
folded control pairs. Each primary transition is matched by one or three
PA194SEL transitions. In the [three-step case](PA194SELSegment.lean) the
selector reads the cell to the left, restores it, then makes the matching
right move. The relation and the step proof hold over arbitrary tape halves
in `IΣ₁` models. The [halting comparison](PA194SELHalting.lean) uses the shared
stuttering theorem before composing with the primary iPRA derivation.

Run from the repository root with fresh output directories.

```sh
pa=Computability/BusyBeaver/Research/PA
literal=/dev/shm/pa194-primary-for-sel
shared=/dev/shm/pa194b-for-sel
bash "$pa/pa194/ipra/native-endpoint/check-literal.sh" "$PWD" "$literal"
bash "$pa/pa194/ipra/variants/pa194b/check.sh" "$literal" "$shared"
bash "$pa/pa194/ipra/variants/pa194sel/check.sh" "$literal" "$shared" /dev/shm/pa194sel-replay
```

The PA194SEL replay regenerates the pinned row data and recompiles its six
Lean modules. It uses the checked primary and PA194B stages for shared
proofs. The final axiom report lists `propext`, `Classical.choice`, and
`Quot.sound`.
