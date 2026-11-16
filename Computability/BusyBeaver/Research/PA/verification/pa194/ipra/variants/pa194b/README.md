# PA194B in iPRA

[`PA194BNative.consistency_iff_literal_nonhalt`](PA194BNative.lean) proves
`iPRA ⊢ Con(PA) ↔ ¬Halt(PA194B)`. The halting sentence is the shared
arithmetic machine predicate for the [delivered dense table](../../../../../docs/PA194B_PA194G_research_2026-11-14/machine/pa194B.tm),
with blank start at state 0 and terminal halt at state 194. The table has
388 rows and SHA-256
`b2bcdb6c3816a1fbade699a79e431e4b530ec341aaf516c911920d43f9995397`.

The [finite certificates](PA194BFinite.lean) check the four changed rows
in native numbering, the control map between dense tables, and the incoming
rows that distinguish the two primary reader states by the bit left of the
head. The [step simulation](PA194BSegment.lean) replaces each primary step
by one, three, or five PA194B steps. The arithmetic proof uses arbitrary tape
halves in models of `IΣ₁`. The [halting comparison](PA194BHalting.lean) uses
`Σ₁` induction and the absorbing PA194B halt at model-valued run lengths.
The [native transfer](../PA194VariantNative.lean) composes the resulting
nonhalting equivalence with the primary iPRA theorem.

Run the staged replay from the repository root with fresh output directories.

```sh
pa=Computability/BusyBeaver/Research/PA/verification
literal=/dev/shm/pa194-primary-for-b
bash "$pa/pa194/ipra/native-endpoint/check-literal.sh" "$PWD" "$literal"
bash "$pa/pa194/ipra/variants/pa194b/check.sh" "$literal" /dev/shm/pa194b-replay
```

The replay verifies the table and label hashes, regenerates the Lean row
data from the delivered files, and builds the relative transfer, packed-run
bridge, shared stuttering proof, and PA194B modules. It retains the checked
primary literal stage and its prebuilt dependency closure. The final axiom
report lists `propext`, `Classical.choice`, and `Quot.sound`.
