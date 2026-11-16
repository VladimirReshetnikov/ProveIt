# AX11H consistency equivalence in iPRA

[`PA194AX11HFinal.consistency_iff_literal_nonhalt`](PA194AX11HFinal.lean)
is an unconditional derivation in the repository's standard iPRA theory.
It states that the consistency of PA is equivalent to the nonhalting of
the exact 194-state AX11H table from its blank start. The table has SHA-256
`c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a`.

The [literal proof](README-physical.md) uses the checked 57,922-step
startup and all 3,671 site contracts. The [halt command](README-halt-frame.md)
and the [returning commands](README-shift-frame.md) discharge the source
contracts for the [direct native transfer](README-direct-native.md).
The axiom case uses the [exact scheduler frame](body-proof/README-ax-frame.md)
and the [checked 3,469 body rows](body-rows/README.md).

With the four verified stages available, run the final checker from the
repository root. Each input directory supplies its checked Lean path.

```sh
variant=Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h
bash "$variant/check-final.sh" "$native" "$shift" "$axiom" "$rows" /dev/shm/pa194ax11h-final
```

Lean's axiom audit reports `propext`, `Classical.choice`, and `Quot.sound`.
