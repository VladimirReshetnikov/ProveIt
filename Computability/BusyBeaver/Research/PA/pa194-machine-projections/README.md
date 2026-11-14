# Model-uniform PA194 machine Cantor projections

`PA194MachineProjections.lean` uses the bounded arithmetic graphs of the
machine's triangular Cantor projections to choose two fixed finite
candidate-PRA codes. The `fixedFirst_model` and `fixedSecond_model` theorems
identify their interpretations in every candidate-PRA model with the existing
machine Cantor projections. `first_machinePair` and `second_machinePair`
prove that those codes invert the previously certified machine-pairing code,
including on nonstandard model inputs. These are the triangular machine
pairing and projections, not Foundation's separate pairing.

The codes are chosen once by the existing bounded-witness extraction; the
Lean theorems certify their properties but this package does not print their
concrete syntax. The projections are prerequisites for a scheduler stack
invariant. This package does not yet prove that invariant, connect scheduler
execution to numerical proof lines, or establish a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-machine-projections/check.sh
```

The final module was rebuilt against previously checked prerequisite objects.
A full nested replay of this wrapper has not yet been completed. Its printed
axiom dependencies contain no `sorryAx`.
