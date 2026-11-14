# Finite codes for modeled PA194 shift and MP effects

`PA194MachineShiftMPCode.lean` gives finite candidate-PRA codes for the
modeled source SHIFT and MP command effects. `shiftHalt_correct` proves that
the SHIFT halt bit is one exactly when top + cache = 1. `shift_preserves`
proves that the modeled normal SHIFT update preserves `SoundStore` using the
certified machine-Cantor projections. `mpTop_model`, `mpStack_model`, and
`mp_preserves` establish the modeled MP branch selection, resulting top and
stack, and invariant preservation in both branches. The halt-bit and MP
branch equations hold in every candidate-PRA model; the invariant-preservation
theorems additionally require IΣ₁ on the arithmetic reduct. Both scopes
include nonstandard register values.

The separate [standard binding](../pa194-machine-shift-mp-standard/README.md)
proves that these codes reproduce the PA194 SHIFT and MP commands on ordinary
natural-number inputs. The model equations do not connect them to a model
scheduler or physical controller trace. They therefore do not establish
machine/calculus calibration, an internal PA interpretation, or a
PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-machine-shift-mp-code/check.sh
```

The final module was rebuilt against the freshly checked AX-code module and
previously checked prerequisite overlays. A full nested replay of this wrapper
has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.

An independent ordered suffix replay rebuilt the generalized AX and SHIFT/MP
code modules against a separately checked model-store object and retained deeper
prerequisite overlays. It passed without `sorryAx`; this was not a full nested
replay.
