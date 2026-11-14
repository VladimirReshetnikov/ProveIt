# Finite codes for the modeled PA194 AX effect

`PA194MachineAXCode.lean` constructs explicit finite candidate-PRA codes for
the modeled AX command's guarded top and its complete triangular-Cantor stack
update. The codes are parameterized by arbitrary finite-code expressions for
the input registers. `axTop_model` and `axStack_model` identify their results
with the `axTop` and `axStack` functions from the model-level store invariant
in every candidate-PRA model, including nonstandard inputs. `axCode_preserves`
then proves that applying these coded effects preserves `SoundStore` when the
model's arithmetic reduct also satisfies IΣ₁.

The separate [standard binding](../pa194-machine-ax-standard/README.md) proves
that these finite codes match the PA194 AX command on ordinary natural-number
inputs. The model equations do not connect them to a model scheduler or
physical controller trace. They therefore do not prove machine/calculus
calibration, an internal PA interpretation, or a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-machine-ax-code/check.sh
```

The final module was rebuilt against the freshly checked model-store module
and previously checked prerequisite overlays. A full nested replay of this
wrapper has not yet been completed. Its printed axiom dependencies contain no
`sorryAx`.

An independent ordered suffix replay rebuilt the generalized AX and SHIFT/MP
code modules against a separately checked model-store object and retained deeper
prerequisite overlays. It passed without `sorryAx`; this was not a full nested
replay.
