# Finite codes for the modeled PA194 AX effect

`PA194MachineAXCode.lean` constructs explicit finite candidate-PRA codes for
the modeled AX command's guarded top and its complete triangular-Cantor stack
update. The codes are parameterized by arbitrary finite-code expressions for
the input registers. `axTop_model` and `axStack_model` identify their results
with the `axTop` and `axStack` functions from the model-level store invariant
in every candidate-PRA model whose arithmetic reduct satisfies IΣ₁, including
nonstandard inputs. `axCode_preserves` then proves that applying these coded
effects preserves `SoundStore`.

The modeled functions were transcribed from the standard PA194 source AX
implementation. This package does **not** yet prove equality of these codes
with that standard command implementation, and does **not** connect them to
any model scheduler or physical controller trace. It therefore does not prove
machine/calculus calibration, an internal PA interpretation, or a
PA194/Con(PA) implication.

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
