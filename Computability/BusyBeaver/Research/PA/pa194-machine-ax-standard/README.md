# Standard binding of the finite PA194 AX codes

`PA194MachineAXStandard.lean` proves that the mathematical `axTop` and
`axStack` used by the model-level store invariant exactly match the guarded
top and complete work stack in `PA194CommandTransfer.step` for AX on ordinary
natural-number inputs. The statement retains the complete stack order and
handles both guard outcomes.

`ax_code_command` strengthens this to the finite candidate-PRA codes: for
arbitrary input expressions and natural-number environments, interpreting
`axTopCode` and `axStackCode` gives the exact AX command result. The imported
model equations for these codes hold in every candidate-PRA model, but this
package compares the effect to the existing command implementation only in
the standard natural numbers. It does not establish an internal scheduler or
physical-controller trace, identify the independent target proof encoding
with PA provability, or prove either PA194 consistency implication.

From the repository root, run with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-machine-ax-standard/check.sh
```

The module passed a fresh suffix check against the separately rebuilt model
AX code and retained prerequisite overlays, without `sorryAx`. The full
nested replay has not yet been completed.
