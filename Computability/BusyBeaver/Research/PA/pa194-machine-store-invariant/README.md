# Model-level PA194 command-effect invariant

`PA194MachineStack.lean` defines `TargetStack` using a finite Foundation-vector
trace of the **machine's triangular Cantor stack**, ending at zero. It proves
that this predicate is Σ₁-definable in every candidate-PRA model with IΣ₁
arithmetic, and that the certified finite machine-Cantor pair and projection
codes preserve it under push and pop. The empty-stack case is discharged using
a concrete target proof of zero, obtained from the guarded rho8 leaf.

`SoundStore` requires target provability of the top and cached formula and
`TargetStack` of the work stack. The model-uniform theorems prove preservation
for the displayed mathematical effects of shift, both MP branches, and AX.
The AX result has the numerical guarded oldBundle top and the complete
source-order stack of diagonal, head6–head1, guarded rho8, generalization and
previous top; the rho8 inequality and oldBundle guards are handled in the
proof. These results apply to nonstandard model values.

The definitions mirror the separately checked standard PA194 source command
effects. This package does **not** prove that the actual PA194 controller's
encoded execution realizes these model-level effects, nor does it establish a
scheduler invariant over an internal machine trace or identify target
provability with Foundation PA provability. Those are remaining machine
calibration and arithmetic interpretation obligations; this package does not
prove a PA194/Con(PA) implication.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-machine-store-invariant/check.sh
```

The final module was rebuilt against the freshly checked triangular projection
and target-line objects with previously checked deeper prerequisites. A full
nested replay of this wrapper has not yet been completed. Its printed axiom
dependencies contain no `sorryAx`.
