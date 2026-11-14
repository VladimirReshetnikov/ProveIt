# Guarded target gate

`PA194TargetGate.lean` constructs finite candidate-PRA codes for the PA194
`oldBundle` formula and its two equality guards. In every candidate-PRA model
whose arithmetic reduct satisfies IΣ₁, `gate_accepts_iff` proves that the
fixed gate checker returns the formula code plus one exactly when `c ≠ a` and
`c ≠ b`; either failed guard returns zero. The model-level formula components
use the target's triangular pairing and apply to nonstandard inputs.

`eval_oldBundle` separately proves that evaluation on standard natural-number
inputs produces exactly `PA196.Commands.Code.oldBundle`.
`oldBundle_derivation` obtains the existing PA194 numerical-calculus gate
constructor with both guard hypotheses explicit. This standard derivation
is not an internal proof object for nonstandard inputs. This package does not
establish a complete target proof-history checker, a machine/calculus
calibration, or a consistency equivalence.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-gate/check.sh
```

The final module was rebuilt against previously checked prerequisite objects.
A fresh full nested replay of this wrapper has not yet been completed. Its
printed axiom dependencies contain no `sorryAx`.
