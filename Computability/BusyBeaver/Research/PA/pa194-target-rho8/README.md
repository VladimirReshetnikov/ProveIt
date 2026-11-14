# Guarded target rho8

`PA194TargetRho8.lean` defines a fixed finite candidate-PRA checker for the
PA194 `rho8` leaf. On every candidate-PRA model whose arithmetic reduct
satisfies IΣ₁, `checkRho8_model` proves that the checker returns zero when
`a < u` and the generated formula plus one otherwise. `rho8_accepts_iff`
therefore proves acceptance exactly when the rule's required guard `u ≤ a`
holds, including for nonstandard model inputs.

The separate `../pa194-target-leaves-standard` package identifies the formula
on standard inputs and constructs an existing numerical-calculus derivation
under this guard. These results do not provide a nonstandard target derivation,
a complete target proof-history checker, or a machine/calculus calibration.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-rho8/check.sh
```

The final module was rebuilt against previously checked prerequisite objects.
A fresh full nested replay of this wrapper has not yet been completed. The
printed axiom dependencies contain no `sorryAx`.
