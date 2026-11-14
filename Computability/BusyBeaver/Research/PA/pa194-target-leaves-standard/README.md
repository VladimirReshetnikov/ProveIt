# Standard target leaf bindings

`PA194TargetLeavesStandard.lean` proves that evaluating the finite codes from
`../pa194-target-leaves` on standard natural-number arguments gives exactly
`PA196.Commands.Code.head2`–`head6`, `rho8`, and
`PA194AXSymbolic.diagonal`. It explicitly reconciles candidate-PRA arithmetic
and triangular pairing with their standard natural-number meanings. The
`head*_derivation`, `rho8_derivation`, and `diagonal_derivation` definitions
then produce corresponding derivations in the existing PA194 numerical
calculus; `rho8_derivation` explicitly requires its guard `u ≤ a`.

This is a standard-input binding, not an internal derivation construction for
nonstandard model inputs. It does not prove a full target proof-history
checker, verify the gate rule, or establish a machine/calculus equivalence.
The formula constructors themselves have separately proved model-uniform
semantics; this package does not transfer standard derivations to arbitrary
models.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-leaves-standard/check.sh
```

The final module was rebuilt against previously checked prerequisite objects.
A fresh full nested replay of this wrapper has not yet been completed. The
printed axiom dependencies contain no `sorryAx`.
