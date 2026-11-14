# Target leaf formula constructors

`PA194TargetLeaves.lean` gives fixed finite candidate-PRA codes for the target
formula constructors `head2`–`head6`, `rho8`, and the diagonal formula. It also
constructs the target membership and equality formulas. The accompanying
`*_model` theorems establish their displayed equations in every candidate-PRA
model, including nonstandard inputs, using the triangular pairing code from
`pa194-target-head1` rather than Foundation's pairing.

These theorems specify formula *generation*. In particular, the module does
not prove the `rho8` guard, a target proof-history checker, a connection to
standard target derivations, or a machine/calculus equivalence. The names and
formula shapes follow `reverse-cert-stack/CertificateStack.lean`; the exact
standard-model equalities and the remaining rule and proof-history correctness
are separate obligations.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-leaves/check.sh
```

The final module was rebuilt against previously checked prerequisite objects;
a fresh full nested replay of this new wrapper has not yet been completed.
The final printed axiom dependencies contain no `sorryAx`.
