# Numerical target truth certificate

`PA194TargetTruth.lean` proves a concrete one-line target proof of numerical
formula `0` in every candidate-PRA model whose arithmetic reduct satisfies
IΣ₁. The line is the restricted rho8 axiom with all four parameters zero;
its guard holds and its output is `0`. The certificate uses the independently
chosen Foundation pair and target proof-history encoding, not the upstream
PA196 certificate encoding.

`verum_node_target` combines this exact target proof with the checked rule-tag
inversion: for any internal current-Foundation relational-source derivation
with tag 1, its decoded context is a valid formula set containing `qqVerum`,
and the numerical target checker accepts the displayed proof of `0`.
`standard_truth_binding` separately checks that the existing standard source
formula translation maps `.verum` to `0`. The standard binding is not a
nonstandard translation of arbitrary contexts or entire sequents. The encoded
context-membership-to-target-context transformer and the whole proof compiler
remain open.

Run from the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-truth/check.sh
```

The final module passed a fresh suffix check against the checked verum-node
and target-proof objects plus retained prerequisite overlays. Its printed
axioms contain no `sorryAx`. The full nested replay remains pending.

An independent suffix replay rebuilt the truth-certificate module against the
separately checked verum-node and scheduler prerequisites, with retained deeper
overlays. It passed without `sorryAx`; this was not a full nested replay.
