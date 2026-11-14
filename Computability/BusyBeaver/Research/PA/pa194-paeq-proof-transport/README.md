# Conditional IΣ₁ transport of internal LK derivations

For an arbitrary arithmetic model satisfying IΣ₁ and arbitrary Δ₁ source
arithmetic theory `T` and target PAeq theory `U`, `derivation_transport` maps
every internally valid `T` LK derivation to derivability in `U` of its
translated finite-set sequent. The induction covers all ten source rule
forms, including shift, quantifiers and cut. Theorems `provable_transport`
and `refutation_transport` give the corresponding single-formula and falsum
consequences, also for nonstandard derivations and formula codes.

The explicit premise is that every internal `T` axiom code translates to a
formula provable in `U`. No full-PA model assumption is used by this
conditional transport. The PA-to-PAeq axiom supplier, particularly the
induction schema, is not established here. Nor does the theorem supply a fixed
finite PRA proof-code transformer or a bridge to the literal PA194 machine.
The result adapts the pinned PA196 derivation argument to current Foundation,
generalizes its source theory, and uses the IΣ₁ substitution agreement.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-proof-transport/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
