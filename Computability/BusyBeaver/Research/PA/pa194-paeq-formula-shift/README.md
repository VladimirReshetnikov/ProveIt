# IΣ₁ PAeq formula shift and single-variable substitution

For every candidate-PRA arithmetic model satisfying IΣ₁, the checked
`formulaCode_shift` commutes with the actual free-variable shift of any
internally valid source formula. The checked `formulaCode_substs1` and
`formulaCode_free` specialize the simultaneous-substitution agreement to one
bound variable and the Foundation free-variable operation. All input codes and
parameters may be nonstandard model elements.

These results adapt the pinned PA196 source to the current Foundation language
and use the IΣ₁ substitution theorem. They do not establish iterated universal
closure, a formula-translation witness bound or finite PRA code, a proof-code
compiler, or either machine/consistency implication.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-formula-shift/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
