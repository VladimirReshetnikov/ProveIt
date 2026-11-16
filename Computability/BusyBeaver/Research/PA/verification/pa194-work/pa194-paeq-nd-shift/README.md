# Shift PAeq natural-deduction proofs

`shiftProof` transports a constructive Foundation LK derivation to the
componentwise shifted context and conclusion. `shiftClosed` specializes this
to a conclusion with no free variables, retaining that conclusion unchanged.
These operations let quantified arithmetic certificates carry closed fixed
axioms through eigenvariable introductions.

The module supplies proof-building infrastructure; it does not itself prove
another PA source axiom, the internal induction-schema supplier, or a machine
equivalence.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-nd-shift/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
