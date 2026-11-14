# Source equality symmetry and transitivity in the PAeq fixed theory

In every arithmetic model satisfying IΣ₁, `symm_translation` and
`trans_translation` identify the actual numeric translations of Foundation's
standard arithmetic equality symmetry and transitivity axioms with the quotes
of the corresponding closed PAeq fixed formulas. The source sentences are
proved members of PeanoMinus. `symm_witness` and `trans_witness` explicitly
construct one-node internal LK proofs of those translations in the Δ₁ finite
target theory.

These are two standard finite source-axiom cases. They do not establish all
PeanoMinus axiom instances, the arbitrary internal induction-schema supplier,
or the connection between PAeq target proofs and the PA194 machine.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-equality-source/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
