# Construct PAeq proofs from finitely many closed axioms

`listTheoryProof` converts a constructive PAeq natural-deduction derivation
from a finite list of closed sentence assumptions into an actual Foundation
`T.Proof` object, given membership of each sentence in `T`. The construction
uses Foundation LK proof conversion and cut-many; it extends the earlier
one-assumption constructor to the multi-axiom contexts needed by arithmetic
and order proofs.

This infrastructure does not prove any additional source PA axiom or the
arbitrary internal induction-schema supplier, and does not connect PAeq
proofs with the literal PA194 machine.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-paeq-nd-list/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorem's axiom audit contained no `sorryAx`.
