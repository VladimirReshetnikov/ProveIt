# Constructive PAeq natural-deduction interface

This adapts the repository's checked natural-deduction interface to the PAeq
target language. Its proof values are actual current-Foundation LK derivations;
it includes implication, conjunction, disjunction, and quantifier rules.
`singleTheoryProof` closes a derivation under one standard sentence assumption
when that sentence belongs to the target theory, producing a Foundation
`T.Proof` object.

This supplies proof-building infrastructure. It does not itself prove a new
source PA axiom, establish an induction-schema supplier, or connect the target
proofs with the literal PA194 machine.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-nd/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
