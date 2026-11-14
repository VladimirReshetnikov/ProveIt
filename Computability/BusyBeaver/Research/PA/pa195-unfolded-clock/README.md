# PA195 bounded clock and unfolded parent

`PA195UnfoldedClock.lean` composes the checked 202-to-195 quotient, the
verified dense/native state map, and the full-tape/zipper bridge. It proves
that the standard-natural-number existential interpretation of the selected
`PA195Bounded.boundedCode` halts exactly when the unfolded 202-control
parent machine halts on its blank tape.

This is a standard finite-run theorem. The selected code's behavior in
nonstandard models and any PRA/iPRA consistency implication remain separate
proof obligations.

To check from the repository root, set `IPRA_LEAN_OVERLAY` and
`IPRA_FOUNDATION_OVERLAY` to the matching audited Lean object directories and
run:

```sh
Computability/BusyBeaver/Research/PA/pa195-unfolded-clock/check.sh
```

The check regenerates the hash-pinned literal table, rebuilds all dependencies
in a private temporary directory, and rejects `sorryAx` in the reported final
theorem dependencies.
