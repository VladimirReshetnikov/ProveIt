# Extended target history invariant

This package extends the independently encoded target history interpreter with
all numerical-calculus leaf forms: `head2`–`head6`, guarded `rho8`, guarded
`oldBundle`, and diagonal. It retains the earlier `head1`, modus-ponens and
generalization cases. Tags 3 through 10 select the new forms; their payload is
`pair a (pair b (pair c u))`, with unused fields ignored. Tags outside that
range fall back to the previous interpreter. Its finite codes use Foundation's
pairing for history fields and the machine's triangular pairing inside formula
codes. The two must not be confused.

`extended_sound` proves one-step preservation for every candidate-PRA model
whose arithmetic reduct satisfies IΣ₁. In addition to the earlier head1, MP,
and generalization closure premises, it assumes the eight explicitly stated
`LeafClosure` conditions, including the `rho8` and gate guards. `history_sound`
then proves the invariant by **internal IΣ₁ induction**, and `accepted_sound`
applies it to any model index and accepted formula, including nonstandard
indices. This is a conditional closure theorem: it does not produce a
concrete predicate satisfying the premises, an internal source-proof compiler,
or a machine/calculus calibration.

The current line-vector lookup is total and **does not check vector length**;
a missing line can be read as a valid zero-coded line. The encoding here is a
new independent checker encoding and has not been identified with the upstream
certificate format. Neither the theorem nor the standard leaf bindings
establishes the desired PA194/Con(PA) implication on their own.

Run from the repository root with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-history-extended/check.sh
```

An ordered suffix replay rebuilt the four leaf/guard modules and then the
final module in one fresh overlay, reusing previously checked history and
Foundation prerequisites. A full nested replay of this wrapper has not yet
been completed. The printed axiom dependencies contain no `sorryAx`.
