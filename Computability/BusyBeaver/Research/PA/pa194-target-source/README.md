# Conditional target-proof translation into PA

`PA194TargetSource.target_sound` translates any proof in the independent
`TargetProvable` encoding into internal PA provability of its numerical
formula. The theorem holds in every candidate-PRA model whose arithmetic
reduct satisfies IΣ₁, including for nonstandard proof programs. It uses the
checked preservation of the six numbered source-axiom families, rho8, the
diagonal, modus ponens and universal generalization. Its one explicit seed
hypothesis is PA provability of all guarded gate translations.

`target_refutes_PA` uses the checked interpretation of code 1 to turn an
independent target proof of code 1 into an internal PA refutation, under the
same gate hypothesis. `scheduler_halt_refutes_PA` composes this result with the
modeled scheduler's halt endpoint, assuming its store invariant at the
halting state.

These are conditional all-model theorems, not a proof of an iPRA consistency
implication. The guarded gate remains unproved. The `*_of_tail` variants narrow that
hypothesis to internal PA provability of the translated negated separation
tail for fresh labels, using the checked gate reduction. Connecting the
modeled scheduler run to the literal PA194 machine also remains open.
The separate PA-refutation-to-machine-halt direction remains open as well.

From the repository root, run with the matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-target-source/check.sh
```

The final module passed a fresh suffix check using separately rebuilt head1,
head2, head5, diagonal, gate-reduction and scheduler objects and retained
deeper prerequisite overlays, with no `sorryAx`. The complete nested `check.sh` replay also passed with
the pinned audited overlays and no `sorryAx`.
