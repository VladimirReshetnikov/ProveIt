# PA194 literal step in arbitrary PRA models

`PA194LiteralStepModel.lean` builds on the finite-control row theorem and
proves that all three explicit configuration-step components agree with the
actual generated `PA194.Literal.transition` row on every working model
control. The proof permits nonstandard tape values and uses the interpreted
parity and half functions for tape updates. The output state is the model
numeral for the literal next-control label. This is a theorem about all models
of the candidate classical PRA; it is not yet an iPRA proof or a
source-register/runtime refinement.

Replay with the same dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-literal-step.sh
```

The checker rebuilds the dependency chain and pinned literal table in a
private directory and rejects `sorryAx`. Its transitive prebuilt overlay
objects are assumed to match their recorded sources; it does not rebuild all
of them.
