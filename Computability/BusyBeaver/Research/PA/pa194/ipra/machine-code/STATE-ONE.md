# PA194 state 1 and binary tape arithmetic

`PA194BinaryDouble.lean` uses quantifier-free open induction to prove in every
candidate classical PRA model that `parity(x+x)=0`, `half(x+x)=x`,
`parity((x+x)+1)=1`, and `half((x+x)+1)=x`, for every model element x,
including nonstandard ones. `PA194StateOne.lean` combines these identities
with the pinned transition table: in state 1, a leading one is written as one,
the machine moves right, remains in state 1, and updates the numeric halves
from `(l, 2*r+1)` to `(2*l+1, r)` in every candidate PRA model.

This is one literal transition and an arithmetic building block for unary
register-block simulations. It does not yet prove a whole variable-length
run, a source-register refinement, or a consistency implication.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-state-one.sh
```

The checker regenerates the pinned table, rebuilds the dependency chain in a
private directory, and rejects `sorryAx` in printed theorem dependencies.
Transitive prebuilt overlay objects are assumed to match the recorded sources.
