# PA194 extended state-15 return

`PA194FifteenExtended.lean` extends `FIFTEEN-RETURN.md` through another
state-15 leftward zero scan, this time of length `n`. From dense state 12
with left half `l` and right half `zeros(n, 2*ones(m+1,2*r)+1)`, after
exactly `(((((n+1)+(m+1))+1)+1)+m)+n` literal steps the machine is in state
15 with left half `l` and right half
`2*zeros(n, zeros(m,1+4*r))`. The formula is valid in every candidate
classical PRA model for arbitrary elements `n`, `m`, `l`, and `r`, including
nonstandard values.

`PA194FifteenExtendedSentence.lean` expresses the result as a universally
closed primitive-recursive-code equality, proves it in candidate classical
PRA by completeness over equality models, and transfers it to native iPRA.
This connected physical-machine segment does not yet prove a full
source-instruction simulation or either direction of the machine-consistency
equivalence.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-fifteen-extended.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
