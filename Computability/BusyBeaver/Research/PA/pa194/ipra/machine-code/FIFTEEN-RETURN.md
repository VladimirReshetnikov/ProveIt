# PA194 connected return through the state-15 scanner

`PA194FifteenReturn.lean` extends the connected segment in `FOURTEEN.md`
through the previously proved state-15 leftward zero scan. Its parameterized
input supplies one additional one to the state-13 scanner. An all-model
open-induction lemma in `PA194ZerosDouble.lean` establishes
`zeros(m,2*x) = 2*zeros(m,x)`, providing the precise parity and tape shape
needed to connect the scans.

Start in dense state 12 with left half `l` and right half
`zeros(n, 2*ones(m+1,2*r)+1)`. After exactly
`((((n+1)+(m+1))+1)+1)+m` literal physical steps, the machine is in state 15
with left half `zeros(n,l)` and right half `2*zeros(m,1+4*r)`. The theorem
holds for arbitrary elements of each candidate classical PRA model, including
nonstandard lengths and tape halves.

`PA194FifteenReturnSentence.lean` expresses this connected run as a
universally closed equality of explicit primitive-recursive-code terms,
proves it in candidate classical PRA by completeness over equality models,
and transfers it to native iPRA. It remains a local physical-machine
segment: a full source-instruction simulation and both machine-consistency
directions are separate, unproved obligations.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-fifteen-return.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
