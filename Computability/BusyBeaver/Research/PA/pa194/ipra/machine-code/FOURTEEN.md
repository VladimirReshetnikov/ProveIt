# PA194 connected scans through state 15

This extends `THIRTEEN-EXIT.md` by one literal transition. Dense state 14
reads zero, writes one, moves left, and enters dense state 15. The separate
open-induction lemma `PA194ZerosEven.modelZerosEven` establishes in every
candidate classical PRA model that `zeros(m,2*x)` is even, so the proof
needs no additional parity hypothesis on the scanned lengths or tape halves.

Starting in state 12 with left half `l` and right half
`zeros(n, 2*ones(m,2*r)+1)`, let `z = zeros(m, 2*zeros(n,l))`. After
exactly `(((n+1)+m)+1)+1` physical steps, the machine is in state 15 with
left half `half(half(z))` and right half `parity(half(z)) + 2 + 8*r`.
The result covers arbitrary elements of candidate PRA models, including
nonstandard lengths.

`PA194FourteenSentence.lean` proves the corresponding universally closed
primitive-recursive-code equality in candidate classical PRA and transfers
it to native iPRA. This connected physical-machine segment is not a full
source-level instruction simulation or a machine-consistency reduction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-fourteen.sh
```

The checker regenerates the pinned PA194 table, rebuilds the segments and
machine-code dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA
chain is not rebuilt by this replay.
