# PA194 increment: one return-cell phase

`PA194ReturnCell.lean` proves a literal return-cell phase needed after the
append-spare step. Starting at dense state 7 with left half `ones(n,2*l)`
and right half `2*t+1`, after exactly `n+2` physical steps the machine is
again in dense state 7, with left half `half(l)` and right half
`parity(l)+4*ones(n,1+2*t)`. It uses the real state-7 row, the previously
proved state-6 leftward one scanner, and its boundary and exit transitions.
The proof covers zero and successor lengths inside every candidate classical
PRA model, including nonstandard values of `n`, `l`, and `t`.

`PA194OnesCommute.lean` additionally proves by open induction that
`ones(n,2*x+1) = 2*ones(n,x)+1` in every candidate PRA model. This is useful
when relating the physical two-half representation to the left-headed
register frames used in the upstream increment proof.
`PA194ReturnCellSentence.lean` proves the universally closed PR-code
return-cell equality in native iPRA.

This is one return-cell phase, not yet a whole return file or a complete
source instruction. It does not establish either machine-consistency
direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-return-cell.sh
```

The checker regenerates the pinned PA194 table, rebuilds the machine-code
dependencies, checks selected source and overlay object hashes, and rejects
`sorryAx`. Other transitive prebuilt overlay objects are assumed to
correspond to their recorded sources; the entire foundation and iPRA chain
is not rebuilt by this replay.
