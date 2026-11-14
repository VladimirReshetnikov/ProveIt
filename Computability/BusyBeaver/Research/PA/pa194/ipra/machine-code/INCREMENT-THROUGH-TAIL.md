# PA194 increment through the append-spare tail

`PA194IncrementThroughTail.lean` composes the marked selected-cell and
fixed-arity carry-file phases in `INCREMENT-FRONT.md` with the six-step
append-spare phase in `INCREMENT-TAIL.md`. From dense state 2 and a marked
selected register followed by a fixed number of regular register blocks,
with the final tape suffix zero, the literal PA194 run reaches dense state
7. The clock is the selected-and-carry clock plus six; the left tape is
exactly the explicit PR output of the front phase, and the right tape is 13.

The model-level theorem allows arbitrary elements, including nonstandard
register values, in every candidate classical PRA model. The number of
register blocks is fixed standard syntax. The accompanying universally
closed PR-code sentence builds the zero suffix directly into the input and is
proved in native iPRA for each fixed arity.

This is not a complete source increment instruction: it starts at the marked
selected register and ends before the return phases and final source-frame
correspondence. It does not establish either machine-consistency direction.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-increment-through-tail.sh
```

The checker regenerates the pinned PA194 table, rebuilds the front and tail
physical-run dependencies, checks selected source and overlay object hashes,
and rejects `sorryAx`. Other transitive prebuilt overlay objects are assumed
to correspond to their recorded sources; the entire foundation and iPRA chain
is not rebuilt by this replay.
