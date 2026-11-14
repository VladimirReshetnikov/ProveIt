# PA194 increment: marked-cell and carry-file composition

`PA194IncrementFront.lean` composes the marked selected-cell phase in
`SELECTED-CELL.md` with the fixed-arity carry-file phase in `CARRY-FILE.md`.
Starting at dense state 2 with a marked first register, any fixed number of
regular register blocks, and an arbitrary numeric suffix, the literal PA194
run consumes the selected block and carries across all remaining blocks.
It reaches dense state 1 with the exact transformed left tape and preserved
suffix.

The total clock is the selected-register time plus the explicit PR carry
clock; the resulting left tape is computed by an explicit PR code. The
number of blocks is fixed standard syntax, while all register values and
tape halves may be nonstandard elements of any candidate classical PRA
model. `PA194IncrementFrontSentence.lean` expresses the composed equality as
a universally closed PR-code formula and derives it in native iPRA for each
fixed arity.

This is the front portion of an increment operation, not a complete source
instruction. The prefix before the selected register, append-spare and return
phases, and the final source-frame correspondence still need proofs. No
machine-consistency direction is established here.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-increment-front.sh
```

The checker regenerates the pinned PA194 table, rebuilds the marked-file,
carry-file, and physical-run dependencies, checks selected source and
overlay object hashes, and rejects `sorryAx`. Other transitive prebuilt
overlay objects are assumed to correspond to their recorded sources; the
entire foundation and iPRA chain is not rebuilt by this replay.
