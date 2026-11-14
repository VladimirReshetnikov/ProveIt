# PA194 complete physical increment on a first marked register

`PA194IncrementReturn.lean` proves the complete physical arithmetic-box
contract for a **first** marked register. Start the literal PA194 machine in
dense state 2, with left half `l` and right half containing the marked
register of value `v`, a fixed standard number of regular register blocks,
and a zero suffix. The run consumes the marked block, carries across the
remaining file, appends a one-valued spare, returns across the remaining
file, and returns across the incremented selected block. It ends in dense
state 7 with left half `half(l)` and right half
`parity(l) + 2*incrementedFile`.

Here `incrementedFile` encodes the selected value `v+1`, the unchanged
remaining register values, and an appended spare of value one. The proof
checks that the spare word `6` is exactly the encoding of a one-valued
register with zero suffix, and that the explicit PR return-file code is the
ordinary file code with that suffix. The exact clock is the selected-and-
carry clock, plus six, plus the carry-file clock again, plus `v+3`; all
components are explicit primitive-recursive codes. The theorem holds in
every candidate classical PRA model for arbitrary, possibly nonstandard,
register values and left tape half.

`PA194IncrementReturnSentence.lean` expresses the contract as a universally
closed PR-code equality with the zero suffix built into its input and proves
it in native iPRA for every fixed remaining-file arity. The proof composes
the marked-cell/carry/append segment, a new return-cell phase, and a new
fixed-arity return-file phase. The relevant all-model value and clock
recurrences are checked separately.

This is a complete arithmetic-box increment **when the marked register is
first**. A general instruction still needs the preceding prefix traversal,
its matching return, and the binary reader/source-control frame. Neither
machine-consistency direction follows from this local result.

Replay with the documented dependency overlays:

```sh
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-increment-return.sh
```

The checker regenerates the pinned PA194 table, rebuilds the front, tail,
and return physical-run dependencies, checks selected source and overlay
object hashes, and rejects `sorryAx`. Other transitive prebuilt overlay
objects are assumed to correspond to their recorded sources; the entire
foundation and iPRA chain is not rebuilt by this replay.
