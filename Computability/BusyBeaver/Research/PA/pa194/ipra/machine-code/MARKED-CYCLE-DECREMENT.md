# PA194 genuine marking cycle to decrement

`PA194MarkedCycleDecrement.markerToDecrement` composes the actual non-first
marker operation, its return, the `k=1` header-controller path, the
at-least-five physical one-run cycle, and the marked decrement box. It applies
to all eight non-first physical marker positions, in every candidate PRA
model. Register values, tape tails, and scan lengths can be nonstandard.
The first returned prefix register has value `m+6`, where `m` may be any
model value. Thus the residual run at state 42 is `m+1`, and after two steps
state 1 scans its remaining `m` ones before reaching the marked file. Both
the selected register's zero and positive cases are covered, with exact tape
halves and a model-valued PR clock.

The delimiter must encode the selected register and a following nonempty
physical file as stated in the theorem. This following file can include the
spare block. The header `k=1` condition and all exact starting tape halves
are assumptions; no theorem here establishes source-program reachability or
identifies the controller choice with a source instruction.

`PA194ReturnedDecrement.returnedMarkedFile` proves the exact match between the
marker-return output and the decrement box: its remaining file has the
regular blocks `e[1]` through `e[idx]`, followed by the *same selected marked
block* and the unchanged following file. `returnedUpdatedFile` proves the
box output replaces that marked block by an ordinary block while preserving
those regular blocks and the following file. The zero case writes zero; the
positive case writes the predecessor. The output has the tape halves stated
in `markerToDecrement`, including the residual one-run on the left.

**The preceding first block `e[0]` is consumed by this physical controller
path.** The output theorem leaves its residual `m` ones on the left tape; it
does not prove that the original `m+6` block is restored or that the output
is a source frame. The separate [positive-return theorem](MARKER-POSITIVE-RETURN.md)
continues this path and proves that the returned block has value `m`. In particular this is not a complete source-instruction
simulation or either PA consistency direction. When the residual at state 42
is zero (first block value five), the machine instead reaches state 84; that
separate branch is in `STATE-42-BOUNDARY.md` and is not covered by this
decrement theorem.

Replay from the repository root using pinned overlays:

```sh
TMPDIR=/dev/shm IPRA_LEAN_OVERLAY=/path/to/ipra/lib \
  IPRA_FOUNDATION_OVERLAY=/path/to/foundation/lib \
  bash Computability/BusyBeaver/Research/PA/pa194/ipra/machine-code/check-marked-cycle-decrement.sh
```

The checker rebuilds the marker-cycle and decrement prerequisite chains in
separate temporary directories, then builds the state-42 and new composition
modules and rejects `sorryAx` in reported theorem dependencies.

An independent suffix replay rebuilt the two new modules in a fresh tmpfs
overlay against separately checked state-42, marker-cycle, and preserved
decrement prerequisites, with no `sorryAx` in their reported dependencies.
The complete nested replay is running separately.
