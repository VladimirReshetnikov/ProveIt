# Can equality operands be produced directly in register3?

Yes for three of the four comparisons, if equality symmetry is used to
select the transient rather than persistent-cache operand. No explicit
R5-to-R3 transfer is needed in those three regions.

Let E(x,y) be the original destructive equality macro with registers5 and6
renamed to x and y respectively. For arbitrary natural operands it clears
both, preserves other registers, and returns normally iff they were equal,
otherwise one break. Renaming and exchanging the operands preserve this
contract. Register3 is zero at the following producers; register6 is also
zero on their external entries. The exact guard-refined incoming edges are
in EQUALITY_PRODUCER_LIVENESS.json.

## Three identical recolored equalities

Use the common E(3,5) macro for these regions:

1. Second AX gate, comparing retained selectorc with additivea:
   change site4580 fromCI6 toCI3. The existing transfer4579..4581 now drains
   retainedc fromR7 intoR3. The following unchanged transfer4582..4584 drains
   a fromR4 intoR5. Run E(3,5) at4585..4594. It leavesR3,R5,R6 all zero,
   with exactly the original equality exit and consequent top-clear action.
2. NIP, testing cacheh=1:
   change site4598 fromCI6 toCI3 and use E(3,5) at4599..4608. R3 becomes1,
   R5 still holds the persistent cache, andR6 stays0. Equality clearsR3/R5
   and reaches halt precisely whenh=1, including the calibration's
   inconsistency direction. Otherwise the unchanged pop runs from exactly
   the old register state. No cache!=1 premise or special NIP grammar is used.
3. MP, comparing the just-computed implication against cacheh:
   change site4706 fromCI6 toCI3. The existing transfer4705..4707 now clears
   R1 intoR3 rather thanR6. Use E(3,5) at4708..4717. R6 remains0 and the
   equality exit, cache clearing, and all following register values agree
   with the original MP block.

These are local source-level simulations for arbitrary other registers
subject to the stated zero-scratch guards. They do not depend on theorem
soundness or Con(ZFC).

## First AX gate: a real live-range conflict

The first gate comparesb=oldcache+y against selectorc and must retainc for
the second gate. The cache is last restored toR5 at site4124; there is no
R5 access again until the equality starts at4567. The selector is last
restored toR3 at4150; there is noR3 access until its final drain at4563.
Both values are live simultaneously. Register3 cannot simply replace the
cache's destination in this interval without overwriting the selector.

The actual four-leaf producer4563..4566 is

    (D3,(I7,(I6,C3)))

It drainsc fromR3, leaving one copy inR6 for the first test and a second inR7
for the second test. Directly replacing I6 byI3 is invalid: every iteration
then restores the unit just removed fromR3. For any positivec the loop
continues forever while increasingR7. This is an exact obstruction to that
specific direct recoloring, not a lower bound on all producer rewrites.

One could restore the R6 copy back intoR3 with an additional transfer, but
that reintroduces the three leaves the question sought to avoid. Moving the
selector earlier is not a free local rename either: R6/R7 are repeatedly
used by the intervening formula-construction operations. No general
register-allocation impossibility is asserted.

## Concrete mixed proposal and its physical boundary

There is nevertheless a transfer-free mixed source proposal: use E(6,5) at
the first gate, retaining its current producer, and E(3,5) at the other three
gates with the three one-leaf edits above. Equality symmetry makes every
region source-equivalent, and no primitive leaves are added. This removes
all four exact oldE subtrees, but splits their sharing into two shapes.

The important compiler issue is not yet a count: both new equality shapes
place CD5 as a right child, an interface entirely absent from the current
source. The existing source only has left-childCD5. A right-child decrement
cannot be assumed to inherit an unproved engine contract. The resulting
native decoder allocation, possible removal of301, retained helper roles,
complete primitive simulation and blank initialization would all need
separate checking. No allocation, source enumeration or runtime search was
launched for this producer/liveness inspection.

## Followed by one shared-source restoration pilot

A single existing three-leaf transferT(6,3) appended to the firstAX duplicate
restoresc intoR3, clearsR6 and preserves the savedc inR7. All four calls can
then use the sameE(3,5), with only that one extra transfer. The old producer
first clearsR3, so the restoration does not self-replenish its original loop.
At the first equality boundary, both old and new regions clearR3/R5/R6 and
choose the same outward equality exit for all natural operands. The three
other producer retargetings remain as described above.

This exact combined source has209 nodes and4747 leaves. Its default
allocator lacks a right-childCD5 entry. A subsequent explicitly provisional
gate1R45, justified only as the natural candidate counterpart to left0R45,
allows a raw table to be emitted. That table counts223 states, removes no
state, adds303–307 and reports one role-binding discrepancy[[46,63]]. The
gate is not proved. Since the raw price exceeds218, the prescribed search
stop applies: no focused gate proof, full runtime replay or blank run was
attempted. This is not a proof that rightCD5 requires a new state, nor a
lower bound on alternative layouts. See shared_recolored_equality.
