# Copy-code support for the compact cell

`CompactCellSupport.lean` proves that if the model copy lookup `copyCode k`
is nonzero and `k < 8807`, then `k` is the cast of a natural position in the
concrete low-mask support. The finite part checks the three far positions and
the 49-entry near table. This is useful for proving that an actual cell has
zero digits at forbidden mask positions.

The companion `CompactCellDigitSupported.lean` extends this to **every**
nonzero local digit for a row `a ≠ 1`: the selector, dummy and copy cases
all lie in the support. The row exclusion is essential because selector 1 is
the forbidden position; it is supplied by `CompactWord.tile_ne` on its valid
indices. Tool session `11079` compiled this companion without warnings or
`sorryAx` and with unchanged direct dependency guards. Its axiom report lists
only `propext`, `Classical.choice`, and `Quot.sound`; its separate source,
command, hashes and log are in `observations/digit-attempt01`.

The results do **not** establish the cell's low-mask `NoCarry` fact, the
physical pulse and product conditions,
`PackingInput`, graph zero, or an internal iPRA proof. The assumption
`k < 8807` is what allows the model index to be identified with a standard
natural; the numeral bound is fixed, not a claim about arbitrary nonstandard
bounded ranges.

The first attempt failed on two Lean rewriting steps; its source and compiler
output are retained in `observations/attempt01`. The corrected single-author
build, tool session `48455`, exited 0 without warnings or `sorryAx`, with
unchanged direct dependency and companion guards. Its two axiom reports list
only `propext`, `Classical.choice`, and `Quot.sound`; the command, source and
object hashes, dependency listing and compiler log are in
`observations/attempt02`. This inherits the previously built digit and
concrete-mask providers' package, transitive, dynamic-loading and
between-observation ancestry; it is not a paired replay or complete dependency
closure authentication.
