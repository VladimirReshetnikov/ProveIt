# Construction of PA194C

Run `python3 -B construction/build194C.py` from the package root.
Python 3.10+ and the standard library suffice; assertions must be enabled.
The script reconstructs the accepted PA194 decoder, applies the six
published 195C controller changes, and verifies their composition.

The outputs are in `rebuilt_194C/`. They have 194 working states, 388 rows,
3,649 source sites, and 4,749 primitive branch outcomes. The state allocation
is 134 fixed controls plus 67 readers minus seven simultaneous contextual
folds. All 28 local fold cases and all source contracts are replayed.
The exact 57,922-transition startup is compared against the whole source tape.

`build194.py`, `compiler.py`, `symbolic_runtime.py`, `source/`, `inputs/`,
`tables/`, and the original evidence are inherited PA194 construction inputs.
Their original provenance is retained verbatim in
`INHERITED_PA194_PROVENANCE.json`. The inherited `tables/pa194*.tm` files
are reference machines; the delivered new table is `../machine/pa194C.tm`.
`reference/` contains inherited Lean and literal-table source files, with
original licenses under `licenses/`. This is not a standalone Lean project.

The new builder also reconstructs the published 195C parent, binds its
native table to SHA-256
`8f34d9e5cc2e64ecc49bbc8581dc29b2ac0a84ad9187c4dd8b7597588ef22ea3`,
and compares the complete source instruction graph to the original published
195C instruction list under `../verification/independent/reference_inputs/`.

The construction symbolic executor uses inherited arithmetic-block
contracts. Run `python3 -B verification/independent/check194C.py` from the
package root for the independent literal-tape verification, which derives
four generic list lemmas from the actual transition rows. The report supplies
the separate logical calibration and PA-provability argument. No new compiled
end-to-end proof-assistant theorem is claimed.
