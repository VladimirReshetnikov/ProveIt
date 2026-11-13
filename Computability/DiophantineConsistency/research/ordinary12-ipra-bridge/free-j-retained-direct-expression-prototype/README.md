# Generated direct 95-gate expression equals the free-J literal

`FreeJRetainedDirectExpression.retained_eq_literal` is a Lean theorem for
arbitrary `p : Fin 4 → ℤ`: the direct expression `retainedExpression p` in
this source is definitionally equal to `Ordinary12FreeJ.literal p`. The
source spells out the 12 variables, four ports, and 95 ordered `let`-bound
binary operations. It makes no assumption about particular coefficient
values or a model.

`generate.py` generated that exact Lean source from
`con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive12_95_degree70.json`,
whose SHA-256 is
`2348183cb8e366433f668cdcc9d77ca9c7e2d0c55b7b630bda39bd8db7506d22`.
The generator verifies that pin, the exact 12-variable/four-port metadata,
95 rows, output name, operator set, unique names and absence of forward
references. Its actual `python3 -I -B generate.py` run printed
`PASS generated exact 95-gate direct source from pinned JSON`. The generated
Lean file has SHA-256
`6933dac1856e0401bbe71141b8e2f43ed5c499a5ef8b52e20c5def06e55b8215`;
the generator SHA-256 is
`f962c5705139a26f58fd05a1479dd82582e07b97d8fff2db73b6f26bf490d04c`.

The Lean theorem is about that generated Lean expression, **not a formal
parser theorem about the JSON file**. The JSON-to-source generation and
hash check are an external provenance boundary. Nor does it prove that the
separate typed array instruction interpreter in the sibling
`free-j-retained-program-prototype` equals this expression: that prototype's
full interpreter equality failed to complete at its resource bounds. The
new theorem also does not bind the symbolic coefficient values to retained
payload bytes or a displayed PDF, or establish an iPRA proof.

The bounded single-author run `observations/attempt01` exited 0 without
warnings or `sorryAx`. The named Lean metatheory axiom report is exactly
`[propext]`; this is not an object-theory axiom list. Its output object
SHA-256 is
`11963621a2a4f7c2ae39c4d53bfa82ea9814b49994bc15ecd984f0fa6b7dd2c3`.
The exact generated source, dependency and companion guards, compiler log,
terminal receipt and selected provider inventories are retained. The 531
selected seed/halt project overlaps matched at preflight and recorded
inventories and direct guards were unchanged at final checks.

This is an author-only exploratory build, not a matched paired replay or a
complete authentication of inherited transitive, package or dynamic
provider ancestry. Filesystem and resource checks are point-in-time and do
not establish continuous monitoring.
