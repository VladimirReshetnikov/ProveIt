# Lean-checked 79-row coordinate identity

`TenPositive79Mask.coordinate_identity` proves in Lean over every commutative
ring that the 79-row output at `v` equals the old 80-row graph output at
`oldVal p v`, whose third coordinate is `q − F − C` with `q = beta*J+1`.
The proof factors both graphs through the same core and proves only the small
identities for `C` and `G`; it does not expand the degree-750 polynomial.

The accepted guarded author check is `observations/attempt02/`, producing
`/tmp/mask79-ring-92upnp8s/MaskCoordinate79.olean`, SHA-256
`7fac254b7efc456af7f4aa03ac2d1fa80c23c18faac88ccfd46914b3d07184f6`.
The printed theorem's Lean metatheory axioms are `[propext, Quot.sound]`, with
no `sorryAx`. Attempt01 elaborated the theorem but was rejected for an unused
local binding; it is retained. Source SHA-256 is
`d017edeccda26a8c605dd0da90d99ea599b5bcb47d32b19f977818ab689d4b9d`;
runner SHA-256 is
`e05667289dc60c539db8938fe659c85105a7bff8eb26448ccc8e3caf5556ae65`.
The runner pins the selected direct graph object and samples resources;
project-transitive, package, dynamic and source/object ancestry are inherited.

Separately, `check-rows.py` externally compares all 79 Lean rows, ten
variable slots, four ports and the output with the pinned candidate JSON;
`rows-check.stdout` captures PASS. It is not a Lean file-parsing theorem.
Most importantly, the ring identity does not establish positive-witness
equivalence: the reverse map needs `F+C<q` to make `q−F−C` positive. That
guard is unproved for arbitrary positive 79-graph zeros, so no 79-operation
consistency or iPRA endpoint is claimed.
