# Exact norm sharing after position-zero normalization

For every commutative ring and every t,s,a,b,

```
(t^2-s(a+b))^2-4s^2ab = (t^2+s(a-b))^2-4sat^2.    (1)
```

Both sides have the same complete six-term expansion

```
t^4 - 2sat^2 - 2sbt^2 + s^2a^2 - 2s^2ab + s^2b^2.
```

The right side shares t² with its final cross term. Its literal schedule
uses one fewer multiplication in the three circuits below. This is an
identity of the entire polynomial, not merely of its zero set or of
values at sampled inputs.

The incoming parents are the three nine-positive circuits in
`ConZFC_Constructive_Reductions_2026-10-23.zip`, whole SHA256
`37e6f0e8d46fec88df60eab7d4c4b5106fc321be1736763d5def910b8d0619e0`.
Their ordinary position-zero proof, exact degree certificates, source
bindings and full fixed payloads were independently reviewed in
`reviews/constructive-nine-peer.md`. This candidate introduces no change
to their source, layout, masks, rank, majorants, variable domain or
native/refutation interpretation.

For each child the certificate names the four actual parent registers
substituted for t,s,a,b in (1), and maps every retained parent register to
its new register. The independent checker expands both *complete* norm
tails with those four formal atoms and proves (1) over the integers.
For every retained node it checks the complete literal node record,
including mapped operands and leaf names/values. Closure of the mapped
prefix and the original topological ordering prove equality at each
mapped register by induction. Every child node belongs either to this
proved prefix or to the proved norm tail. Consequently its output is
identically equal to the entire parent polynomial after substitution.

This also transfers the accepted parent's exact degree, including its
cancellation-resolved leading-term argument. We do not replace it by the
larger syntactic degree bound of the newly emitted arithmetic DAG. A
literal traversal proves strict topology, complete liveness, use of all
nine inputs and the counted binary-operation totals. Integer literals
and fixed leaves do not count as binary operations; each add, sub or mul
does count, including squaring and multiplication by a constant.

The fixed bindings are preserved whole. For each of original31 and
compact54-sharp, the checker decompresses and compares *all four entire*
native port byte strings to the earlier reviewed tuple. It then evaluates
every parent coefficient recipe using those actual integers, and compares
each resulting signed integer to its complete archived fixed payload.
The base and threshold scales are also compared exactly to their specified
powers of two. Neither a modular checksum nor the compressed length is
used as a substitute for equality of the fixed integers. MF_source is
the already shifted source port in both whole tuples.

All payloads and inherited proofs are read directly from the authenticated
incoming ZIP. The new sibling therefore need not copy the other arrival
components or its large fixed streams. `FIXED_BINDINGS.json` records all
relevant decoded sizes and hashes; `SOURCE_PINS.json` pins the parent
graphs, required proof members and the preceding ordinary review.

The exact transformations preserve the parent positive zero sets in both
directions, with the same nine coordinates. Thus the previously reviewed
ordinary source/refutation implications apply unchanged. They do not
establish Con(ZFC), assert absence of zeros, certify global optimality or
supply a new Lean/internal-object-ZFC derivation. Lean remains paused.

The actual-fixed-value modular assignments are only diagnostics. The
six-term identity and every-node correspondence establish the unbounded
algebraic proof. Mutation controls change the final subtraction orientation
without changing its operation counts or liveness, change a retained fixed
leaf, and corrupt the cut correspondence; each must be rejected.
