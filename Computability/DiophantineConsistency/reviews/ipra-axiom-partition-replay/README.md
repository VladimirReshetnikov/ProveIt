# Partition of remaining native iPRA obligations

`axiom_images_from_remaining` combines the already established native
induction GG transfer with three explicit premises: GG transfer for equality,
primitive-recursive defining equations, and basic axioms.
`mapped_noZero_comparison_from_remaining` uses this to state the equation
comparison with those premises, the classical comparison proof, and the
consistency-target bridge all visible. No outstanding premise is asserted.
External transitive ancestry is inherited. Run
`python3 Computability/DiophantineConsistency/reviews/ipra-axiom-partition-replay/replay.py`.

The initial author attempt failed before compilation because a documentation
comment preceded a later import. Its source, log and state are preserved under
`failed-author/`; the successor moves the comment after both imports.

Successor author PASS; both axiom reports were separately parsed and
contain only the standard Lean trio.

Independent peer PASS; both source/object/full-log rows match author,
and both axiom reports contain only the standard Lean trio.
