# Internal formula-code and finite-tuple orders

The merged `CodeOrder` and `TupleOrder` modules supply two concrete building
blocks for the constructible Choice route. They were contributed in
`b5c4b5cdaa` and `b2d43d88bc`; the accompanying `OrderRec` change requires its
append decomposition only on well-ordered inputs. Existing consumers already
supply that premise.

`CodeOrder.code_order` constructs a unique represented well-order whose field
contains every recognized internal formula code. It starts with internal omega
and iterates appending new pairs, using definable ordinal recursion at internal
omega. Its coverage proof uses actual formula-code induction, so it includes
nonstandard codes. Power and Regularity are explicit assumptions in addition
to the base ZF interface. The field also contains other pair-closure elements;
it is not asserted to be exactly the formula-code domain. A literal named
formula defines the order, with its satisfaction theorem.

`TupleOrder.wo_lexN` well-orders function-graph tuples of each internal natural
length over a given internal well-order. The first differing coordinate is
found internally. Leastness uses actual formula induction on internal omega,
Replacement of unique prefixes, and Separation of their last values bounded
by triple Union. No Power or Choice premise is added to this tuple theorem.
Here a well-order means least elements for nonempty represented subsets; it
does not assert external well-foundedness of a nonstandard model.

The [163-unit integration](results/code-tuple-order-integration-verification.json)
freshly checks `OrderRec`, both new modules and the umbrella;159 source-matched
checked units are reused. Twelve axiom reports and six generic callers pass
with only `propext`, `Classical.choice` and `Quot.sound`. This is not a fresh
rebuild of all163 units. The independent full source/API review is preserved
in [the review record](results/code-tuple-order-review.json).

The earlier intake156 review's missing-CodeOrder statement is now historical.
The full constructible order still needs varying-length key packaging, bounded
sets of keys and a definable append construction. In particular,
`InternalWO.wo_pull` requires a set of all relevant keys for each represented
set. Allowing arbitrary witnessing stages gives proper-class many keys even
for one object; keys must use least birth stages or another bounded convention.
The resulting order/selector must belong to the interpreted domain before it
can prove the exact Choice axiom. These remaining steps, finite refutation
transport and internal PA representation are separate from the two checked
orders. No binary table or state count changed.
