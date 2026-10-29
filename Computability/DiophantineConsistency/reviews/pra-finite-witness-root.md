# Independent replay: finite primitive-recursive witness selection

For a fixed Boolean-valued primitive-recursive predicate code, a list of
primitive-recursive candidate codes, and candidate-PRA proofs of Boolean range
and the universally closed finite disjunction of their success,
`PRA_exists_listWitness` constructs one fixed primitive-recursive selector code
and proves its universally closed success in candidate PRA. A fallback
candidate is included explicitly, even when the list is empty. This is the
finite-disjunction-to-single-witness step; the theorem does not extract such
a disjunction from an arbitrary Π₂ proof or establish conservation.

Two separate builds against the independent equivalence provider
`/tmp/pra-universal-independent-m5hxtn5a/lib` passed all four modules with
matching source, object and complete-log hashes. The driver verifies 44 parent
source and object hashes and the frozen witness sources. [Independent driver,
state and logs](pra-finite-witness-root-replay/) and the [author packet](pra-finite-witness-author-replay/)
are preserved. Historical failed and warning probes are evidence only, not
compiled proof inputs. Foundation, Mathlib and unchanged local objects remain
inherited cache boundaries.
