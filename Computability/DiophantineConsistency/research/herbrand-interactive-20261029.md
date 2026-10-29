# Interactive Herbrand extraction for the candidate universal theory

`HerbrandInteractive.separated_interactive` constructs, from an actual
candidate universal-theory proof of the relevant existential/universal
sentence with a universal-prefix matrix, an actual proof of a finite staged
disjunction. Parameters are reserved below the matrix's free-variable bound;
each candidate term uses only parameters and earlier challenges, and each
stage's matrix uses no later challenge. The proof uses valuation compactness,
a term-generated submodel, and first-order completeness in the classical Lean
metatheory; it is not an effective proof transformer.

The author build and an independent replay against the independently checked
92-module provider matched all five source, object and complete-log hashes.
The [replay packet](../reviews/herbrand-interactive-author-replay/manifest.json)
authenticates its local parent sources and objects; Foundation and Mathlib
remain inherited boundaries.

A later upstream merge changed `PRAAddOne`, `PRASubReconstruct`,
`PRABoundedSearchInvariant`, and `PRABoundedSearchMinimal`, which are in the
extractors' transitive import graph. The recorded replays cover the preceding
source snapshot and must be refreshed before claiming current-source coverage.

`HerbrandInteractiveTriple.separated_interactive` extends the construction to
three separate challenges per round, reserving distinct indices and proving
that candidate terms use only parameters and earlier rounds. Its author and
independent builds match all three source, object and complete-log hashes;
the independent replay is `/tmp/herbrand-interactive-triple-independent-xk8q_fea`.
Both results produce proofs in the candidate universal theory. Neither
eliminates the disjunction, translates arbitrary Σ₁ induction, or establishes
PRA conservation.

The three-challenge extractor still has only one outer witness per round. The
intended Ferreira normal form has four outer witnesses; applying it needs a
verified four-witness generalization or a pairing and decoding reduction. Its
inner existential witness may also depend on the three challenge variables,
which must be preserved by the prenex adapter.

For the separate pure-existential route, `HerbrandPackedTriple` applies the
coded counterexample-defeat theorem to finite triple extraction, packing all
occurring parameters and producing an actual candidate-PRA disjunction.
`PRAFiniteTripleChoice` turns a provably Boolean coded finite disjunction into
three coordinated primitive-recursive choice functions and a proof of their
joint predicate instance. Both focused author and independent replays match.
These results do not yet translate the staged interactive disjunction into the
selector's input or perform successive disjunct elimination.
