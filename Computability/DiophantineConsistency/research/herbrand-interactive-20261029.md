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
source snapshot. A subsequent 68-module candidate-provider refresh and a
21-module extraction/selection refresh have now each passed author and
independent replays with matching source, object and full-log hashes.
Foundation and Mathlib remain inherited boundaries.
A later merge changed the contextual witness and selection modules as well as
bounded-search prerequisites. The recorded replays are for the preceding
snapshot. The affected 62-module candidate graph and reordered 21-module
extraction/selection chain have since passed author and independent replays
with matching source, object and full-log hashes. Pending upstream changes to
Herbrand sources must be audited after the next merge.

`HerbrandInteractiveTriple.separated_interactive` extends the construction to
three separate challenges per round, reserving distinct indices and proving
that candidate terms use only parameters and earlier rounds. Its author and
independent builds match all three source, object and complete-log hashes;
the independent replay is `/tmp/herbrand-interactive-triple-independent-xk8q_fea`.
Both results produce proofs in the candidate universal theory. Neither
eliminates the disjunction, translates arbitrary Σ₁ induction, or establishes
PRA conservation.

The three-challenge extractor above has one outer witness per round. The
intended Ferreira normal form has four outer witnesses, and its inner
existential witness may also depend on the three challenge variables.

`HerbrandInteractiveFourTriple` now supplies the unpaired four-witness,
three-challenge staged extraction, and `HerbrandFourTriplePrenexAdapter`
preserves an inner existential matrix depending on all challenges. The
contextual extraction and selection clients preserve an existential side
while choosing a primitive-recursive witness. A 21-module author build and
two isolated replays matched all source, object and full-log hashes against
the checked provider snapshot. Construction of the induction-derived premise
and successive stage elimination remain open.

For the separate pure-existential route, `HerbrandPackedTriple` applies the
coded counterexample-defeat theorem to finite triple extraction, packing all
occurring parameters and producing an actual candidate-PRA disjunction.
`PRAFiniteTripleChoice` turns a provably Boolean coded finite disjunction into
three coordinated primitive-recursive choice functions and a proof of their
joint predicate instance. Both focused author and independent replays match.
The [coded-stage chain](../reviews/pra-coded-stage-current-author-replay/README.md)
now connects contextual selection, challenge-variable permutation, the coded
induction counterexample and retained-side stability to remove every finite
stage. `PRAFourWitnessCodedGoal.PRA_proves_goal` consequently derives an
actual candidate-PRA proof of the open existential goal from the specific
four-witness universal-theory premise in its statement. The 32-module author
build and two independent replays match source, object and complete-log
hashes. Deriving that premise from an arbitrary induction proof, handling
multiple induction instances, and comparison with standard PRA remain open.

After the 32-module replay, an upstream merge refactored finite and interactive
Herbrand extraction, contextual tree witness/selection, and valuation
compactness. The coded-stage proof covers the preceding snapshot; the affected
chain has since passed a 45-module author rebuild and two independent replays
with matching source, object and full-log hashes. This also checks a U-theory
bridge for one closed coded induction axiom with no external predicate
parameters. Arbitrary and multiple induction instances remain open.

`PRAFoundationOneInduction.PRA_proves_goal_of_succInd` lifts the result to a
candidate-PRA proof using one actual Foundation successor-induction instance
for `codedSigma pred`, where `pred : Code 3`. Its author and independent
replays match source, object and full-log hashes. It does not cover external
predicate parameters or multiple induction instances.
