# Proof audit

## Scope

The manuscript's universal statements are supported by written mathematical proofs. No proof-assistant certificate is supplied. Finite computational tests are implementation audits, not the logical foundation of the universal theorems.

## Dependency structure

1. Genuine coordinate supports are unchanged by constrained crossover; every supported word is obtained by finite stitching. Empty words are handled separately.
2. For a context-free seed, a finite-state transduction followed by effective Parikh semilinearity produces Presburger support relations.
3. Closure inclusion is exactly implication of genuine support predicates. Finite Boolean combinations admit a Presburger length-existence formula using finitely many witness positions for negative clauses.
4. Regular closure implies finitely many support rows through reachable DFA state subsets. Finitely many Presburger rows give unary ultimately periodic rectangles, from which the bad-coordinate language is regular. Canonical least row representatives decide finiteness and give an infinite progression certificate in the negative case.
5. A one-marker seed contains 0*. Hence any subset of the supported one positions is realizable. Generation g is exactly the set with at most 2^g ones, and frozen-source generation g has at most g+1 ones.
6. A semilinear component with two independent nonnegative periods has arbitrarily large equal-length fibers. Collinear periods normalize effectively to an arithmetic tail plus finite exceptions.
7. On a common length progression, marker sites are affine functions. Selecting sites gives finitely many gap rays. A finite union is regular iff each ray grows in at most one gap, and context-free iff each grows in at most two gaps.
8. The pumping proof for step 7 first chooses a long point off every low-support ray line. Pumping adds a vector supported in at most one/two gaps; infinitely many pumped points force a low-support line through the chosen point, contradiction. This is deliberately a proof for finite unions, not an invalid inference from an included bad sublanguage.
9. Co-occurring distinct interior velocities create three positive gap slopes. The exact-two-marker slice occurs at every generation from one onward, giving immediate non-context-freeness.
10. A support slice determines a clique of compatible, affinely distinct rays. Conversely, generalized CRT and finite crossing avoidance realize every clique cofinally. Finite points are checked at their own lengths.
11. A private prime for each graph nonedge realizes every graph by constant-position rays. Universal-clique padding moves an arbitrary clique threshold to one greater than a power of two, proving the variable-depth coNP result.

## Important boundary cases

- Words in the one-marker generation theorem are binary. Extending its position-only formula to larger alphabets would be false without further restrictions.
- Epsilon is preserved, not introduced by an empty product convention.
- K=0 and K=1 both have depth zero. Empty graphs have clique number zero.
- Genuine supports, not arbitrary unnormalized masks at dead lengths, are required by the necessity half of the global regularity criterion.
- Finite points can change exact maximum support. They cannot change regular/context-free/linear membership because finite changes preserve those classes.
- Identical affine marker functions do not contribute distinct sites, even when their congruence domains differ.
- Isolated crossings of different functions are excluded by a sufficiently large CRT solution, not by deleting graph edges.
- Different interior velocities at incompatible length congruences are harmless; there must be simultaneous availability.
- A ray at velocity zero or one is an endpoint ray, not an interior obstruction.
- Two-marker intersection, plus the finite-union pumping lemma, is essential. A non-context-free subset alone proves nothing about its ambient language.
- General Presburger normalization may expand enormously. Polynomial structural classification is asserted only for the ray input format.
- Depth hardness is for binary ray inputs and a variable threshold, not every fixed depth and not expanded DFA input.
- The implementation computes only ray instances. It does not implement the global CFG decision procedures or formal verification.

## Additional author-side review

The code uses exact integer/rational arithmetic. The prime generator uses integer square roots; floating-point square-root decisions were removed. The CLI validates nonnegative integer coordinates and reports input/output errors. The complete-period test bound exceeds every starting length and every affine crossing, then covers an entire common period. The graph reduction is checked on every labeled simple graph on one through five vertices.
