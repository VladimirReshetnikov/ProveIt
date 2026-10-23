# Independent review of exact Q42 projections

Both projections preserve the integer solution set by an explicit bijection, not just a rational implication. Each deleted row has coefficient +1 or −1 in its eliminated coordinate. Solving it gives an integer polynomial in other coordinates. The dependency graphs are acyclic; after resolving dependencies, every reconstruction expression uses only retained coordinates and the unchanged fixed coefficient ports. Projection and these reconstructions are mutually inverse on zero sets. Thus no denominator, sign, divisibility or nonzero-branch hypothesis is introduced.

The independently parsed source rows and emitted reconstruction maps were checked symbolically without importing the builder. For every eliminated variable, its actual parent residual was checked for unit coefficient; its dependency graph was reconstructed independently. Substitution makes every deleted residual identically zero and gives exactly every emitted retained residual, in order. All retained unknowns remain live, and the fixed tuple/binding agrees literally with Q42.

Results:

- sextic36: 36 unrestricted integers, 21 residuals of degree at most3, exact sum-of-squares degree6, 435 symbolic expanded terms. The coefficient of I^4*g^2 is exactly1, with no additional fixed-port contributions, so specialization cannot remove that leading term.
- octic32: 32 unrestricted integers, 17 residuals of degree at most4, exact sum-of-squares degree8, 395 symbolic expanded terms. The coefficient of I^4*V^4 is exactly1, again without fixed-port contributions.

An independent symbolic expansion agrees term-for-term with each emitted expanded JSON. Fresh-copy normal and optimized builder runs pass and regenerate both literal and expanded packets byte-identically. REVIEW.json records exact artifact hashes, counts, leading monomials and independently established dependency orders; check.py reproduces this audit.

PROJECTIONS.md correctly states the generic integer projection lemma and the concrete substitutions. These are degree/variable tradeoffs derived from the corrected Q42 theorem; they are not smaller quartics or new imported number theory. Their logical equivalence inherits Q42's ordinary mathematical proof and explicit compiler/Pell dependencies. No new Lean/Rocq certificate or global minimality is asserted.
