# Final height-one mathematical audit

The final selection supersedes the interim source338-based numerical endpoints in HEIGHT_ONE_MATHEMATICAL_AUDIT.md. The general proof and fresh independently written checker from that review remain applicable unchanged.

## Frozen results

- compact793:793 unrestricted integer variables,51,982 monomials.
- balanced806:806 unrestricted integer variables,23,719 monomials.
- sparse994:994 unrestricted integer variables,11,744 monomials.

All three have exact total degree4, individual degree4, coefficient height1, constant coefficient1, and every counted variable occurs. These are whole collected ordinary integer polynomials, not surrogate circuit metrics.

compact793 and balanced806 use the exact287-coordinate direct/strict_grouped_centered/equation.json, SHA256 e342eee770c4d8ec4311fd87d65b02b97171ab39152151c97a64b97c9890b11b. sparse994 uses the exact309-coordinate direct/strict_sparse_centered/equation.json, SHA256 b867f70b15340736a7caaeafacbe9de35adb5422fe7ab36964a444542919333d. The checker compares each copied original source with its sibling direct file byte for byte and verifies both complete affine maps before using their refactored sources.

The exact endpoint polynomial/certificate hashes are hard-coded in the portable final driver and also cross-checked against ENDPOINTS.json. Normal and optimized receipts bind those exact bytes, checker versions, direct sources, refactored sources and literal text equations.

## Full proof review

The final release report/proof_body.tex has been read in full. Its chain is correct:

1. Affine-square refactorization introduces uniquely determined monic affine coordinates, fixes every original coordinate, and restores each source residual by exact polynomial substitution.
2. Unit-coefficient normalization introduces triangular monic constant/scale coordinates with exact original-row pullbacks.
3. Prescribed signed source-term edges and internal free tree edges produce the literal half-incidence sum of squares.
4. Identifications are restricted to aliases of the same logical value or unit. No global C4-free assertion is required: the final complete coefficient collection, not a heuristic assumption, certifies height one.
5. Ordinary alias cycles, collision-safe quartic equality pairs, and the anchored unit path are nonnegative and have exactly their claimed equality/unit zero sets. For quartic pairs the complete absence of square-edge monomials on either pair coordinate is checked, in addition to exact final coefficient collection.
6. The forward map assigns affine/normalized coordinates, aliases and units, then uses subtree-divergence sums for every internal tree flow. Its full universal identity is P(L(x))=[sum R_r(x)^2+(sum R_r(x))^2]/2, not generally sum R_r(x)^2.
7. At any integer zero, nonnegativity makes all energies vanish. Reading one representative per logical class and summing row-block divergences recovers every normalized source row; triangular reconstruction gives the original source zero. Every auxiliary, alias, dummy, unit and tree flow is unique. Thus the transformations give a bijection of integer zero sets.

The collision-safe quartic pair polynomial is Q(a,b)=a^4+b^4-a^3b-ab^3=(a-b)^2(a^2+ab+b^2), with 2Q=(a^2-b^2)^2+(a^2-ab)^2+(ab-b^2)^2. It vanishes exactly on a=b over the reals. The stated pair criterion and disjoint alias namespaces prevent its four quartic monomials from colliding with graph terms; the checker verifies the whole identity and complete coefficient support anyway.

## Independent computation and scope

review/final_height_one_audit/ is a portable three-file standard-library checker closure. It imports no producer or incoming verifier. The final driver checks every polynomial coefficient and every symbolic vertex-divergence substitution, so the forward identity is verified universally, not at sample tuples. It also independently roundtrips all literal polynomial text, verifies both complete affine maps and all original source rows, compares exact sibling direct sources, and rejects30 graph plus8 affine corruptions in each Python mode. All tests raise explicit exceptions and remain active with -O.

The algebraic graph/refactor theorem is unconditional. The final Con(ZFC) equivalence is obtained by composing it with the direct strict-source semantic/calibration theorem, which is a separate audit obligation. These finite receipts do not by themselves establish that source's unbounded arithmetic semantics, prove consistency, give a new end-to-end kernel proof, establish historical priority, or prove a global optimum.

balanced806 and sparse994 improve both variable count and support over the inspected2215-variable/30468-term height-one predecessor. compact793 buys fewer variables with a larger51,982-term support. All remain different from the lower-variable small-coefficient direct quartics and the few-variable high-degree scalar equations.
