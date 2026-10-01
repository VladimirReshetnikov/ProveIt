# Proof status

## Established in ordinary mathematics

1. A bipartite graph with a cover split two plus two has real stable complemented-row basis polynomial and signed unmatched-support polynomial
2. Every positive weighted matching-support diagonal in this class is real-rooted, with normalization by its actual degree in Newton's inequalities
3. All bipartite matching-support polynomials of matching rank at most four are rank-normalized ultra-log-concave under arbitrary positive activities; zero activities are handled by deleting their vertices
4. For the complete two-by-s core with n common exterior left vertices and m common exterior right vertices, signed stability is equivalent to (m+2)(n+2)s >= 2(m+1)(n+1)(s-1)
5. In the two-by-three family this is (n-2)(m-2) <= 12. The n=m=6 graph has 17 vertices and unstable signed support polynomial, while its unit-weight diagonal has five real negative roots

## Dependencies

- Standard upper-half-plane stability closure under real specialization, differentiation, positive scaling and polarization
- Grace–Walsh–Szegő polarization theorem, as in Borcea–Brändén
- Newton's inequalities
- König's matching–cover theorem
- Matroid basis polynomials are Lorentzian and nonnegative linear substitution preserves that property, from Brändén–Huh, for the smaller-shore input

Leaf attachment, vertex gluing and independent-column expectation are proved directly. The two covariance realizations are explicit. The complete-core basis characterization is proved directly. No unrefereed ProveIt block classification is needed for the mathematical argument.

## Review and exact checks

An independent proof review checked the main theorem's covariance PSD realizations, all Boolean minor types, expected determinant operator, complete-core polarization, gluing and weighted normalization. It found no substantive gap. Two exposition clarifications were incorporated: random variables are centered, and derivative polynomials are stable and nonzero before division in the gluing proof.

A separate audit approved the complete two-by-s stability boundary, including degenerate parameters, the exact binomial-ratio reduction, the 17-vertex minimality statement within that family, and all six rational evaluations for its unit-weight root certificate. No substantive correction was required.

The supplemental scripts use exact arithmetic. Numerical optimization and exploratory root searches suggested the theorem but are not part of the proof or required verification.

## Not claimed

- Lean or other proof-assistant certification
- Independent journal referee review
- Global priority
- Real-rootedness for every graph of matching rank four
- A rank-five ULC counterexample
- General unit-weight, one-shore-weighted, or two-shore-weighted rank normalization beyond the stated range

The earlier rank-six two-shore weighted failures remain compatible with these results. The smallest failure rank is reduced to five or six by the rank-four theorem.
