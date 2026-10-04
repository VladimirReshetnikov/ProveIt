# Independent review of the first-norm monomial bound

**PASS; no requested change.** I read the complete helper and companion, compared the actual84 first-norm instructions and dependent producers, and ran fresh normal and optimized exact receipt replays from `/`. Both passed. No predecessor Python was imported or executed.

| Artifact | SHA-256 |
|---|---|
| `first_norm_monomial_scaling_bound.py` | `8f938efc5e1690d173bd9524cf83b60d3b78b2146be11593771632f44b0a3f58` |
| `first_norm_monomial_scaling_bound.json` | `b687e870b6a841f178c238399688f42ddd43640692d034526cf6b15b6a63c238` |
| `first_norm_monomial_scaling_bound.md` | `1a7677200ada8b171268aeb5189a9477dc2c9a3743fffb6e1f4d3de11dd3be4c` |

The quantified multiplication argument is sound. After Y=1 every permitted paid input is affine in T,X,k, including the dependent ports E=X and Z=k. Two multiplication gates, with arbitrarily many affine operations, cannot exceed degree four. The normalized multiplier gives restricted degree `4+a+b+e+d+f`, so every nonconstant surviving multiplier is excluded immediately. The remaining arbitrary power of Y becomes a nonzero scalar; it does not evade the original quartic obstruction.

I checked that obstruction directly from the displayed two-product normal form. The first quadratic leader must be proportional to Xk, forcing both affine factors to have linear parts proportional to X and k. Therefore its full polynomial has no T term. On X=0, factorization of the required quadratic T² makes both second-product linear parts proportional to T. The resulting vanishing k coefficients eliminate the Xk² coefficient globally, contradicting its required value -1. This covers the entire exceptional Y-power family, rather than merely the three sampled exponents.

The addition argument also extends correctly to all monomial multipliers. The radicand `(kY)² X(XY²+1)` has odd X-valuation, proving the quadratic P irreducible; no variable divides P. A circuit with at most one addition has output a monomial times a power of one binomial. Since the target has the sole nonmonomial irreducible factor P with multiplicity one, that power must be one and the binomial would be a monomial multiple of P. Multiplying P by a nonzero monomial preserves its three distinct terms, which is impossible for a binomial. Arbitrarily many multiplications and free rational constants do not affect this reasoning.

The helper authenticates its five dependencies, checks all84 rows for closure/liveness, and matches the literal 3M+2A component and the actual E=XY,Z=kY producers. Its exact sparse expansion and 729 exponent examples agree with the formulas: three enter the quartic branch and726 the degree branch. It reads the pinned predecessor receipt's contradiction data as evidence; the new companion supplies the complete mathematical argument. The finite examples are not being represented as a proof of the unbounded exponent quantifier.

The result is a component lower bound at exactly the six declared ports. The multiplier is computed from those ports, not supplied freely. Joint sharing with other paid registers, changed coordinates, nonmonomial positive multipliers and agreement only on constrained zeros remain outside the theorem. No transformed complete circuit or global84 lower bound is claimed. The positive-domain discussion correctly warns that scaling a factor alone does not automatically provide a fully paid scaled-output construction.
