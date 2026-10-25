# Height one quartics from incidence local contraction

The three delivered equations have unrestricted integer variables, exact total degree four, individual degree at most four, constant coefficient one, and every nonzero collected coefficient equal to +1 or -1:

- compact793: 793 variables and 51,982 monomials. This minimizes variables among the three selected endpoints but has more terms than the incoming 2,215-variable equation.
- balanced806: 806 variables and 23,719 monomials.
- sparse994: 994 variables and 11,744 monomials.

The balanced and sparse equations improve both variables and monomials relative to the inspected incoming 2,215-variable, 30,468-monomial graph equation. This is not a global-optimality claim. The three points are a deliberately selected tradeoff, not an exhaustive Pareto frontier.

Each endpoint contains the actual complete collected polynomial as polynomial.json and an ordinary literal equation as polynomial.txt. Its certificate binds every factor to a source occurrence, every equality class, and every edge of the incidence graph. ENDPOINTS.json gives exact metrics and hashes. CONFIG.json fixes all generator inputs; none is a polynomial parameter.

The new ideas are exact incidence-local alias contraction (no global C4 restriction), collision-safe two-alias quartic equality, and affine-square refactorization before coefficient normalization. report/proof_body.tex supplies the complete ordinary proof, including explicit forward and inverse maps, uniqueness, and the correct off-zero identity. report/results.tex identifies the exact selected equations.

The first two endpoints compile the enclosing package's 287-integer strict grouped source. The third compiles its 309-integer strict sparse source. SOURCE_BINDINGS.json binds their literal source bytes. The source consistency calibration and strict cap/sign proofs are supplied by the enclosing direct-source component. This module proves a bijection of zero sets and does not independently re-prove that source calibration. It does not prove Con(ZFC), universal nonvanishing, or a new end-to-end formal-kernel consistency theorem.

## Reproduce

Python 3.10+ and its standard library suffice. No network, CAS, source checkout, or installed package is required.

    python verify.py --report replay.json

By default this runs both ordinary and optimized child interpreters. It checks every coefficient, monic source extension, alias binding, internal tree, literal equation, and universal symbolic canonical lift. It then regenerates every source transformation and every endpoint byte for byte in a temporary directory. All checks use explicit exceptions and remain active under -O. Use --mode normal or --mode optimized for one mode, or --skip-rebuild to omit only deterministic regeneration.

Finite corruption tests and sample evaluations are additional implementation checks, not substitutes for the unbounded proof. The stronger independent_audit.py checks each canonical vertex-divergence identity symbolically, not by sampling.

comparison/COMPARISON.json records a matched-source compiler comparison. Its old artifact is an authenticated historical input, not a delivered endpoint. The new matched polynomial is regenerated and independently audited by compare_matched.py; its source and complete expected polynomial hash are retained.
