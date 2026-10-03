# Independent review of the local algebra and literal quartic

Reviewed 2026-10-03. Verdict: accepted. The final supplement explicitly defines “natural” as **nonnegative integer**, as required for the binary-valued auxiliary witnesses. The final convention-clarified artifact was independently reconstructed again under normal and optimized Python, with identical successful output.

The reviewed supplement files are pinned by `reviewed-supplement-files.sha256`. This review concerns one local G transition only. It establishes no unbounded reachability or broader finite-fold claim.

## 1. Algebra, Boolean degree, and exact dependency

The sixteen signed exact-component indicators agree with the four geometric rewrites. The local algebra is valid on the entire binary full shift by exact component recognition and nonoverlapping output sets. The halo sizes are 30, 35, 40, and 45. The six distinct L top monomials survive with nonzero coefficients, so the unique real multilinear Boolean representative has exact degree 45.

The union of those six top supports is exactly the 78-cell rectangle. The essentiality argument by uniqueness of multilinear interpolation is valid, and the concrete witnesses supplied in the earlier audit independently verify every input cell. Thus the exact-radius strengthening applies to these particular G and F rules. It is not an optimality claim across alternative constructions.

The finite-support conservation argument in indicator form also checks: every translate sum is finite and each rewrite has as many births as removals.

## 2. The exact-one-auxiliary-tuple theorem

Each multiplier residual is `z−uv` or `z−u+uv`, with the new auxiliary z appearing linearly with coefficient one and depending only on external bits or earlier auxiliaries. The graph is acyclic. The 78 bit residuals force every real external input to be zero or one. For these inputs, the multiplication chains force each auxiliary uniquely and keep it in `{0,1}`. The last residual forces the external output to be exactly the local Boolean function.

The literal expanded polynomial equals the sum of the squares of these residuals over the integers. Hence it is a nonnegative real polynomial whose zero set is exactly the simultaneous residual zero set. For fixed external input/output, its nonnegative-integer auxiliary fiber therefore has size one exactly for a valid binary local transition, and size zero otherwise. The identical statement holds for the real auxiliary fiber. No additional output-bit residual is necessary because the forced output is already binary.

The gate residual degrees are at most two. The input-bit squares contribute uncancelled fourth powers, proving that the expanded polynomial has degree exactly four. The auxiliary projection of a quartic can encode the degree-45 Boolean function; these are different degree statements and are consistent.

## 3. Independent reconstruction of the artifact

`reconstruct_local_quartic.py` imports neither the generator nor the main quartic checker. It independently reconstructs the sixteen indicators from separately encoded geometric rules, using rectangular halos rather than the builder's Minkowski-sum procedure. It reconstructs all gates and residuals, and only then reads the exported artifact to compare them.

The script independently expands each reconstructed residual square by separate diagonal terms and unordered cross terms. Its exact sparse polynomial equals every term and coefficient of `local-quartic-certificate.json`. It also checks the complete variable order, coordinates, indicators, gate instructions, residuals, and degree-45 top terms. Both ordinary and optimized Python executions passed; all checks use explicit exceptions.

The main quartic checker's source was also reviewed. Its sampling checks are appropriate supplemental checks and it does not present sampling as proof of uniqueness. The independent geometric reconstruction goes beyond its expansion of the exported residuals by establishing that those residuals themselves exactly implement the prescribed rule.

## 4. Verified resource ledger

- 78 external input bits; 79 external variables including output
- 614 nonnegative-integer auxiliaries; 693 total variables
- 26 plain-product gates and 588 complementary-product gates
- 693 residuals, including all gates, 78 bit residuals, and one output residual
- 1,990 residual-monomial occurrences
- 6,032 ordered SOS-product occurrences
- 3,403 collected expanded monomials
- Exact total degree 4; maximum absolute coefficient 2

A further exact independent accounting explains the collection count:

- The 693 separately squared residuals have 4,011 distinct terms before collection across residuals
- Exactly 608 monomials occur twice, always with coefficient +1 at each occurrence
- They are 604 auxiliary squares, the central input square, and three shared degree-four input products
- There are no cancellations and no other collisions
- Consequently `4011−608=3403` collected monomials

The three repeated input products are `c_(0,0)^2 c_(1,0)^2`, `c_(0,0)^2 c_(2,0)^2`, and `c_(-2,0)^2 c_(0,0)^2`.

Exact coefficient histogram: 1,361 coefficients equal −2; 774 equal +1; 1,268 equal +2.

Exact degree histogram: 1,434 degree-two terms; 1,280 degree-three terms; 689 degree-four terms.

The machine-readable result and certificate hash are in `quartic-reconstruction-results.json`; the optimized-run output is in `quartic-reconstruction-optimized.txt`.

## Conclusion

No algebraic, counting, implementation, or uniqueness defect was found. The supplement and literal polynomial support the stated local one-step unique-witness theorem with the exact resource ledger above.
