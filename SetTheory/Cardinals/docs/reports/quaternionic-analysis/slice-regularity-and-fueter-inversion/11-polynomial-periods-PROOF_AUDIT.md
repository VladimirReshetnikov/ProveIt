# Proof audit and limits

This is an internal mathematical audit accompanying an unrefereed article.
It is not an independent referee report or a proof-assistant certificate.

## Normalizations fixed throughout

- Spatial dimension m=2h+1; physical dimension m+1=2h+2; h >= 1.
- The map is Delta_(2h+2)^h without an additional rescaling.
- c_h = 2^h h! and kappa_h = (-1)^(h+1)/(2^(2h-1) h! (h-1)!).
- C_h = (-1)^h c_h^2, so kappa_h C_h = -2h.
- Positively oriented planar circles define residues.
- Central complex conjugation acts only on the complexification E + i E.
- Polynomial coefficients in the kernel and period spaces lie in the real
  coefficient module E, not in its complexification.

## Critical arguments reviewed

1. **Radial image.** The scalar and vector radial Laplacians have different
   zero-order terms. Their commutators with R and S give the same factor c_h.
   The Cauchy--Riemann identities imply both Vekua equations.

2. **Current closedness.** Differentiation of the weight cancels exactly the
   2(h-1)Q term. The h=1 case is treated without a spurious negative power.

3. **Hermite identity.** Matching h+1 complex jets at z and their conjugates at
   conjugate(z) by a real-coefficient polynomial of degree <=2h+1 proves that
   the monomial test is an exact spanning reduction for every h. This is not
   the same as testing a finite number of h values numerically.

4. **No circular inverse proof.** The forward radial formula and Hermite
   identity are established before the inverse is constructed. Holomorphicity
   follows from the factor (t-z)^h in the anti-holomorphic derivative. The
   moving-node derivatives reproduce exactly the required Hermite jets.

5. **Polynomial kernel.** An imaginary constant is generally not in the
   kernel. For h=1, the stem i*a maps to -2*I*a/y^2. The symbolic suite includes
   imaginary monomials specifically to detect a false complex-linear argument.

6. **Realization.** A logarithm branch change adds the real kernel polynomial
   M(z), so its target patches globally. The target need not be rational or
   free of log|z-p| terms. Its period is M, with the 2*pi*i normalization.

7. **Finite covers.** Additive real period groups have no nonzero torsion.
   A finite-index subgroup contains a positive power of every loop. The deck
   group is discrete as an abstract group even if its coefficient-space image
   is dense.

8. **Residue hierarchy.** Real coefficients force conjugate roots with equal
   multiplicity. A nonzero polynomial of degree <2h therefore has order at p
   at most h-1. The filtration classifies the minimum growth among
   representatives, not the growth of every representative.

9. **Sharp bounds without a growth assumption.** The error in the leading
   Fourier extraction is bounded by C*rho^(s+1) times the circle L1 norm.
   Hence the universal lower estimate is valid even for faster-growing
   representatives. It is not based on assuming an asymptotic expansion of an
   arbitrary target.

10. **Attainment and energy.** The canonical logarithmic target has a uniform
    angular leading term. Its axial-pair norm is angle-independent to leading
    order. The physical sphere average is exactly sigma_(2h)*(|P|^2+|Q|^2).
    The radial measure includes y^(2h), which cancels v^(-2h) from the leading
    pair norm. The s=1 logarithmic endpoint is computed separately from s>=2.

11. **Lp scope.** The residue integrability classification is stated for
    exponents >=1, where Jensen and Holder give the required lower estimate.
    No unproved extrapolation to quasi-norm exponents below one is made.

12. **Removability.** Zero residue guarantees a single-valued inverse on a
    punctured domain, not extension through the puncture. The stem 1/(z-p)
    supplies a zero-residue singular example. The article does not claim a
    complete removability theorem.

## Remaining verification limits

The symbolic code certifies finite exact identities and the numerical code
checks finite diagnostics. Neither formally verifies topology, all h, or
improper-integral limiting arguments. Those are covered by written proofs in
the article and remain subject to mathematical review. No Lean/Rocq file is
included, no existing repo theorem is silently treated as an axiom, and no
claim of historical priority is established.

Domains crossing the real axis, fractional Fueter operators, arbitrary
nonaxial targets, and growth-controlled infinite-connectivity realization are
outside the proved scope. The final section formulates research directions
around those limits.
