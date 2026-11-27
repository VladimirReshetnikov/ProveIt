# Formalization plan and verification boundary

## Current status

The deliverable contains mathematical proofs and executable exact checks. **No Lean formalization of its new theorems is claimed.** The repository's upstream Lean development does not automatically certify results derived later in this paper. The present finite-field theorems are unconditional and require no hypothesis about zeros of $L$-functions.

The Python programs use exact arithmetic for finite formulas and independent small-field enumeration. They check implementations and examples; they are not kernel-checked proofs of statements quantified over all fields and dimensions. Rational enclosures certify the displayed numerical constants under their explicit product-tail bounds.

## Suggested proof stages

1. **Finite linear algebra.** Define alternating bilinear forms over finite fields, including characteristic two. Formalize symplectic frames, restricted ranks, radicals, and the transitivity needed to replace uniform group elements by uniform frames. Establish the embedding count, with zero outside its feasible range.

2. **Finite probability and exact counts.** Model uniform distributions on finite sets and pushforwards by rank and residual form. Prove the residual likelihood, its sign classification and the finite total-variation identity. Distinguish matrix distributions from their rank distributions in the types and statements.

3. **Kernel moments.** Define Gaussian binomial coefficients with boundary conventions. Count subspaces of each restricted-form type and prove the rank and defect moment identities. For the joint law, formalize the conditional distribution of the ordinary kernel after imposing a defect-kernel constraint. Recover mixed moments by finite sums.

4. **Moment inversion.** Prove the Gaussian-binomial inversion and interpolation identities on the grids $1,q,q^2,\ldots$ and $1,q^2,q^4,\ldots$. Establish coefficient bounds and out-of-grid estimates before using the identities on limiting distributions. This is where finite identities become summable quantitative comparisons.

5. **Infinite products and signed measures.** Construct $\gamma_\infty,\eta_\infty,\theta_\infty$, prove positivity and quantitative tail estimates, normalize the limiting laws and verify the moments of $\xi_d$ and $\zeta$. Record that each signed correction has total mass zero and determine its sign pattern.

6. **Uniform asymptotics.** State constants with dependence only on $q$. Retain the factor $q^{-dj}$ in every positive-order rank-moment remainder; the zeroth remainder is exactly zero. Prove summable bounds uniform in $d\ge0$, control interpolation tails, and then obtain the $L^1$ errors. For the joint theorem, justify the two-variable inversion and the subtraction of the product of the actual marginals.

7. **Statistical corollaries.** Derive the rank, full-matrix and joint total-variation expansions from signed $L^1$ estimates. Prove asymptotic optimality of the exclusive-or event using the sign of $-\xi_d\otimes\zeta$, including its zero cases.

## Using the supplied checks

`code/exact_laws.py`, `code/joint_laws.py` and `code/independent_enumeration.py` provide reproducible regression cases. Their outputs under `results/` can guide theorem statements and detect normalization, parity and characteristic-two errors. A future formalization should prove the underlying identities directly rather than introduce the numerical outputs, asymptotic estimates or principal theorems as axioms.

