# Reproducing the rational ordinate enclosures

Run these commands from this directory with Python 3. Both use only its standard library.

```sh
python certify_moments.py
python verify_zeros.py
```

The first script constructs certified decimal intervals for the first seventeen power sums of the scaled atoms y = 200/(1/4 + gamma^2), counting each distinct positive ordinate with its multiplicity. The second reads those intervals from certified_moments.json and the rational trial polynomials, cut points, and separators from witness.json. It verifies all four enclosures using integer and rational arithmetic. verified_zeros.txt records the output. The arguments --moments and --witness accept alternative input paths.

## Why the checker works

Let M_k be the kth scaled power sum, let the distinct scaled atoms satisfy y_1 > y_2 > ..., and write mu = sum_i m_i y_i delta_{y_i}. Integration of a polynomial against mu uses the moments M_1, M_2, ... in ascending order. The certificate uses the following checks for each index j starting at 1.

1. On the first j rational trial polynomials the matrix representing integration of (y − cut_j) f g is symmetric, has positive diagonal, and is strictly diagonally dominant. The program verifies these facts by bounding every entry from its coefficients. This matrix is positive definite. If at most j − 1 atoms exceeded the cut, a nonzero combination of the j polynomials could vanish on all such atoms. Its quadratic form would be nonpositive, a contradiction. Thus y_j > cut_j.
2. The checker proves M_k − sum_{i<j} cut_i^k ≤ 2 b^k for the supplied k and rational b. Since every multiplicity is at least one and y_j ≥ y_{j+1}, this proves y_{j+1} ≤ b. The checker also requires b < cut_j. If the atom at y_j had multiplicity at least two, the same remainder would be at least 2 y_j^k > 2 b^k. Thus each reported zero is simple.
3. Normalize q_j^2 dmu to a probability measure. Compute an interval for its mean R and an upper bound E on its mean squared distance from the rational center supplied with q_j. Then its variance is at most E. The product (y − y_j)(y − b) is nonnegative throughout the support. Its integral under the normalized measure is Var(y) + (R − y_j)(R − b). The checker verifies R > b and therefore obtains y_j ≤ R + E/(R − b). Replacing each term by the appropriate rational endpoint preserves the bound.
4. The map y to sqrt(200/y − 1/4) reverses the bounds. Integer square roots and outward rounding give the printed decimal endpoints.

The witness generator is optional. Running `python verify_zeros.py --propose` computes approximate generalized eigenvectors using mpmath 1.3.0, rounds them to rational coefficients, and saves the resulting witnesses after the same exact checks. Correctness of those floating-point eigenvectors is unnecessary. The independent floating-point experiment in ritz_demo.py illustrates convergence as matrix size increases.
