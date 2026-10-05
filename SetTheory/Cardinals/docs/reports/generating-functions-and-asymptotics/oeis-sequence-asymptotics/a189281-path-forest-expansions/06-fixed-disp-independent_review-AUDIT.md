# Independent audit: fixed-displacement permutation expansion

Reviewed `../proof.md` on 2026-10-01. The exact identities, all-orders algebraic remainder, flat geometry comparison and inverse qualifications pass. No guessed recurrence, unproved holonomicity assertion, or full exponentially small coefficient expansion is used.

## Exact counting and stable chains

A selected set of forbidden edges forms directed paths. Matching the position paths to value paths of equal lengths contributes exactly `prod α_i!`; their orientations are fixed by the positive displacement. The remaining isolated vertices contribute `(n-j-c)!`. Adjacent distinct tiles do not merge unless their connecting edge was selected, so the paired-tiling description neither omits nor duplicates assignments.

For one chain, ordering its `N-j` tiles gives `(N-j)_c/prod α_i!`. The residue version of Lagrange inversion gives exactly the same coefficient in `C λ^N`. To obtain formula (6), expand the extra `C^(r-1)`. If `b` marks the selected factors of `φ'`, their contribution shifts the exponent by `sum i b_i`; applying the one-chain residue identity to the remaining marks shifts it back by `sum (i-1)b_i`. The resulting falling factorial is therefore precisely `(n-j-h)_(c-h)`, with sign `(-1)^h`. This checks the potentially delicate normalization.

The weighted-degree agreement holds for every individual chain of length at least `2J`. Consequently, multiplication depends only on total length and the fixed number of chains throughout the retained range. There is no hidden residue-class dependence at an algebraic order.

## Genuine uniform remainder

The factorial-moment bound controls the inclusion–exclusion truncation without assuming convergence of an alternating infinite series. With `j=O(log n/log log n)`, its exponential factor is bounded and the factorial tail is smaller than the required algebraic remainder. The same estimate at `j=γn` proves the stated flat comparison of forest geometries, with `γ<min(δ/2,1/4)`.

For defect `D>K`, the positive profile generating function `exp(u/(1-u))` controls the entire tail at `u=1/n`. For `D<=K`, only the dimer count is unbounded. In the normalized stable-chain formula, the degree-h prefactor is bounded using `e_h<=j^h/h!`; the rising-factorial ratio grows only polynomially in h. The remaining normalized falling factorial has absolute value at most one in the stable truncation range. Thus the discarded h-tail has the claimed `n^(-K-1)` times polynomial-in-j bound.

For retained h, expansion of the logarithms of falling factorials and their reciprocal has remainders bounded by `n^(-K-1)` times a fixed polynomial in j and `exp(Cj²/n)`. After multiplication by the dimer factor `1/k!`, every such remainder is summable. This is the reason that no power of `log n` is lost in the final remainder. Extending the retained polynomial sums in k beyond the cutoff is again factorially negligible.

## Independent coefficient reconstruction

`check_coefficients.py` is an independent standard-library implementation. It expands normalized falling products and inverts the denominator by a complete-homogeneous recurrence. Polynomial coefficients in the dimer count are summed by Newton forward differences:

`e * sum_(k>=0) (-1)^k P(k)/k! = sum_j (-1)^j Δ^j P(0)/j!`.

The theoretical degree bound at retained order l is `2l`; two extra interpolation points are checked rather than merely fitted. No producer code or Touchard routine is imported.

The optimization-safe run verifies:

- A189281 coefficients through order six: `1,3,2,1,0,3,26`;
- 30 higher-defect profiles;
- 299 finite-difference polynomial checks, including the general-parameter checks;
- all 16 pairs `1<=r,s<=4` through order three;
- 25 profile counts from fresh direct edge-subset enumeration in two arithmetic-progression chains.

These exact checks corroborate the formulas; the analytic argument supplies the asymptotic error theorem.

## Inversion

The explicit gamma models are positive and increasing on a large real tail, with logarithmic slope asymptotic to `log x`. The forward logarithmic error therefore moves their roots by `O(x^(-K-1)/log x)`. Enlarging the constant yields the two ceiling inequalities even at endpoints. Eventual increase of the original sequence follows from the leading relative equivalent, since `a(n+1)/a(n)~n+1`.

The Lagrange ordinate-reversion operator is correctly normalized by `1/ψ(X+1)`. For A189281, `log D=3/X-5/(2X²)+4/X³+O(X^-4)`. The k=2 term yields exactly `-9/(X³ψ²)-9ψ'/(2X²ψ³)`; all omitted terms fit the stated `O(X^-4/log X)` bound. The proof appropriately distinguishes inverse asymptotics and integer threshold information from a chosen analytic interpolation of the discrete sequence.

## Additional bounded transcription check

The same independent reconstruction was subsequently extended to order ten. `check_order_ten.py` verifies every coefficient printed in the article, including `101,124,-1409,-13266`, using 139 higher-defect profiles and 423 polynomial checks. It passed under optimization-safe execution. The original order-six/general-parameter/direct-count checks remain separately recorded.
