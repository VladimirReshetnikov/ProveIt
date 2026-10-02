# Wasserstein contact orders at uniform factor resonances

Let U_a be the centered uniform probability law on an interval of width a. Let mu_q be the law of the sum of independent centered uniforms of widths 1, q, q^2, ... . This article studies the smallest Wasserstein distance from mu_q to laws with two prescribed uniform convolution factors.

## Main results

For every fixed pair of integers B >= 2 and j >= 1, set

    sigma_(B,j) = U_(1/B) * U_(B^(-j))
    Delta_(B,j)(q) = inf_{nu in P_1(R)} W_1(mu_q, sigma_(B,j) * nu).

The article proves, from both sides of q = 1/B,

    Delta_(B,j)(q) = Theta_(B,j)(|q - 1/B|^j).

Thus every positive integer contact order occurs. The positive lower asymptotic coefficient is at least

    j! * P_B / [2*pi*(1 + pi*B^(j+1)/(B-1))],
    P_B = product_{l>=1} sinc(pi*B^(-l)) > 0.

The upper bound constructs actual probability remainders using finite signed Taylor kernels, positive-tail interpolation, and normalized positive parts. All constants and neighborhoods concern fixed B and j. No uniform growing-depth or varying-base assertion is made. The proof does not establish existence or equality of normalized one-sided limiting coefficients at orders j >= 2.

The original non-dyadic case is retained in full. For sigma_nd = U_(1/2) * U_(1/3), strictly positive one-sided coefficients exist:

    Delta_nd(1/2 +/- t) = c_plus/minus * t + o(t).

They have exact L^1 tangent-cone descriptions and satisfy

    |P| / [6*pi*(1 + 12*pi)] <= c_plus, c_minus <= 1/4,
    P = product_{k>=2} sinc(6*pi*2^(-k)) != 0.

Neither coefficient is evaluated and their equality is not asserted. The global adaptive bound is Delta_nd(q) <= |q - 1/2| / 4. This resolves the pinned report's sharp-distance question for this prescribed factor.

An explicit quadratic construction at B = j = 2 is also preserved, including the signed density, its chi-square energy bound 4735, and the constructive bound

    Delta_2(q) <= 6259 * (q - 1/2)^2 for |q - 1/2| <= 0.01.

A worked cubic example supplies both Taylor kernels and their exact endpoint coefficients. The quadratic and cubic cases illustrate the proved hierarchy; the hierarchy is not an extrapolation from numerical examples.

## Files

- `wasserstein-resonance.pdf`: 17-page mathematical article, including the general proof and explicit examples
- `wasserstein-resonance.tex`: editable standalone LaTeX source
- Five `check_*.py` scripts and corresponding `*-verification.json` receipts
- `SOURCE.txt`: pinned motivating and predecessor sources
- `REVISION.md`: description of changes from the first edition
- `build.sh`: ordinary two-pass pdfLaTeX build
- `SHA256SUMS`: package checksums

## Reproduce the checks

Use Python 3 with assertions enabled. Do not use `-O`. The linear, nested, cubic, and hierarchy checkers require only the standard library. The integer-base checker additionally requires mpmath (tested with version 1.3.0).

    python3 check_linear.py > linear-verification-new.json
    diff -u linear-verification.json linear-verification-new.json
    python3 check_nested.py > nested-verification-new.json
    diff -u nested-verification.json nested-verification-new.json
    python3 check_cubic.py > cubic-verification-new.json
    diff -u cubic-verification.json cubic-verification-new.json
    python3 check_hierarchy.py > hierarchy-verification-new.json
    diff -u hierarchy-verification.json hierarchy-verification-new.json
    python3 check_integer_base.py > integer-base-verification-new.json
    diff -u integer-base-verification.json integer-base-verification-new.json

Floating-point last digits can vary across runtime versions. Exact rational assertions and stated tolerances are the intended reproducible tests.

### Scope of finite verification

- Linear: 1,713 finite regressions, including 700 compact-source pairwise inequalities, 12 Fourier derivative ratios, and 1,001 comparisons of analytic bounds
- Nested: exact rational convolution coefficients and arithmetic for 4735, the Taylor constant 9, and 6259; 12 floating-point defect ratios
- Cubic: two exact rational endpoint coefficient rows, 16 finite Fourier checks of kernel identities, 196 scalar clipping checks, and 12 defect ratios
- Hierarchy: 8,780 exact finite extraction/support cases at depths 2 through 8; exact scalar leading signs through depth 8; 2,160 interpolation comparisons using rational moments and floating-point bound evaluations; 16 defect ratios
- Integer base: 72 high-precision coefficient/sign checks for bases 2 through 7 and depths 1 through 6, from both sides, with displacement 10^(-25) and 100 decimal digits of working precision

The original four checkers truncate their geometric products at index 99. The integer-base checker uses product indices l = 1,...,179 for P_B and i = 1,...,j+179 for the separated defect. The receipts record the evaluated finite quantities.

No script computes optimal Wasserstein distances, tangent-cone coefficients, weighted-integral suprema, the general upper constants, or normalized limiting coefficients. The tests are not interval certificates for the infinite products and are not a proof-assistant formalization. The all-depth theorem rests on the analytic proof in the article.

## Build

Install a working pdfLaTeX distribution with amsmath, amssymb, amsthm, lmodern, geometry, booktabs, microtype, and hyperref, then run:

    sh build.sh

Every page of the delivered PDF was visually inspected after compilation.

## Attribution and limitations

The predecessor manuscript already proves the ordinary, support-independent Fourier-value Wasserstein obstruction and asks about optimal approximate factorization. This article uses a bounded-source Fourier-derivative comparison together with constructive positive remainders. The motivating and predecessor pins appear in SOURCE.txt and the bibliography.

The real-line CDF transport identity is credited to Vallender; finite uniform-convolution density formulas to their classical literature, including Bradley and Gupta; related interpolation background to Ray and Schmidt-Hieber and Ghisi and Gobbino. The exact positive-tail inequality used here is proved directly. Fabius-type background is credited to Arias de Reyna.

This is a resolution and extension of the inspected repository question without a worldwide priority claim. Exact coefficients, optimal remainders, normalized higher-order limits, and useful estimates uniform in varying base or depth remain open in this article.

Revised 1 October 2026 for Vladimir Reshetnikov.
