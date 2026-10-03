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
- `requirements.txt`: the pinned mpmath version for the integer-base checker
- `SHA256SUMS`: package checksums (verified in full, 17/17, on filing and
  retired; not in the repository)

## Reproduce the checks

Use Python 3 with assertions enabled. Do not use `-O`. (Since the editorial
amendments of 2026-10-01 below, each checker also writes its receipt to
`rerun/` with LF line endings; on the ProveIt machine use `py` for
`python3`.) The linear, nested, cubic, and hierarchy checkers require only the standard library. The integer-base checker additionally requires mpmath (tested with version 1.3.0).

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

(`build.sh` copies the rebuilt PDF over the filed `wasserstein-resonance.pdf`:
build on a copy.)

Every page of the delivered PDF was visually inspected after compilation.

## Attribution and limitations

The predecessor manuscript already proves the ordinary, support-independent Fourier-value Wasserstein obstruction and asks about optimal approximate factorization. This article uses a bounded-source Fourier-derivative comparison together with constructive positive remainders. The motivating and predecessor pins appear in SOURCE.txt and the bibliography.

The real-line CDF transport identity is credited to Vallender; finite uniform-convolution density formulas to their classical literature, including Bradley and Gupta; related interpolation background to Ray and Schmidt-Hieber and Ghisi and Gobbino. The exact positive-tail inequality used here is proved directly. Fabius-type background is credited to Arias de Reyna.

This is a resolution and extension of the inspected repository question without a worldwide priority claim. Exact coefficients, optimal remainders, normalized higher-order limits, and useful estimates uniform in varying base or depth remain open in this article.

Revised 1 October 2026 for Vladimir Reshetnikov.

## Editorial amendments (ProveIt, 2026-10-01)

Made in the editorial pass after batch 73 of `docs/incoming/` (see
`docs/incoming/README.md`), which filed this package on 2026-10-01; every
change to a program is marked `ed. (2026-10-01)`. The article
(`wasserstein-resonance.tex` and `.pdf`), `REVISION.md`, `SOURCE.txt`,
`build.sh`, `requirements.txt` and the five receipts are kept as delivered;
the notes below are recorded here instead of in the source.

- **First edition, not filed.** The batch delivered two editions:
  `wasserstein-resonance-package (1).zip` is the first (title *Linear and
  Quadratic Wasserstein Separation at a Dyadic Resonance*, 396-line source,
  9-page PDF, Theorems `thm:linear` and `thm:quadratic` only, its checksum
  ledger verified 9/9), and this package is its revision. The first
  edition is the `versions/v1/` that `REVISION.md` names but the package
  does not contain. It was not filed: every result of it is in this
  edition, whose `thm:hierarchy` answers its closing question on higher
  nested factors, and its `check_linear.py`, `check_nested.py`, their
  receipts and `build.sh` are byte-identical to the ones here. It survives
  in its arrival commit (see `docs/incoming/README.md`, batch 73). Its
  notation differs: its `sigma_1`, `Delta_1` are `sigma_nd`, `Delta_nd` here,
  whereas here `sigma_1 = U_(1/2) * U_(1/2)`. The phrase "optimal distance
  Delta_1" in `check_linear.py` and `linear-verification.json`, inherited
  from it, means `Delta_nd`.
- **Answered question and reciprocal notes.** The article answers the
  question "Sharp distance to a resonance" of
  `../Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/`, improves
  that article's bound (9.2), `|q - 1/2|/(2(1 - q))`, to `|q - 1/2|/4`, and
  replaces the order `(q - 1/2)^2` of its Theorem 8.1 near `q = 1/2` by the
  exact order `|q - 1/2|`; its resonant factorization (9.3) and the
  derivative product of Theorem 8.1 are re-derived here with credit.
  Reciprocal notes of 2026-10-01 now stand in that article (after Remark
  8.2, after Corollary 9.2 and after the question), and in
  `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/` (after Proposition
  3.9, `prop:wasserstein`, and after the 2026-09-30 note to its question
  "Optimal approximate factorization", whose ladder case stays open).
- **Attribution.** The article and `SOURCE.txt` say that the predecessor
  supplies only the Fourier-value inequality. The contact-order mechanism
  itself, a target zero of lower order than the factor's, evaluated just
  beyond the zero, is already in `prop:wasserstein` of
  `../Arithmetic_Convolution_Factors_Fabius_Type_Laws/` (an order-`r` bound
  `a_r h^r / (4 pi (t_0 + h))` for divisibility-ladder targets) and in
  `thm:metric` of `../Arithmetic_Rigidity_off_Resonance_Geometric_Uniform_Laws/`
  (the double-zero case for geometric targets). What is new here is the
  comparison of derivatives at the zero (Lemma 2.1), which gives a lower
  bound linear rather than quadratic in the derivative product, and the
  matching constructive upper bounds.
- **Pins.** The pinned commits in `SOURCE.txt` and the bibliography are
  ancestors of the filing commit, and the cited line ranges (host
  question 748-751, Theorem 8.1 from 480, Theorem 9.1 to Corollary 9.2 at
  538-571; predecessor 588-635 and 1592-1605) hold at those commits. The
  SHA-256 that `SOURCE.txt` gives for the inspected host source matches no
  committed version of the host or of the predecessor (checked against
  every committed version of both files, with LF and with CRLF line
  endings); the inspected text was evidently a local copy.
- **Lean crosswalk.** No result of the article is formalized, and the
  repository's tracked Lean sources mention neither Wasserstein distance
  nor Vallender's formula. Two ingredients have Lean counterparts in
  `Analysis/FabiusFunction/Lean/FabiusFunction/`, in the normalized
  convention (`Y_q = (1 - q) sum q^k V_k`, `V_k` uniform on `[0, 1]`, so
  `X_q = (Y_q - 1/2)/(1 - q)`): the transform identity
  `Phi_q(t) = prod_k sinc(pi q^k t)` of Section 1 is
  `Fabius.charFun_geometricUniformDistribution_eq_phase_mul_geometricSincProduct`
  (`GeometricSincCharacteristicFunction.lean`; the phase cancels after the
  affine change), and the separation of the first uniform in Sections 2, 4
  and 6 is `Fabius.ProbabilityRepresentation.geometricUniformSeries_split`
  (`GeometricUniformLaw.lean`; law level for general weights:
  `weightedUniformDistribution_split`, `WeightedUniformSeries.lean`).
- **Checked on filing (not a claim review).** The constants
  `P = -0.04620229913...`, `|P|/(6 pi (1 + 12 pi)) = 6.3338e-5`,
  `P_3 = P_dy = 0.55377127589` and `P_3/(pi (1 + 8 pi)) = 0.0067452`; the
  defect (3) and `sinc(6 pi q) = -(delta/q) sinc(6 pi delta)`; the
  derivative signs and the coefficient `epsilon_(B,j) j! P_B` of (19), and
  the lower coefficient of Theorem 1.2 with `R_(1/B) = B/(2(B - 1))`; the
  coupling of Section 2.2 (cost `|q - 1/2|/4`, smaller than the host's
  bound for every `q`); the Taylor constant
  `1/(4 * 0.49^4) + 1/(2 * 0.49^3) = 8.59 < 9`; the energy
  `3675 + 36 + 1024 = 4735`. Two points a reviewer should not mistake for
  errors: `6259 = 9 + (5/4) * 5000` uses `K < 5000`, not `K <= 4735` (which
  would give 5927.75), and is a valid, deliberately crude constant; and
  the interval `[.49, .51]` that Theorem 1.2 allows for `B = 2` (proved in
  Section 4) and the integer-base interval `I_B = [3/(4B), 5/(4B)]` of
  Section 5 are two proved choices, not a contradiction.
- **Checkers** (`check_linear.py`, `check_nested.py`, `check_cubic.py`,
  `check_hierarchy.py`, `check_integer_base.py`): new option `--output-dir`.
  As delivered each printed its receipt only to standard output, and the
  recipe above (a shell redirection, then `diff -u`) writes CRLF on
  Windows and reports last-digit float differences as failures. Each now
  also writes `rerun/<name>-verification.json` beside itself (or into
  `--output-dir`), with LF line endings, and still prints the receipt.
  Pass `--output-dir .` from this directory, on a copy, to regenerate the
  recorded receipts. A rerun of the amended checkers on a copy (2026-10-01,
  `py`, Python 3.14.4, mpmath 1.3.0) passed all five; the standard output
  equals the `rerun/` file after CRLF-to-LF conversion;
  `integer-base-verification.json` was reproduced byte for byte, and the
  other four receipts agree in every exact field, with 25 of 128 floats
  differing in the last digit (relative difference at most 4.6e-16), the
  variation this README already anticipates.
- `build.sh`: kept as delivered. It writes to `build/` and then copies the
  rebuilt PDF over the filed one, so build on a copy. A two-pass build of
  the filed source on a copy (MiKTeX 26.2) gives 17 pages with no error,
  undefined reference, overfull or underfull box; the filed PDF is the
  delivered one.
- `README.md`: the file list (`requirements.txt`, retired ledger), the
  parentheses after the reproduction and build instructions, and this
  section.
