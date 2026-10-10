# Polylogarithm Continuation

## Fractional Kernels, Cayley Quotients, and Joint Scaling Limits

Research prepared for Vladimir Reshetnikov's ProveIt project, 10 October 2026 (UTC).

**Read `article.pdf`.** Its complete source is `article.tex`, with the mathematical sections in `sections/`, the bibliography in `references.tex`, and vector figures in `figures/`.

Baseline: `28357e8ca63dd78327db91d9be239d75e4462879` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/28357e8ca63dd78327db91d9be239d75e4462879/Analysis/Polylogarithms/docs/manuscript).

## Main contributions

1. **A sharp signed-moment classification.** For `a >= 0, b > 0`, the moments `H_(n-1)^(b) / n^a` have a finite real signed measure exactly when `a > 0, a+b >= 1`, or when `a = 0, b > 1`. The measure is unique; the interior density changes sign once; the two critical edges carry positive atoms at one.
2. **Complex and angular zero theorems throughout that domain.** The double polylogarithm has only its double origin zero on the principal slit plane. Every open upper arc of radius at most one has exactly one simple imaginary-part zero. Atomic boundary values use Abel continuation.
3. **Endpoint asymptotic laws.** Two power-law atom-formation scales, an exponential scale at `b = 1`, and signed mass asymptotic `1/(e a)` at the excluded logarithmic corner.
4. **A proved part of an existing conjecture.** The first nonconstant coefficient in the normalized-radius expansion has the predicted sign in the complete previously conjectured local range, including every real `a >= 2`. A unique fractional threshold is proved.
5. **Fractional nonmonotonicity.** Exact rational interval signs and an analytic implicit-function argument prove that a strict local radial maximum emerges immediately below the threshold at `b = 1/2`, with an explicit square-root onset law. A complementary exact certificate proves strict local minima above the threshold at `b=999/1000`. The opposite quartic signs prove at least one interior degeneracy along the threshold. The intervals in `a` are existential; the separately sampled rational pair and the approximate degeneracy location are labeled diagnostic.
6. **An adjacent-index Bessel regime.** For `n = k+r` with any fixed integer `r`, a complete profile expansion is uniform over the entire Lerch interval `0 <= rho <= 1`. Simple branches near positive Bessel zeros have explicit locations through `k^(-4)` in `a`; their Lerch motion is exponentially small.
7. **The complete small-Lerch-parameter count for every fixed pair `(n,k)`.** The central branches are classified by a nonzero integer polynomial in `log(2)`. Exact interval arithmetic certifies representative signs.
8. **A joint reflected-gamma transition.** At `n=(m+1)(log m+c)`, the normalized moment has limiting factor `exp((zeta(2)/(2 gamma)-gamma) exp(-c))`, with a proved first correction and uniform remainder.
9. **An all-weight Cayley quotient theorem.** The raw row rank and the entire shuffle-ideal quotient are computed. The latter is polynomial, with explicit Hilbert and conjugation-character equations, an infinite product, and coefficient asymptotics.
10. **A proved all-index identity family.** The explicit pure-depth Cayley expression for `S_p` includes a 96-term weight-seven identity for `S_6`, supplied as exact structured word data.

The final article also contains a correction and status ledger and sixteen focused further research topics. All claims of newness are relative to the inspected sources; no exhaustive historical priority claim is made.

## What remains open

- The frozen, short, depth-two reduction of `S_6`. The high-depth identity and the formal quotient theorem do not prove it.
- The original all-radius normalized-motion conjecture for the specified integer outer orders. Its local coefficient is settled; a general fractional extension fails.
- Numerical independence of level-four periods. Every dimension here belongs to a precisely specified formal quotient.
- Global enumeration of zeros in the adjacent-index Bessel limit, growing Bessel order or zero label, and the central exponentially sensitive unfolding.
- Uniform optimal truncation for two growing gamma exponents.

`S_4`, the specified level-four product-matrix rank theorem, and the rejection of the older `S_8` vector were already settled in the pinned canonical manuscript. They are not new results of this package.

## Reproduce the arithmetic

Python 3.10 or later is recommended. The recorded replay used Python 3.12.14, SymPy 1.14.0, mpmath 1.3.0, NumPy 2.3.5, and Matplotlib 3.10.8. Install the listed packages in your preferred environment if needed:

```sh
python3 -m pip install -r requirements.txt
python3 code/run_verification.py
```

The exact replay builds rational matrices, checks rational polynomial certificates, regenerates Bessel coefficients, and checks exact interval signs. The standard-library sign and turning-point certificates require neither SymPy nor a numerical special-function package when run individually.

For the optional numerical diagnostics:

```sh
python3 code/run_verification.py --diagnostics
```

The provided run report is `verification/replay_with_diagnostics.json`; the individual logs are in `verification/logs/`. Exact mathematical evidence lives in `data/`, beside explicitly named diagnostic data. Replays replace their own generated evidence files.

Extra radial explorations can be reproduced individually from the bundle root:

```sh
python3 code/kernels/check_fractional_radial_motion.py
python3 code/kernels/check_rational_radial_motion.py
python3 code/kernels/check_quartic_sign_sweep.py
python3 code/kernels/locate_quartic_sign_transition.py
```

The first two scripts use analytically bounded disk-series truncations; the last two use finite local coefficient formulas. All four are floating-point diagnostics. Their arithmetic and implicit roots are not interval certificates.

### Evidence distinction

| Type | Examples | What it establishes |
|---|---|---|
| Analytic proof | kernel sign change, full-weight gamma localization, Bessel coefficient control | Stated all-parameter or asymptotic theorem |
| Exact rational or integer certificate | Bernstein coefficients, Cayley ranks, log-polynomial signs, fractional turning signs | Its finite algebraic or interval assertion |
| Exact symbolic generation | gamma correction and Bessel higher coefficients | The coefficient identity; analytic remainder is proved in the article |
| Floating-point diagnostic | quadrature, sampled zeros, plots | Consistency checks only |

The proofs received independent cross-audits during preparation, and the exact certificate programs were replayed. This is not proof-assistant verification or external peer review.

## Build the PDF and figures

The source uses standard TeX Live packages and requires no network access or external bibliography service.

```sh
make
```

If `latexmk` is unavailable:

```sh
python3 code/build_pdf.py
```

The PDF figures are already included. To regenerate them:

```sh
python3 code/make_figures.py
python3 code/zeros/make_bessel_figure.py
```

The first command reads the saved gamma diagnostic data. The Bessel plotting script uses the exact finite-polynomial formula and records numerical samples; it fits no coefficients. `make clean` removes ordinary LaTeX intermediate files while preserving the PDF.

## Integration

Suggested report location:

```text
Analysis/Polylogarithms/docs/reports/fractional-cayley-scaling/
```

Read `integration/INTEGRATION.md` for the chapter-level map, `integration/CLAIM_STATUS.json` for the result ledger, and `integration/source_snapshot.json` for the pinned source hashes. New mathematical labels were checked against the canonical chapter labels. Keep the theorem hypotheses, atom terms, open-arc restriction, and evidence distinctions when merging.

The package excludes retrieved historical reports and the unfinished large `S_6` matrix search. The supplied mathematical results and replays do not depend on those scratch files. `MANIFEST.sha256` records the delivered file hashes.
