# A Spectral Representation for the Inverse Digamma Function

**Direct optimal truncation, eventual enveloping, and inverse Borel boundary singularities**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Read the article

- `inverse_digamma_spectral.pdf`: 24-page compiled article.
- `inverse_digamma_spectral.tex`: editable LaTeX source; its figures and generated table are included in the archive.

The article addresses the direct-inverse-partial-sum question explicitly left open in
ProveIt's *Exponential Accuracy and Stokes Transport for Inverse Harmonic Transseries*.
For the branch defined by `psi(W(X) + 1/2) = log(X)`, it proves an exact spectral
representation with a convergent inner-contour correction, an all-orders sharp
optimal-scale remainder for the direct inverse series, and eventual strict
consecutive-partial-sum envelopes. It also derives all logarithmic coefficients
of the nearest one-sided inverse-Borel boundary expansions and proves a general
boundary-phase transfer theorem.

The direct remainder's first relative correction is

    ((2*sigma^2 - 3*sigma + 7/12)/(2*pi) - pi/12)/X,
    sigma = M + 1 - pi*X.

The minus sign before `pi/12` is important: inversion of the forward truncation
has a plus sign in that position. The article proves the distinction and the
verification program checks it independently.

## Reproduce

Python 3.10 or later is recommended. Install the packages in `requirements.txt`.
The recorded environment was Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, and
matplotlib 3.10.8. No network access is needed after dependencies are installed.

```sh
python verification/verify.py
python verification/contour_check.py
python verification/make_figures.py
make pdf
```

The stored data and figures let `make pdf` run without repeating the numerical
calculations. A LaTeX installation with the packages in the source preamble is
required, including newtxtext, newtxmath, cleveref, and needspace.

## Verification artifacts

`verification/verify.py` carries out exact rational coefficient checks, exact
formal residual and error-polynomial checks, 24 high-precision direct-remainder
comparisons, complex density tests, and late-coefficient comparisons.
`verification/contour_check.py` independently checks the core-plus-spectral
remainder formula by finite quadrature at two quadrature resolutions.
`verification/make_figures.py` plots the saved results.

Actual recorded outputs are in `data/`, including JSON, CSV, the generated
LaTeX table, run logs, and a PDF build audit. The figures are available in PDF
and PNG formats. None of the floating-point checks is an interval certificate.

## Scope and provenance

The principal prior source was inspected in ProveIt at commit
`5804c7aff9955e6cbc09be2a71a295a07b238bc9`, path

    Analysis/Transseries/docs/series-and-transseries/
    Inverse_Harmonic_Stokes_Transport/inverse_harmonic_transseries.tex

with Git blob `2da951cd1d724042f9784365a448c584984ece74`.
The article documents the inspected scope and credits prior coefficient
asymptotics, contour-reversion methods, and nonlinear resurgence theory.
Newly arrived binary research archives at that checkpoint were not audited
claim by claim. Global priority is not established.

The universal mathematical results are supplied as conventional proofs.
No new Lean formalization is claimed. The eventual envelope thresholds are
existential; the paper does not claim global envelopes at every order and
argument. The Borel results are precise one-sided singular expansions, not
complete continuation data on every sheet. Nine further research questions
identify the remaining work.
