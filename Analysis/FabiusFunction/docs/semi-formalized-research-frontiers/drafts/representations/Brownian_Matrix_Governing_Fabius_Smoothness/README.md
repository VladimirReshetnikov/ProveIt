# The Brownian Matrix Governing Fabius Smoothness

**Sharp anisotropic Fourier envelopes, mixed derivative growth, and a signed resonance**

Research continuation of the ProveIt common-digit Fabius project, prepared
29 September 2026 for Vladimir Reshetnikov.

## Read first

`article.pdf` is the complete 21-page article. `article.tex` is its editable,
LaTeX source. The archive includes its generated table input, and the
bibliography is embedded in the source.
The article gives full analytic proofs, nine proposed research questions,
worked examples, a formalization roadmap, and explicit (unoptimized) constants.

This is an **unrefereed research draft**, not a Lean-checked development.
No claim of exhaustive historical priority is made. The exact finite checks
and numerical experiments supplement, and do not replace, the proofs.

## Main result

Let

    Y_j = sum_{k >= 0} q_j^k V_k,   V_k independent Uniform[-1,1],

where all coordinates use the same digits, 0 < |q_j| < 1, and the moduli
|q_j| are pairwise distinct. Put lambda_j = -log|q_j| and
M_ij = min(lambda_i, lambda_j). If f is the joint density, then

    log ||partial^alpha f||_Lp = (alpha^T M alpha)/2 + O(|alpha| + 1).

The error is uniform over all multi-indices alpha and all 1 <= p <= infinity
for each fixed parameter vector. Equivalently, the norm is bounded above and
below by exp(alpha^T M alpha / 2), up to factors exponential in total order.

The proof establishes a uniform Fourier envelope controlled by

    H(s) = integral_0^infinity max(0, s_j - lambda_j u : 1 <= j <= d) du,

and the exact positive-orthant conjugacy

    sup_{s >= 0} [a.s - H(s)] = a^T M a / 2,   attained at s = M a.

Averaging log absolute sinc factors produces the matching lower envelope
without assuming independence between the factors. Distinct moduli make
cancellation significant at only a uniformly bounded number of digit indices.

## Further proved results

* A sharp ray-window envelope, with a matching lower bound on any prescribed
  fixed fraction less than one of each window. This settles a precise version
  of the leading-coefficient portion of the source's `conj:ray-decay`.
* An exact directional derivative spectrum and reciprocal convolution-power law.
* Quantitative boundary flatness and derivative-aware Fourier truncation bounds.
* A signed resonance: at (r,-r), the leading mixed-derivative cost is
  (-log r)(alpha_1+alpha_2)^2, twice the naive repeated-modulus extension.
* Two noncommuting limits: the high-order coefficient for partial_1^n at
  (r,-r exp(-epsilon)) tends to (-log r)/2 when order tends to infinity first,
  and to -log r when epsilon tends to zero first.

The proposed periodic/quasiperiodic Fourier remainder, local non-Gevrey
behavior on every open set, matching boundary lower bounds, and uniform
near-resonance crossover formulas remain research questions.

## Files

- `article.tex`, `article.pdf`: source and rendered article.
- `code/verify.py`: exact rational tests and high-precision diagnostics.
- `data/box_diagnostics.csv`: five families of logarithmic boxes.
- `data/ray_diagnostics.csv`: eight ray-window cases.
- `data/numerical_table.tex`: generated table used in the article.
- `data/verification_report.json`: versions, precision, counts, and outcomes.
- `PROVENANCE.md`: inspected repository snapshot, source labels, and scope.
- `VALIDATION.md`: mathematical/computational and PDF validation boundaries.
- `requirements.txt`: Python dependency for reproducing the experiments.

## Reproduce the checks

Python 3.10 or later is expected. The recorded run used Python 3.13.5 and
mpmath 1.3.0. From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py
```

Run without Python's `-O` option: the script explicitly requires assertions
to stay enabled. It runs 8,601 exact rational/parity assertions and then
96 deterministic pseudorandom samples per logarithmic-box or ray-window case
at 160 decimal digits. Seeds are fixed in the script. It regenerates all
files under `data/`.

The omitted logarithmic product tail has an analytic bound; the numerical
values of that bound and the other outputs are not interval enclosures of
floating-point rounding error. These calculations are diagnostics, not
computer-assisted certificates of the analytic theorems.

## Rebuild the PDF

The supplied data are sufficient for PDF building; running Python again is
optional. Use a TeX installation with Libertinus and the packages listed
in the preamble: AMS math/theorem packages, mathtools, geometry, microtype,
booktabs, array, longtable, enumitem, TikZ, fancyhdr, xcolor, tcolorbox,
hyperref, and cleveref.

Run three serial passes from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

No external images, bibliography downloads, or font files are bundled or
needed as downloaded assets. TikZ draws the envelope diagram from the source.
The supplied PDF was compiled with pdfTeX 1.40.26 and checked by rendering.
