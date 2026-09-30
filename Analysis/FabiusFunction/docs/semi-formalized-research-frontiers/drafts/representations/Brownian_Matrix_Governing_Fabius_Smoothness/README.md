# The Brownian Matrix Governing Fabius Smoothness

**Sharp anisotropic Fourier envelopes, mixed derivative growth, and a signed resonance**

Research continuation of the ProveIt common-digit Fabius project, prepared
29 September 2026 for Vladimir Reshetnikov.

## Read first

`article.pdf` is the complete 22-page article. `article.tex` is its editable,
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
uv run --no-project --with mpmath==1.3.0 python code/verify.py
```

Run without Python's `-O` option: the script explicitly requires assertions
to stay enabled. It runs 8,601 exact rational/parity assertions and then
96 deterministic pseudorandom samples per logarithmic-box or ray-window case
at 160 decimal digits. Seeds are fixed in the script. It regenerates all
four files of `data/` in `data-rerun/` (or in the directory given by
`--output-dir`); only `--output-dir data` overwrites the recorded files.

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
The delivered PDF was compiled with pdfTeX 1.40.26 and checked by rendering;
the filed PDF is the 2026-09-29 rebuild described below.

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 56 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`, every change to the program `ed. (2026-09-29)`.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. One note, after the paragraph
  that follows the proof of Theorem `thm:rays`, records that the leading
  coefficient of `conj:ray-decay` of
  `../common_digit_fabius_zonoids_frontier_report/` is proved here in the
  window-supremum and relative-measure sense only (its pointwise form away
  from the zero hyperplanes and the periodic/quasiperiodic remainder are not
  claimed); that the scalar identity `eq:upnorm` is machine-checked as
  `Fabius.isGreatest_abs_iteratedDeriv_rvachevUp`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/GlobalBounds.lean`), which
  the article does not cite; and that the envelope area `H` is the function
  `I(a)` of `../Endpoint_Geometry_Common_Digit_Fabius_Laws/`, filed after
  this article's snapshot, whose theorems are different. The title page no
  longer sets a PDF page anchor (it duplicated the destination `page.1`).
  A reciprocal note now stands at `conj:ray-decay` in the zonoid report.
- `article.pdf`: rebuilt from the amended source by the three passes above
  (MiKTeX pdfTeX 1.40.29): 22 pages (21 as delivered), no error, undefined
  reference or citation, duplicate destination, or overfull box (two
  underfull lines inside the note's long paths); the page carrying the note
  was rendered and inspected. `VALIDATION.md` gains a closing paragraph
  saying so.
- `code/verify.py`: new option `--output-dir`, default `data-rerun/`, so a
  plain run no longer overwrites the recorded `data/` (including the table
  that the article inputs); `--output-dir data` regenerates the recorded
  files. The CSV files, the table and the JSON report are now written with
  LF line endings on every operating system (the delivered program wrote
  CRLF CSV files everywhere and CRLF text on Windows).
- `data/box_diagnostics.csv`, `data/ray_diagnostics.csv`: delivered with
  CRLF line endings; normalized to LF on filing (batch 56).
- A rerun of the amended program on a copy (2026-09-29,
  `uv run --no-project --with mpmath==1.3.0 python code/verify.py`,
  Python 3.13.5) reproduced all four files of `data/` byte for byte.
- `README.md`: the page count under "Read first", the command and output
  location under "Reproduce the checks", the PDF sentence under "Rebuild the
  PDF", and this section.
