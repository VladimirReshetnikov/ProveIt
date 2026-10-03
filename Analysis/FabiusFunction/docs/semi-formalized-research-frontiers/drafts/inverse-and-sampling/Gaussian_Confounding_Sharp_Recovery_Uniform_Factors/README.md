# Gaussian Confounding and Sharp Recovery of Uniform Convolution Factors

**Shifted power sums, minimax estimation, and detection above a Fabius–Rvachev background**  
Research report prepared for Vladimir Reshetnikov · 29 September 2026

## Result

The observation model is

    X = Z + a_1 U_1 + ... + a_m U_m + sqrt(v) G,

where Z is a known bounded random variable, the U_i are independent uniforms
on [-1,1], G is an independent standard normal, and
0 <= a_1 <= ... <= a_m <= 1. The capacity m is fixed and known; zero slots
represent absent factors. Either v is fixed and known, or v ranges over a
fixed nondegenerate compact interval bounded away from zero.

For independent samples of size n, the article proves matching minimax upper
and lower bounds in expected ordered maximum error:

| Quantity | Optimal rate |
|---|---|
| Half-lengths, known Gaussian variance | n^(-1/(4m)) |
| Half-lengths, unknown Gaussian variance | n^(-1/(4m+4)) |
| Unknown Gaussian variance itself | n^(-1/(2m+2)) |

Detection of at least one factor is different: its critical half-length is
n^(-1/8) with unknown variance and n^(-1/4) with known variance, independent
of m. Consistent testing requires separation by a diverging multiple of the
critical scale; below that scale the testing risk tends to one.

The main algebraic theorem is the sharp shifted-moment inverse inequality

    max_i |x_i-y_i| <= 8 [max_{r+1<=k<=r+m} |sum_i x_i^k-sum_i y_i^k|]^(1/(m+r))

for ordered nonnegative nodes in [0,1] and integer r >= 0. The exponent, not
the numerical constant 8, is proved optimal. Exact moment-preserving curves
and weighted Gaussian likelihood expansions yield the statistical lower bounds.

The Rvachev up random variable sum_{j>=1} 2^(-j) U_j is an admissible known
background. The new theorem does not assert the same sampling rates for the
unsmoothed up-law model.

## Files

- `article.pdf`: the 19-page article, including eight further research questions.
- `article.tex`: self-contained LaTeX source, with bibliography embedded.
- `verify_results.py`: exact finite algebraic checks and a Fourier diagnostic.
- `artifacts/verification_results.json`: detailed checks and rational root certificates.
- `artifacts/verification_summary.txt`: recorded successful check summary.
- `SOURCE_AUDIT.md`: repository pin, source scope, primary literature, novelty boundary.
- `CLAIM_LEDGER.md`: proof locations and validation status of the main assertions.
- `BUILD_VALIDATION.md`: PDF build and rendering checks.
- `requirements.txt`: versions used for the supporting program.
- `Makefile`: PDF and verification commands.
- `SHA256SUMS.txt`: final payload checksums, excluding this checksum file itself.

## Reproduce the checks

Python 3.10 or newer is recommended (the source uses modern type annotations).
Install the dependencies and run:

```sh
python -m pip install -r requirements.txt
python verify_results.py
```

The script writes its output relative to its own directory and can be invoked
from any working directory. It verifies 7,000 rational inequality instances,
40 exact tangent identities, eight symbolic moment flows with rational
all-positive-root certificates, and the explicit two-factor coefficients.
The 80-digit Fourier computation is a diagnostic, not interval arithmetic.
Do not run Python with `-O`, which disables the assertions used by these checks.

## Rebuild the PDF

Use a TeX installation containing `libertinus`, `amsmath`, `amsthm`, `mathtools`,
`microtype`, `booktabs`, `tabularx`, `enumitem`, `xurl`, `hyperref`, and `fancyhdr`.
No BibTeX step, shell escape, network access, or external image is needed.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively use `make pdf` and `make check`. Generated TeX auxiliary files
are not included in the delivered archive. Font files are not distributed.

## Claim boundary

The article supplies conventional mathematical proofs for the stated model.
These proofs have not been independently refereed or checked in Lean/Rocq.
Finite exact checks do not prove universal assertions. The research-question
section contains explicitly labeled conjectural and open extensions.

The statistical experiment includes strictly positive Gaussian smoothing,
fixed capacity, known bounded background, and equal unit multiplicities of
uniform factors. Constants are not uniform as m grows or the Gaussian
variance tends to zero. The finite-grid estimator establishes attainable
rates; an efficient general-purpose numerical solver is not supplied.

The selected extension was compared with ProveIt at commit
`c130dba623c420551d90db41dae7b3d9cff72dfd`. The preceding finite-factor report
is credited, not presented as a new discovery. No claim of worldwide
publication priority or resolution of an unrelated named conjecture is made.
No repository files were modified.

## Editorial amendments (ProveIt, 2026-09-29)

In the editorial pass after batch 54 of the repository-level `docs/incoming/`
drop zone (see `docs/incoming/README.md`), a later package of this tree was
found to take up two of its research questions. The article gains reciprocal notes; its
mathematical text is unchanged.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style.
- `article.tex`: after the research question "Classify all local strata with
  unknown variance", a note records that
  `../Local_Minimax_Geometry_Uniform_Factors/` (filed 2026-09-29,
  unreviewed; its Corollary `cor:joint`) proves the candidate denominator
  `eq:localconjecture` at the level of minimax sampling rates
  `n^(-1/(2M))`, for Gaussian variance unknown in a compact interval away
  from zero; the pairwise Hellinger-modulus form is not stated there. The
  note adds that the same article's grid moment estimator attains the local
  rates on every fixed stratum without being told the stratum (bearing on
  "Adapt to collision and vanishing patterns"), is not efficient, and leaves
  honest adaptive confidence sets open. `CLAIM_LEDGER.md` is the delivered
  record and still marks the mixed-stratum formula CONJECTURAL.
- `article.tex`: after the research question "Growing capacity and the
  infinite-factor transition", a note records that
  `../Gaussian_Dust_Christoffel_Recovery_Uniform_Factors/` (filed
  2026-09-29, unreviewed) treats square-summable infinite spectra for the
  Gaussian variance alone (exact minimax risk `V/2`; uniform consistency
  exactly under uniformly vanishing squared-scale tails); growing capacity
  and the recovery of the half-lengths are not treated there. Both notes are
  marked `% ed.`.
- `article.pdf`: rebuilt with three `pdflatex -interaction=nonstopmode -halt-on-error article.tex` passes (MiKTeX pdfTeX): 19 pages, as before, 651,180
  bytes; no error, undefined reference, rerun request, duplicate
  destination or overfull box; no Type 3 font.
- `SHA256SUMS.txt`, listed under Files, is no longer in the package; it was
  retired when the package was filed.
