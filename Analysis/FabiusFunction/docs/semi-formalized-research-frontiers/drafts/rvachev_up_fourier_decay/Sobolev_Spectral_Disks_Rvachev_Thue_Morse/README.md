# From Analytic Spectral Collapse to Sobolev Spectral Disks

**Exact regularity thresholds and sharp endpoint laws for Rvachev–Thue–Morse transfer operators**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026
(Pacific time). The compiled article has 24 A4 pages (23 as delivered; the
editorial notes of 2026-09-29 add one).

## Main conclusions

The article answers the periodic Sobolev portion of the explicit “Spectra at
finite smoothness” research question in ProveIt's spectral-collapse manuscript.
It also proves the corresponding interval result at every nonnegative integer
Sobolev order.

* Under a stated positive square-mask eigenfunction hypothesis, an integer-dilation
  transfer operator with a trigonometric polynomial mask has a complete spectrum
  equal to an exact essential disk together with the spectrum of a finite Fourier
  matrix. All exterior generalized eigenspaces lie in the finite band.
* The positivity hypothesis is proved for all even sine powers and every integer
  dilation. For the dyadic quadratic sine mask, the disk radius on H^{s,beta} is
  2^{-s} sqrt(1+sqrt(17))/4. The eigenvalues 1/2 and -1/4 are isolated exactly above
  s0 = 0.1785093184... and s1 = 1.1785093184..., respectively.
* An exact Fourier-cutoff identity connects the leading Thue–Morse correlation
  functional to the subleading Stern-polynomial functional B_k(-2). Exact
  quadratic energies give their sharp continuity thresholds.
* At the subleading critical index s1, a logarithmic Sobolev exponent beta > 1/2
  yields a sharp scalar two-term remainder of order
  4^{-n}(1+n)^{1/2-beta}. A matching operator-norm little-oh remainder is impossible.

The article supplies full arguments, precise hypotheses, ten further research
questions, provenance, bibliography, and a staged formalization plan.

## Files

- `article.tex`: self-contained LaTeX source, including bibliography.
- `article.pdf`: compiled, visually inspected article (rebuilt 2026-09-29).
- `verify.py`: exact finite checks; Python standard library only.
- `verification.json`, `verification.log`: executed verification results; the
  log is the program's console output (the same JSON without `energy_data`).
- `provenance.json`: repository pin and source/claim boundaries.
- `BUILD_REPORT.md`: build and validation receipt.
- `Makefile`: reproducible PDF and verification commands.
- The submitted `CHECKSUMS.sha256` was verified in full (9/9) on filing (batch 57 of `docs/incoming/`) and not kept; the delivered archive remains in the repository history (see `docs/incoming/README.md`, batch 57 row).

## Reproduce the checks

Python 3.10 or later is sufficient; the executed run used Python 3.13.5.
No third-party Python packages are required.

```sh
py verify.py
```

This writes `rerun/verification.json` beside the program (another path with
`--output`); `make verify` writes `rerun/verification.json` and
`rerun/verification.log`. The recorded run is `verification.json` and
`verification.log`; only an explicit `--output verification.json` run from
this directory overwrites it.

The default run checks levels 0 through 12, reaching absolute frequency 4096.
It passed 16,395 cutoff coefficient checks, 24,579 dual-functional checks,
89,014 finite-band cases, 52 energy recurrences, 26 closed-energy identities,
5 positive-eigenfunction coordinates, and 2 characteristic polynomials.
Every mathematical comparison uses integers, fractions, or the exact field
Q(sqrt(17)). Explicit exceptions enforce checks even under Python `-O`.

These finite checks supplement the general proofs. They do not establish an
infinite-dimensional spectrum by numerical sampling.

## Rebuild the PDF

Use a LaTeX installation supplying the standard packages in the preamble of
`article.tex` (including Latin Modern, AMS mathematics, geometry, microtype,
fancyhdr, hyperref, and cleveref).

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `make pdf`. The bibliography is internal; no BibTeX step,
external figure, font file, or network access is required. PDF bytes can differ
on rebuild because of timestamps and TeX versions.

## Scope and status

Immutable comparison commit:
`b2aed2d23125006c48d63fc97aef0d64b67becb1`.

The supplied results are conventional mathematical proofs in an unrefereed
research manuscript. No Lean code was supplied or built, and the Python program
and runtime were not formally verified. Global literature priority is not
established. The antecedent analytic spectrum, previously certified RMS constants,
and the classical sequences are credited rather than claimed as discoveries.

The paper does not resolve the Hölder/C^r spectrum, general fractional interval
spaces, or the full decomposition of the interior Sobolev disk into point,
continuous, and residual spectra. No repository files were changed.

## Editorial amendments (ProveIt, 2026-09-29)

Made in the editorial pass after batch 57 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-29)`, every change to the program and `Makefile`
`ed. (2026-09-29)`. The byline "OpenAI ChatGPT" is kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-29)" is defined in the preamble. A note at the end of Section 1.2
  records the repository results the article re-derives without citing
  them. Part I of `../../thue-morse/Thue_Morse_Frontier_Deductions/` (filed
  2026-09-05) already proves, for the same Riesz product and sequences, the
  cutoff identity with `a_k = B_k(-2)` (its `bc:thm:boundary`,
  `bc:eq:Stern-identification`), the tail formula (`bc:thm:distribution`),
  the energy recurrences and closed forms (`bc:prop:energies`,
  `bc:cor:energy-closed`, with a trapezoidal endpoint weight), the exponents
  `s_0 = sigma`, `s_1 = s_*` (`bc:eq:exponents`), the unweighted (`beta = 0`)
  thresholds (`bc:thm:regularity`) and remainder rates in `H^(-s)`; it
  credits the growth rate `1 + sqrt(17)` to Zaks, Pikovsky and Kurths. The
  operator form of the cutoff identity is the finite-mode reduction
  `prop:finite-mode` of the predecessor `../Spectral_Collapse_Alternating_RMS/`.
  New in this article are the logarithmic refinement, the two-sided
  remainder laws, the critical scalar/operator separation and the
  operator-spectral classification. The same note names the uncited Lean
  theorems: the eigen-identities are `Fabius.rms_transfer_const_eigen`,
  `Fabius.rms_transfer_sin_eigen`, `Fabius.rms_transfer_one_add_cos_eigen`,
  `Fabius.rms_transfer_cos_even_mode` and `Fabius.rms_transfer_sin_even_mode`
  (`Analysis/FabiusFunction/Lean/FabiusFunction/RMSTransferEigenfunctions.lean`),
  and the recursion for `eta` is that of `Fabius.limitingAutocorrelation`
  (`ThueMorseAutocorrelationLimit.lean`). A second note, after Question 12.9
  (Hoelder and `C^r` spaces), records that the rewrite
  `../Rvachev_Up_Fourier_Decay-2/` imports a Ruelle-Perron-Frobenius spectral
  gap on `C^alpha[0,1]`, which concerns sup-norm Hoelder spaces and does not
  conflict with Theorem 6.1; the question stays open. The hypothesis display
  `(P)` is set with `equation*`, because the numbered environment gave
  hyperref a duplicate destination `equation.2.5` (also in the delivered
  build); its tag and references are unchanged. The verification paragraph
  of Section 11 gives the new default command and output.
- The article also settles, on the Sobolev spaces `H^(s,beta)` with
  `s > s_1`, the canonical synthesis's statement that `-1/4` has not been
  shown to be the second spectral value; on `L^2` and `H^1` it is not
  isolated. The canonical text is unchanged.
- Reciprocal notes now stand under the questions "Spectra at finite
  smoothness" and "Arithmetic and regularity of the correction functional"
  of `../Spectral_Collapse_Alternating_RMS/article.tex`.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX 26.2 pdfTeX 1.40.29): 24 pages (23 as delivered),
  523,816 bytes; no error, undefined reference, duplicate destination or
  overfull box; no Type 3 font. The pages carrying the notes were rendered
  and inspected. `BUILD_REPORT.md` is the delivered build receipt and
  describes the 23-page PDF.
- `verify.py`: the default `--output` is now `rerun/verification.json` beside
  the program instead of `./verification.json`, and the JSON is written with
  LF line endings on Windows too. `Makefile`: the `verify` target writes
  `rerun/verification.json` and `rerun/verification.log` instead of the
  recorded files. A rerun of the amended program on a copy (2026-09-29,
  `uv run --no-project --python 3.13.5 python verify.py`, under a second)
  passed and reproduced `verification.json` byte for byte, and its console
  output equals `verification.log` after CRLF-to-LF normalization of the
  Windows console capture.
- `README.md`: the page count, the file list (ledger, log), the reproduction
  command and output location, and this section.
