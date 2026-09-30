# From Analytic Spectral Collapse to Sobolev Spectral Disks

**Exact regularity thresholds and sharp endpoint laws for Rvachev–Thue–Morse transfer operators**

Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026
(Pacific time). The compiled article has 23 A4 pages.

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
- `article.pdf`: compiled, visually inspected 23-page article.
- `verify.py`: exact finite checks; Python standard library only.
- `verification.json`, `verification.log`: executed verification results.
- `provenance.json`: repository pin and source/claim boundaries.
- `BUILD_REPORT.md`: build and validation receipt.
- `Makefile`: reproducible PDF and verification commands.
- `CHECKSUMS.sha256`: hashes of the delivered files except itself.

## Reproduce the checks

Python 3.10 or later is sufficient; the executed run used Python 3.13.5.
No third-party Python packages are required.

```sh
python verify.py --output verification.json
```

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
