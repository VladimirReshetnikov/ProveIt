# Sharp C^r Spectral Disks for the Rvachev--Thue--Morse Transfer Operator

Research package prepared for Vladimir Reshetnikov on 30 September 2026
(Pacific time), relative to ProveIt commit
`ffddaa8b9c89e7bf027e1442cc6216bb010906d0`.

## Main result

For the ProveIt-normalized operator

\[
(\mathcal L f)(x)=\frac12\left[
\sin^2(\pi x/2)f(x/2)+\cos^2(\pi x/2)f((x+1)/2)
\right],
\]

the article proves, on both periodic `C^r(T)` and interval `C^r([0,1])`,

\[
\sigma_{\mathrm{ess}}(\mathcal L)=\overline D(0,2^{-r-1}),\qquad
\sigma(\mathcal L)=\overline D(0,2^{-r-1})\cup\{1/2,-1/4\}.
\]

Every point in the open disk has infinite geometric multiplicity. The paper
also proves a universal exact essential-disk theorem for smooth dyadic Markov
weights, an endpoint-jet spectral ladder on interval spaces, smoothness of all
exterior generalized eigenvectors, the exact three-mode resonance block, and
optimal compact-approximation lower bounds.

## Files

- `article.tex` - self-contained LaTeX source with internal bibliography.
- `article.pdf` - compiled A4 research manuscript (17 pages since the
  editorial pass below; 16 as delivered).
- `verify.py` - standard-library exact finite checks.
- `verification.json` - recorded verification output.
- `BUILD_REPORT.md` - build, preflight, and inspection receipt of the
  delivered files (see the editorial amendments below).

## Reproduce the finite checks

```sh
python verify.py
```

(On the ProveIt machine use `py` rather than bare `python`.) Since the
editorial pass below the program writes `verification.rerun.json` unless
`--output` is given; the delivered instruction was
`python verify.py --output verification.json`, which overwrites the recorded
`verification.json`, so run it that way only on a copy.

The recorded run passed 361 exact assertions: the three-mode matrix and
characteristic polynomial, finite descendant-frequency bounds, endpoint-jet
matrices through order 12, sine-mask nilpotence, and all threshold scalings.
These checks supplement, but do not replace, the infinite-dimensional proofs.

## Rebuild the PDF

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

No BibTeX step, external figure, network access, or nonstandard font file is
required.

## Status and claim boundary

This is an unrefereed conventional mathematical manuscript resolving a
specific repository gap relative to the pinned source corpus. No new Lean code
was supplied or built. The article does not assert global first-publication
priority and does not settle noninteger Hoelder/Zygmund spaces.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 69 and 70 of `docs/incoming/` (see
`docs/incoming/README.md`); every change to the source is marked
`% ed. (2026-09-30)`, every change to the program `ed. (2026-09-30)`. The
title-page byline and `pdfauthor` entry ("OpenAI; research manuscript
prepared for Vladimir Reshetnikov") and the bibliography's attribution of the
Sobolev article to "OpenAI ChatGPT" are kept as delivered.

- `article.tex`: an unnumbered environment "Editorial note (ProveIt,
  2026-09-30)" is defined in the preamble (the theorem counter is
  unchanged). One note, after the three-mode matrix (Section 6.2), names the
  Lean declarations that the Lean plan and the provenance table mention only
  by file: in `Analysis/FabiusFunction/Lean/FabiusFunction/RMSTransferEigenfunctions.lean`,
  `Fabius.rms_transfer_const_eigen` (`L 1 = 1/2`),
  `Fabius.rms_transfer_sin_eigen` (`L sin(2 pi x) = -1/4 sin(2 pi x)`) and
  `Fabius.rms_transfer_one_add_cos_eigen`
  (`L (1 + 3 cos(2 pi x)) = -1/4 (1 + 3 cos(2 pi x))`, three times the
  second eigenvector of the theorem), all pointwise identities, and
  `Fabius.rms_transfer_cos_even_mode` and `Fabius.rms_transfer_sin_even_mode`,
  the even-frequency case of the Fourier rule (37); no spectral statement of
  the article is formalized.
- Reciprocal notes now stand under "Spectra at finite smoothness" in
  `../Spectral_Collapse_Alternating_RMS/article.tex` and under
  "Finite-smoothness spaces outside the Hilbert scale" in
  `../Sobolev_Spectral_Disks_Rvachev_Thue_Morse/article.tex`, whose integer
  `C^r` parts this article answers; noninteger Hoelder spaces stay open in
  both.
- `article.pdf`: rebuilt from the amended source with the three `pdflatex`
  passes above (MiKTeX 26.2, pdfTeX 1.40.29): 17 pages (16 as delivered; the
  note adds one), with no error, undefined reference, multiply defined
  label, duplicate destination, overfull or underfull box; every font
  embedded, no Type 3 font. The page carrying the note was rendered and
  inspected.
- `verify.py`: the default `--output` is now `verification.rerun.json`, so
  a plain run no longer overwrites the recorded `verification.json`, and the
  JSON is written with LF line endings on every platform (CRLF on Windows
  before). A rerun of the amended program on a copy (2026-09-30,
  `py verify.py`, Python 3.14.4, standard library, under a second) passed
  all 361 assertions; its output equals `verification.json` except the
  recorded Python version (3.14.4 for 3.13.5).
- `BUILD_REPORT.md` is kept as delivered: it describes the delivered build
  (16 pages, 493,704 bytes) and its checksums are those of the delivered
  `article.tex`, `article.pdf` and `verify.py`, which have since changed (the
  delivered files remain in the repository history); its "Executed command"
  is the overwriting form discussed under "Reproduce the finite checks".
- `README.md`: the page count and `BUILD_REPORT.md` line under "Files", the
  reproduction command, and this section.
