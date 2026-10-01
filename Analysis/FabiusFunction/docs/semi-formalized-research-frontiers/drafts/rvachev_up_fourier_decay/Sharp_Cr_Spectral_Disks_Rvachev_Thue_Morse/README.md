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
- `article.pdf` - compiled 16-page A4 research manuscript.
- `verify.py` - standard-library exact finite checks.
- `verification.json` - recorded verification output.
- `BUILD_REPORT.md` - build, preflight, and inspection receipt.

## Reproduce the finite checks

```sh
python verify.py --output verification.json
```

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
