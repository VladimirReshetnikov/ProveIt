# Spectral Collapse and Alternating RMS Asymptotics for the Rvachev Up-Function

Research manuscript prepared for Vladimir Reshetnikov, 28 September 2026
(Pacific time). The compiled article has 23 pages.

## Main results

The article addresses the explicitly unresolved spectral/RMS claim in the
canonical Fourier-decay synthesis in the ProveIt repository. On the analytic
Hardy disk space H_R = H^2({z: |z-1/2| < R}), R > 1/2, it proves:

1. The quadratic transfer operator has complete spectrum {0, 1/2, -1/4},
   with nonzero algebraic multiplicities 1 and 2. Both nonzero values are
   semisimple. In particular, the previously exhibited -1/4 eigenvalue is
   genuinely subleading on these specified spaces.
2. The normalized shell RMS R_n satisfies
   R_n^2 = M/2 + (B/6)(-1/2)^n + epsilon_n,
   where the remainder has an explicit square-exponential upper bound.
   Executed integer/rational interval arithmetic certifies
       -0.002907 < B < -0.002898,
       0.021221672 < M < 0.021221677,
       0.10300890 < sqrt(M/2) < 0.10300894.
   An explicit bound proves that every even index n >= 10 is below the
   limiting RMS and every odd index n >= 11 is above it.
3. For every trigonometric polynomial weight w and integer dilation b >= 2,
   the analytic interval transfer determinant factors as
       det(I-z L_{b,w}) = det(I-z A) product_{ell>=1}(1-z w(0)/b^ell).
   Here A is an explicitly defined finite Fourier matrix. When w(0)=0,
   every nonzero generalized eigenspace lies in the finite Fourier band.
   Even sine powers, an exact fourth-moment formula, and a high-dilation
   spectral-collapse result are developed as applications.

See the article for all definitions, hypotheses, normalizations, proofs,
and ten further research questions. Spectrum is function-space dependent;
no identical statement on all continuous or finite-smoothness spaces is
asserted.

## Contents

- `article.tex`, `article.pdf`: editable manuscript and compiled article.
- `certify_integer.py`: primary numerical certificate, requiring only the
  Python standard library. Every mathematical bound uses exact integers or
  rational numbers and explicit elementary-series remainders.
- `integer_certificate.json`, `integer_certificate.log`: executed primary
  certificate, exact rational endpoints, and outward decimal enclosures.
- `certify_constants.py`: independent mpmath.iv cross-check of the same
  finite coefficient reduction.
- `constants_certificate.json`, `constants_certificate.log`: its output.
- `verify_algebra.py`: finite exact symbolic checks, including matrices for
  powers 1 through 5, 80 trace checks, and 512 Fourier-mode checks.
- `algebra_certificate.json`, `algebra_certificate.log`: its output.
- `provenance.json`: immutable repository source and bibliography metadata.
- `requirements.txt`: optional dependencies for the two secondary checks.
- `Makefile`: build and verification commands.
- `CHECKSUMS.sha256`: SHA-256 hashes of the delivered files except itself.

All three supplied verification programs were executed successfully. The
finite computations supplement the general proofs; finite checks alone do
not establish infinite-dimensional spectral statements.

## Reproduce the primary certificate

Python 3.10 or later is required. No third-party Python package is needed.
From this directory run:

```sh
python certify_integer.py --output integer_certificate.json
```

The run used Python 3.13.5 and took approximately 26 seconds in the preparation
environment. Runtime is only a diagnostic; no floating-point timing value
participates in a mathematical assertion. The JSON output records exact
rational bounds. Do not run Python with `-O` or otherwise disable assertions.

The certificate proves its fixed, documented parameter choice. Changing its
truncation parameters or precision requires checking the supporting estimates
and assertions again; it is not a general-purpose validated numerics API.

For the optional independent checks:

```sh
python -m pip install -r requirements.txt
python certify_constants.py --output constants_certificate.json
python verify_algebra.py --output algebra_certificate.json
```

The tested versions are mpmath 1.3.0 and SymPy 1.14.0. `make verify` runs the
primary certificate; `make verify-all` runs all three and captures logs.
Rerunning updates diagnostic runtimes and therefore can change checksums of
output files without changing any mathematical endpoint.

## Rebuild the PDF

A LaTeX installation with the packages named in `article.tex` is required.
The delivered PDF was compiled with pdfTeX 1.40.26 (TeX Live 2025/dev/Debian).
The article has an internal bibliography and no external figure dependencies.

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `make pdf`. PDF bytes may differ between rebuilds because
of engine versions or timestamps; mathematical content should remain the same.
The delivered PDF was rendered and visually inspected. Its final build had no
undefined references or overfull boxes.

## Source and evidence status

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected immutable commit:
`de4ac5ab1438bcbeed58481c4449b593074a1a1f`
Canonical TeX blob:
`aeba04f6c5f2d1eccff67645f773ba71803fa2a7`

The exact path and source-line range identifying the gap are recorded in
`provenance.json` and Appendix A. The source's previously known eigenfunctions
and RMS normalization are credited as antecedents, not new results.

The article provides conventional mathematical proofs and executed
computer-assisted certificates. It is an unrefereed research manuscript;
no new Lean/Rocq proof objects were supplied or built. The Python programs,
interpreter, and standard analytic inputs have not been formally verified
as part of this package. Priority for every generalization in the broader
literature is not asserted. No repository files were modified.

## Editorial amendments (ProveIt, 2026-09-29)

In the editorial pass after batch 57 of the repository-level
`docs/incoming/` drop zone (see `docs/incoming/README.md`), a later package
of this tree was found to answer two of its research questions on the
Sobolev scale. The article gains reciprocal notes; its mathematical text is
unchanged.

- `article.tex`: an unnumbered environment `ednote` ("Editorial note
  (ProveIt, 2026-09-29)") is defined after the last theorem style.
- `article.tex`: after Question 12.2 ("Spectra at finite smoothness"), a
  note records that `../Sobolev_Spectral_Disks_Rvachev_Thue_Morse/` (filed
  2026-09-29, unreviewed) answers the Sobolev part: on the periodic spaces
  `H^(s,beta)` the spectrum of the quadratic operator is the closed disk of
  radius `2^(-s) sqrt(1+sqrt 17)/4` (all essential) together with `1/2` and
  `-1/4`, isolated exactly for `s > s_0 = (1/2) log_2((1+sqrt 17)/4)`
  (about 0.1785) and `s > s_0 + 1` respectively, so `-1/4` is not isolated on
  `L^2` or `H^1`; the same holds on `H^r(0,1)` for integer `r`. Hoelder, `C^r`
  and weighted endpoint spaces are not treated there.
- `article.tex`: after Question 12.9 ("Arithmetic and regularity of the
  correction functional"), a note records that `alpha(k) = B_k(-2)` (Stern
  polynomials at `-2`) and that the functional is continuous on `H^s` of the
  circle exactly for `s > s_0 + 1`, both already in Part I of
  `../../thue-morse/Thue_Morse_Frontier_Deductions/` (filed 2026-09-05, not
  cited here), and that the later Sobolev package adds the logarithmic
  endpoint: on `H^(s_0+1,beta)` it is continuous exactly when `beta > 1/2`.
  Both notes are marked `% ed.`.
- `article.pdf`: rebuilt with `latexmk -pdf -interaction=nonstopmode
  -halt-on-error article.tex` (MiKTeX 26.2 pdfTeX 1.40.29): 23 pages, as delivered,
  508,202 bytes; no error, undefined reference, duplicate destination
  or overfull box; no Type 3 font; the pages carrying the notes were
  rendered and inspected.
- `CHECKSUMS.sha256`, listed under "Contents", was verified (15/15) and
  retired when the package was filed (batch 38 of `docs/incoming/`); the
  delivered archive remains in the repository history.

## Editorial amendments (ProveIt, 2026-09-30)

Made in the editorial pass after batches 69 and 70 of `docs/incoming/` (see
`docs/incoming/README.md`); the change to the source is marked
`% ed. (2026-09-30)`.

- `article.tex`: a second unnumbered environment `ednotelater` ("Editorial
  note (ProveIt, 2026-09-30)") is defined after `ednote`. Under Question
  12.2 ("Spectra at finite smoothness"), after the 2026-09-29 note, a note
  records that the later article
  `../Sharp_Cr_Spectral_Disks_Rvachev_Thue_Morse/` (filed 2026-09-30,
  batch 70, unreviewed) answers the integer `C^r` part: on `C^r` of the
  circle and on `C^r([0,1])` the essential spectrum of `L_2` is the closed
  disk of radius `2^(-r-1)`, every interior point an eigenvalue of infinite
  multiplicity, and the spectrum adds only `1/2` (isolated and simple
  exactly for `r >= 1`; on `C^0` it lies on the boundary of the disk) and
  `-1/4` (isolated, semisimple of multiplicity two, exactly for `r >= 2`);
  unmatched endpoint jets add no spectrum for this mask, and the essential
  disk is proved for every smooth dyadic Markov weight. Noninteger Hoelder
  and weighted endpoint spaces remain open.
- `article.pdf`: rebuilt with three `pdflatex` passes (MiKTeX 26.2, pdfTeX
  1.40.29): 23 pages, as before; no error, undefined reference, duplicate
  destination or overfull box (the two underfull boxes of the previous
  build remain); no Type 3 font; the page carrying the note was rendered and
  inspected.
- `README.md`: this section.
