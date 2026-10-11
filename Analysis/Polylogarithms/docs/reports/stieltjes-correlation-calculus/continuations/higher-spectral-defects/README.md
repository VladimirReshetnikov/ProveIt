# Beta Polarization of Higher Spectral Defects

Research continuation for ProveIt / Analysis / Polylogarithms, 11 October 2026.

**Article:** `article.pdf` (25 pages); complete, standalone source: `article.tex`.
No repository files were changed. The archive is a proposed integration package.

## Results

The article proves an endpoint-subtracted beta identity giving every spectral
factorization defect as finite ordinary integrals of lower-order Hurwitz jets.
It also supplies an independent global harmonic–Stieltjes coefficient formula.
The second defect is a Gamma–Hurwitz chord minus an explicit odd-weight
polynomial; its universal vanishing criterion is `W = 0`, not even parity.

Applications include second jets at every nonpositive spectral integer with
finite polylogarithmic integrands; pairwise covariance formulas for any number
of quadratic factors with an even polynomial weight; complete coincident-mass
expansions with finite polygamma coefficients; and fully anchored shift and
normalized all-order mass antiderivatives.

These address the explicit-representation content of Section 7.6 Questions 2
and 7 in the byte-identified quadratic-spectrum predecessor. The finite-function-
algebra/minimality component of Question 1 is **not** settled. No global priority,
period independence, Gaussian S6 or revised S8 evaluation, proof-assistant
formalization, or interval certification is claimed.

## Build and checks

A TeX Live installation with `latexmk` builds the PDF:

```sh
make pdf
```

Python 3 with the pinned packages in `requirements.txt` runs the checks:

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py
```

The numerical suite is slower than the exact suite. An interrupted numerical
run can be resumed at the same precision and profile:

```sh
python code/verify_numeric.py --resume
```

For a smaller diagnostic selection, use `--quick`; this writes a separate
results file and must not be confused with the complete suite. `--dps` changes
working precision, not the number of series terms or quadrature nodes; raising
precision alone is not a validated accuracy guarantee.

## Executed verification

- **432 exact assertions:** duplication/double-zero polynomials; harmonic
  corrections; local beta moments; confluent coefficients; primitive algebra;
  normalized mass germs; formal Stieltjes-pole coefficient extraction.
- **87 numerical comparisons at 35 decimal-digit working precision**, all
  accepted at scaled-residual threshold `1e-23`. Largest recorded residual:
  `9.17825989122e-35`. Checks were completed in staged tool invocations.
- The PDF was compiled without unresolved references or overfull boxes. Every
  page was rendered for layout inspection; key formula pages were also
  inspected at readable resolution.

Residuals are not rigorous error bounds. Some comparison routes share mpmath's
Hurwitz-zeta implementation. The proofs are in the article; the finite checks
and floating-point diagnostics do not replace them.

## Contents

`code/spectral_defects.py` contains reusable evaluation routines.
`results/` contains exact and numerical records and PDF validation metadata.
`notes/` contains source identity, correction guards, and a claim ledger.
`integration/` contains a compact manuscript fragment and an editorial note.
`SHA256SUMS` covers the delivered files except itself.

Suggested new report destination:

```
Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/higher-spectral-defects/
```

The classical beta identity, Gamma/Hurwitz ingredients, and predecessor's
first-jet formulas retain their attribution. The source audit is targeted,
not an exhaustive audit of every repository report.
