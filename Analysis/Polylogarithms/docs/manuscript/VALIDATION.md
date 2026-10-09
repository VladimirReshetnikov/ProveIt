# Validation of the unified manuscript

Completed October 9, 2026. The reading artifact is
[`polylogarithms.pdf`](polylogarithms.pdf): **100 pages**, ten chapters,
a literature appendix with 94 distinct historical question leads, and one
bibliography of 39 references. The source is
[`polylogarithms.tex`](polylogarithms.tex) with its edited chapter files.

The validated PDF SHA-256 is:

```
2eb68c4f92a44b4422c9b92157779cc4c31d22f5dacec0a1ceb135a67cdeb9d2
```

## Source reconciliation

- All **39** textual source documents are represented in the
  [editorial ledger](EDITORIAL-LEDGER.md).
- All original source digests match [the inventory](source-inventory.json).
- Earlier material is merged through later corrected treatments. Session
  commands for unavailable tools, repetitive abstracts and unsupported
  external claims are not repeated as manuscript mathematics.
- Static checks find no duplicate labels, missing references, missing
  bibliography keys, duplicate bibliography keys or missing TeX inputs.
  See [document-integrity.json](verification/document-integrity.json).
- [source-sha256.json](verification/source-sha256.json) pins the LF-normalized
  manuscript and verification-script contents used for this validation.
  [receipt-integrity.json](verification/receipt-integrity.json) confirms the
  source hashes and that the PDF matches both its build and raster receipts.

## Fresh mathematical checks

The native Wolfram Language battery passes **31/31** focused symbolic and
numerical checks at 70-digit working precision, with a residual gate of
`1e-45`. It covers the corrected rational dilogarithm, interface conventions,
the four even-weight harmonic sums, the rational trigamma DFT grid,
Gaussian mixed weight two, the g51 integral representation, a trig-root gamma
identity, the Lee integral, the log-gamma quarter point and both basic CM
periods. The high-weight `MultiplePolyLog` g51 call initially exceeded its
90-second limit; the recorded successful check evaluates it by an independent
iterated integral. See [wolfram-results.json](verification/wolfram-results.json).

The independent mpmath battery passes **67/67** focused checks at 65 decimal
digits, with gates of `1e-48` (and `1e-43` for numerical high derivatives of
Stieltjes functions). It checks Clausen distribution tables, F(1/q) and
F(2/q) for small denominators, direct Herglotz derivative quadrature,
the harmonic-number master identity, both nonzero and trivial-zero bridge
forms, the *printed* corrected Gamma1(1/3) expression, the negative-polygamma
quarter point, the signed cubic-regulator numerical candidate, all seven
displayed golden ladders at weights 5–9, and all five displayed Gaussian
weight-six double reductions through integral representations.
See [mpmath-results.json](verification/mpmath-results.json).

The independent check also caught an erroneous proposed editorial change to
W(12). The original coefficient was restored and is now derived explicitly:
`W(12) = 11 sqrt(3) Cl2(pi/3)/9`. A failed intermediate proposal is not
retained as an accepted identity.

The new all-order even-weight odd-denominator harmonic-sum theorem is an
analytic proof using a beta-integral generating function. Its first four
cases were also checked numerically. The manuscript corrects gamma
completeness attribution, convergence, word orientation, HPL alphabet
transport, Nielsen signs, Clausen parity, depth/product conventions,
trivial-zero normalization and class-field degrees. It supplies an exact
derivation of the external rational-dilogarithm correction.

## Build and rendered review

- Three serial LuaLaTeX passes all exit successfully.
- The auxiliary/reference state is identical across the final passes.
- The final log has **zero** unresolved references/citations, duplicate-label
  warnings, overfull boxes, missing-glyph diagnostics or rerun requirements.
  See [build-results.json](verification/build-results.json).
- The PDF extraction audit finds no unresolved `??` text or text outside
  page bounds on any of the 100 pages.
- All pages were rasterized and reviewed in seven contact sheets. Full-size
  inspection included the title, chapter openings, golden ladders,
  even-weight proof, Gaussian reductions, CM normalization, expanded
  Stieltjes values, sixth-point derivatives, regulator table, literature
  tables and final bibliography. No clipping, overlap or illegible layout
  defects were found.
  See [pdf-inspection.json](verification/pdf-inspection.json).

## Limits of the evidence

These are focused checks, not a replay of all historical Smithereens
experiments or absent certificate tools. Numerical candidate identities
remain numerical where no proof is given. No unsuccessful relation search
is used as a proof of independence, non-elementarity or minimal depth.
Motivic and formal quotient dimensions are separated from numerical period
dimensions. Rohrlich completeness and Stark regulator predictions retain
their stated conjectural boundaries. No proof-assistant formalization or
remote CI run is claimed.
