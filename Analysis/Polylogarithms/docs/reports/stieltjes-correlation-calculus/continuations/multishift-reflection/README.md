# Contact-Complete Multishift Lerch Reflection

Research continuation for Vladimir Reshetnikov's ProveIt programme, 10 October 2026.

**Read `article.pdf` (23 pages).** Its source `article.tex` is self-contained and builds without a repository checkout. The report develops exact identities and supplies ordinary mathematical proofs, rather than inferring identities from numerical residuals.

## Principal contributions

The report constructs an explicit horizontal-cut completion for independent complex shifts, continuous depth, and independent entire spectral orders. It includes merged-cut and simultaneous-collision rules, all-index ordinary logarithmic moments, the cubic overlap correction, a convergent Stirling-to-Stieltjes compiler, balanced harmonic log-ratio identities, integer Hermite reflection, centered half residues, and every local spectral contact coefficient.

A second development gives finite Bell formulas for all spectral derivatives at both centered resonance lattices. These retain the generalized alternating-Hurwitz derivatives that cannot be inferred from the discrete value formulas alone. Consequences include entire-order Gamma–polylogarithm identities, explicit Stieltjes-valued order derivatives, polygamma weights, and anchored primitives through integration resonances.

The exact connection is to **Q4 and Q8 in the incoming Continuous-Depth Lerch Calculus report**. These questions are answered as representation and branch-completion problems in the domains stated in the article. This is not a claim of finite arithmetic reduction of all retained spectral constants.

## Proof and attribution boundaries

The classical Gamma transform, the one-shift Johansson–Blagouchine hyperbolic Stieltjes integral, the prior continuous-depth family, and the existing single-anchor expansion are credited as inputs. No global novelty or arithmetic-independence claim is made. No false source theorem was identified in the inspected portions; explicit counterexamples diagnose invalid extensions instead.

**The separate Gaussian S6 and revised S8 candidates remain unresolved.** There is no Lean or other proof-assistant formalization. Not every incoming archive was fully inspected; see `SOURCE_AUDIT.md`.

## Executed verification

The exact suite passed **490 assertions, including three negative controls**. Each numerical run, at **45 and 60 working decimal digits**, passed **77 positive comparisons and three negative controls**. The largest normalized positive residuals were approximately **5.185e-31** and **7.510e-41**.

These are floating-point diagnostics, **not certified interval enclosures**. Finite truncations and quadrature cutoffs are recorded. The infinite identities are established by the article's analytic proofs. The numerical suite compares independently constructed contour, cut, series, and special-function representations.

```sh
python -m pip install -r requirements.txt
python code/verify_exact.py
python code/verify_numeric.py --dps 45
python code/verify_numeric.py --dps 60
python code/build.py
python code/inspect_pdf.py
```

A normal TeX Live installation with pdfLaTeX, Latin Modern, AMS packages, geometry, microtype, enumitem, xurl, hyperref, and fancyhdr is required for the PDF build. No font files are distributed.

## Package map

`article.tex` and `article.pdf` are the main deliverables. `code/` contains the verification implementation and build/inspection scripts. `data/` retains exact and numerical results, build and visual-review records, and source provenance. `integration/` contains a proposed additive manuscript insertion and claim ledger. `SHA256SUMS` hashes every distributed file other than itself.

The suggested destination is `Analysis/Polylogarithms/docs/reports/multishift-lerch-reflection/`. **No repository files were edited, committed, uploaded, or overwritten.** The canonical manuscript volumes were not rebuilt. Apply the repository's authorship and licensing conventions during integration.
