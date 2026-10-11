# Ordered Hurwitz Germs at Every Depth

**Harmonic renormalization, directional Stieltjes constants, and
polylogarithmic Mellin identities**

Research continuation prepared for the ProveIt project, local session
date 10 October 2026. The observed repository commit and independently
identified source blobs are recorded in `provenance/sources.json`.

## Main results

The article constructs a compatible holomorphic remainder at every
ordered depth near the all-one point. The exact polar decomposition,
its normally convergent construction, and a finite mixed-coefficient
recursion appear in Sections 3–4. Sections 5–6 identify Gamma-generated
regular values and prove agreement with harmonic cutoff constants and
a specified stuffle-preserving regularization. Section 7 gives every
ordered depth-three ray and an explicit nonsymmetric Stieltjes
coordinate. Section 8 handles nonlinear and arbitrary finite-order
tangential curves not contained in a polar divisor.

Sections 9–10 turn the regular jets into ordinary Mellin integrals of
polylogarithms and their order derivatives. An all-depth hierarchy is
summed both in an elementary generating identity at a=1 and in a
Hurwitz-shifted hypergeometric identity on Re(z)>-1. The latter has a
direct incomplete-beta proof independent of the nested-sum construction.
Section 11 supplies shift transport and exact polygamma antiderivatives.
The final sections contain audit findings, reproducibility, and nine
further research questions.

## Files

- `article.pdf` and standalone `article.tex`: full statements, proofs,
  examples, references, and research questions.
- `integration/`: a namespaced manuscript entry-point fragment, a
  compile smoke test, and exact source-question/status mapping.
- `verification/`: executable symbolic and numerical checks, actual
  result files, a verification summary, and integrity checker.
- `provenance/`: observed commit, inspected source blobs, primary
  references, and the six incoming archive metadata records.
- `CORRECTIONS.md`: integration safeguards and explicit audit boundary.
- `SHA256SUMS`: byte hashes for the delivered files other than itself.

## Build and replay

```sh
python -m pip install -r requirements.txt
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
python verification/verify.py --part all
python verification/check_manifest.py
```

The hash check should be run on an unchanged extracted package. Rebuilding
PDFs or rerunning checks can change metadata, timing fields, and hashes.
No repository files are needed to compile the article. A normal TeX Live
installation with pdfLaTeX, latexmk, Latin Modern, amsmath, amsthm,
mathtools, microtype, hyperref, and the other standard listed packages is
sufficient. The numerical environment actually tested is recorded in the
results files; no claim of latest library versions is made.

## Scope and priority

The primary source targets are questions 1–3 and the coordinate-construction
part of question 6 in `resonant-jets-and-shifts/sections/08-audit-research.tex`.
The construction settles the specified ordered-germ, harmonic-subtraction,
and off-divisor path tasks; it does not prove arithmetic reduction of the
nonsymmetric coordinate or settle the Gaussian S6/S8 evaluations.

Classical Euler–Zagier continuation and regularization retain their
attribution, including Matsumoto–Onozuka–Wakabayashi and Guo–Zhang.
No exhaustive novelty claim is made across the literature or every
incoming archive. The six incoming ZIPs were inventoried by metadata,
not exhaustively unpacked. No remote repository files were modified.
All analytic results are proved in the article; they are not
proof-assistant formalizations. Numerical comparisons are diagnostics,
not interval certificates.
