# A Reflexive Root-Polytope Model for Preorder h-Polynomials

Research manuscript prepared on 20 September 2026.

## Result and status

The manuscript gives a proposed general proof of Conjecture 5.1(c) of
Athanasiadis–Chapoton, *Polytopes and posets associated to preorders*,
arXiv:2605.26916v1. It constructs an n-dimensional reflexive directed root
polytope C_tau whose Ehrhart numerator is the support polynomial h_tau, and
realizes h_tau as the h-polynomial of an n-dimensional simplicial polytope.
Palindromicity and unimodality, Conjecture 5.1(a,b), follow.

The higher-dimensional augmented bipartite root-polytope identity and preorder
duality were already proved by Dai, Hou, Liu, Thawinrak, and Wang in
arXiv:2608.16037v2 (27 August 2026). They are credited as prior results.
The proposed additions are the lower-dimensional model, its exact integer
fibers, and the general simplicial-polytopal realization.

The proof has not been independently refereed or checked by a proof assistant.
The finite checks do not prove the universal result. Absolute publication
priority is not certified. Flag realizability, gamma-positivity, and
real-rootedness are not proved here. See STATUS.md and the article for details.

## Contents

- article.pdf: the complete 17-page mathematical article.
- article.tex: self-contained LaTeX source, including the bibliography.
- build.py: cross-platform pdfLaTeX build script; no external Python packages.
- code/verify.py: exact, standard-library finite verification.
- data/preorders_through_5.csv: all 7,332 labeled preorders through size 5,
  including the empty preorder, and their support coefficients.
- data/verification_results.json: detailed exact results and sample certificate.
- data/verification_log.txt: console transcript of the complete verification.
- data/runtime.txt: observed verification runtime and environment.
- STATUS.md: version-specific literature and claim-status notes.
- PROOF_AUDIT.md: short independent-review checklist and proof dependencies.

## Rebuild the PDF

Python 3.10+ and a TeX distribution with pdfLaTeX are sufficient. Run from the
extracted directory:

```sh
python build.py
```

The script invokes pdfLaTeX twice, places temporary files in `build/`, and
copies the resulting PDF to `article.pdf`. On systems where Python is named
`python3`, use that command instead. TeX Live or MiKTeX must provide the usual
packages used in the preamble, including newpxtext/newpxmath, amsmath, amsthm,
mathtools, microtype, tcolorbox, titlesec, fancyhdr, listings, and hyperref.
No font files or third-party papers are distributed in this archive.

The equivalent direct commands are:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

## Reproduce the exact checks

```sh
python code/verify.py --output reproduced_data
```

Only Python's standard library is used. Do not pass `-O` or `-OO`; the script
refuses to run with assertions disabled. A successful run ends with
`ALL CHECKS PASSED`. The CSV and JSON are deterministic; compare them with the
files supplied in `data/`. To overwrite the supplied result files instead,
use `--output data`. This command does not itself capture a new console log.

All 7,332 preorders through n=5 are checked for coefficient symmetry,
unimodality, duality, endpoints, the h_1 formula, and special-simplex slacks.
All 35 preorders through n=3 undergo independent spanning-tree, hypertree,
activity, edge-sum, Hall-margin, polar/gauge, fiber, and interior-translation
checks. The run enumerates 18,009 spanning trees and checks 399 matching-tree
certificates. Five selected n=4 instances have complete Ehrhart checks through
m=8 for the larger model and m=4 for the smaller model. Further examples occur
in dimensions 5 and 6.

## Data conventions

The CSV fields are `n`, `principal_ideal_bitmasks`, and `h_coefficients`.
The two vector fields use semicolons. Bit positions are zero-based: row value
5 means {0,2}. Row i is the set of j satisfying j <=_tau i (a principal ideal,
NOT a principal filter). Polynomial coefficients are listed in increasing
degree order. The n=0 row has an empty ideal-vector field and polynomial 1.

Graph certificates in the JSON use both shores indexed 0,...,n, with 0 the
universal added vertex. These graph indices are offset by one from the
zero-based indices in the preorder bitmasks.

The verification does not compute a numerical convex realization of the
simplicial polytope, test flagness, certify real roots, or constitute a formal
proof. Its purpose is to compare exact, independently defined representations
and expose orientation, dimension, or lattice-index errors.
