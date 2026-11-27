# Two extensions of the ProveIt GRH research program

Prepared for Vladimir Reshetnikov, 27 November 2026.

## Start here

- `uniform_symplectic_compressions.pdf` and `.tex`: main research paper. It proves uniform laws for rectangular symplectic compressions, sharp rank discrepancy, a persistent full-matrix discrepancy, and a first-order joint independence law.
- `half_dyadic_filters.pdf` and `.tex`: companion note. For every even length, almost half of the dyadic pole-detection filters can be removed without changing the optimal uniform constant or its minimizers. Stability, residue recovery, and angular-frequency consequences are proved as well.
- `notes/source_audit.txt`: relationship to the source repository, precise novelty boundaries, and verification status.
- `code/`: reproducible exact checks and the plot-generation script.
- `data/`: exact-check receipts, comparison tables, and a pinned source manifest.
- `figures/`: the comparison figure as a standalone vector PDF and PNG.

Both papers give complete human-readable proofs and are unconditional: neither uses RH or GRH as an assumption. They extend mechanisms and results investigated in the supplied repository. The files distinguish inherited lemmas from the new conclusions. No claim of a new Lean kernel verification is made.

## Source version and novelty

The source is VladimirReshetnikov/ProveIt at commit
`497c1844e71393df41914f5b783d5dc9a618eb61`, specifically
`Analysis/GeneralizedRiemannHypothesis/Article/`.

The main paper resolves the fixed positive dimension-gap case singled out in `spn:q:symplectic`, with estimates uniform in every nonnegative gap. Its first-order joint law is an additional result. The companion resolves the family of simultaneous positive-even-index deletions in `ana:q:dyadic`. The full-family filter constant, the exact finite symplectic likelihood, and the square-case marginal expansions were already in the source and are attributed accordingly.

Novelty means new relative to the pinned corpus and the primary literature inspected for this task. The packet does not certify exhaustive global priority. The source manifest gives the exact Git blob hash and SHA-256 digest for every retrieved article text file; all 25 were checked against the returned Git metadata. Original source texts are not redistributed in this packet.

## Reproduce the computations

Python 3.10 or later, standard library only:

```sh
python3 code/verify_symplectic.py
python3 code/verify_half_dyadic.py
```

The first command writes `data/symplectic_verification.json` and `data/symplectic_checks.csv`; it performs direct enumeration and rational probability calculations. The second writes `data/half_dyadic_checks.json` and `data/half_dyadic_verification.txt`; its certificates use exact rational arithmetic and outward-rounded integer intervals. The current receipts report all checks passed. The finite computations corroborate the proofs; they do not establish the universal theorems by themselves.

Optional figure regeneration requires matplotlib:

```sh
python3 code/make_figures.py
```

## Rebuild the papers

A conventional TeX Live installation with common AMS, Latin Modern, geometry, booktabs, graphicx, microtype, and hyperref packages is sufficient. From this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error uniform_symplectic_compressions.tex
pdflatex -interaction=nonstopmode -halt-on-error uniform_symplectic_compressions.tex
pdflatex -interaction=nonstopmode -halt-on-error half_dyadic_filters.tex
pdflatex -interaction=nonstopmode -halt-on-error half_dyadic_filters.tex
```

The main paper inputs `notes/symplectic_validation.tex` and includes the existing PDF figure. Bibliographies are embedded in the TeX sources; BibTeX is not required.

`SHA256SUMS` lists the final packet's file digests. The archive includes no cached toolchains, source-repository copy, or transient compilation files.
