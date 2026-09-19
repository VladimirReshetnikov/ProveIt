# Reciprocity and Matrix Duality for Preorder Polytopes

Research manuscript, September 19, 2026.

## Main outcome

The article supplies proofs of Conjectures 7.2, 4.2, and 4.4 in Christos A.
Athanasiadis and Frédéric Chapoton, *Polytopes and posets associated to
preorders*, arXiv:2605.26916v1. It also proves the ordinary, q=1 statement
in their Conjecture 4.9, but not its full q-refinement.

Two mechanisms do the work:

- Subtracting the all-ones vector from interior lattice points, followed by
  ordinary Ehrhart–Macdonald reciprocity on integer rays. The result extends
  the double identity to independently weighted capacities at every element.
- Independently copying both color classes of the preorder's bipartite graph,
  followed by Postnikov's lattice-point formula. The result gives a
  heterogeneous array duality and hence the conjectured matrix transpose.

The implication from Conjecture 7.2 to Conjecture 4.4, and from the latter to
the ordinary zeta evaluation, was already explained in the source paper.
The manuscript supplies complete derivations after proving the required
reciprocity identity; it does not claim these implications as new.

## Status

These are research proofs, not an externally reviewed or formally verified
result. The classical imported results are stated explicitly and cited.
Computations supplement the proofs, rather than establishing the universal
quantifier. A public literature search did not locate a resolution of the
selected conjectures, but does not certify priority against private or
unindexed work. See `notes/source_audit.md` and `notes/referee_checklist.md`.

## Files

- `article.pdf`: typeset comprehensive article.
- `article.tex`: complete editable LaTeX source, including bibliography.
- `build.sh`: three-pass pdfLaTeX build.
- `code/verify.py`: exact-arithmetic verification, Python standard library only.
- `data/verification.json`: actual recorded result, test counts and example data.
- `data/verification.log`: console output of that run.
- `notes/referee_checklist.md`: hypotheses, signs, orientations and limitations.
- `notes/source_audit.md`: original sources and exact relevant locations.
- `references.bib`: optional BibTeX export of the references. The article itself
  uses an embedded bibliography and does not need a BibTeX run.

No external fonts, copied research papers, or LaTeX intermediate files are
included.

## Reproduce the exact checks

From this directory:

```sh
python3 code/verify.py --max-n 4 --out data/verification.json
```

Requires Python 3.10 or later. No packages, network, or external data are
needed. All decisions and arithmetic are exact integers. The recorded run
examined all 389 labeled preorders of sizes 1 through 4 and passed every
check. It took about 19 seconds in the original environment. Run time will
vary; timing fields are the only expected output variation for the same seed
and Python implementation. The default seed is 20260919.

The relation enumeration is exhaustive, while the heterogeneous parameter
checks use eight seeded choices per preorder. Polynomial reciprocity is
verified at a full unisolvent grid for each enumerated relation. Some
conjectures already had larger finite checks in the source paper; this
program is an independent regression test, not an improved enumeration bound.

`--max-n 5` is supported but was not run for this report. Exhaustive relation
generation examines 2^(n(n-1)) candidates and the subsequent exact counts
can become expensive. This is an audit program, not a scalable enumerator.

The JSON also includes one five-element worked example; that is not an
exhaustion of five-element preorders.

## Build the article

```sh
bash build.sh
```

Requires a reasonably complete TeX Live installation with pdfLaTeX and the
standard packages used in the preamble, including `newpx`, `microtype`,
`mathtools`, `tcolorbox`, `hyperref` and `cleveref`. No custom fonts are needed.
Equivalent manual build:

```sh
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
pdflatex -interaction=nonstopmode -halt-on-error article.tex
```

The PDF was compiled with TeX Live 2025, checked for unresolved references
and overfull boxes, and rendered for visual inspection.

## Conventions worth retaining

The ground-set size counts individual elements, not preorder equivalence
classes. Every nonempty order ideal is retained when slack is positive.
Negative arguments of counting polynomials are polynomial evaluations.
For multichains, k means the number of entries, with one empty multichain
at k=0. In the copied graph, the draconian total is the number of non-root
right vertices. The h-star polynomial is not the support enumerator.
