# Automorphisms of the Surcomplex Numbers

**Subtitle:** Real forms, Hahn symmetries, valuation, and rigidity  
**Date:** 22 September 2026  
**Length:** 28 PDF pages, including the title page and contents  
**Author line:** Research article prepared with ChatGPT

## Contents of this package

- `surcomplex_automorphisms.pdf`: the typeset article, with linked contents,
  theorem references, bibliography, and external source links.
- `surcomplex_automorphisms.tex`: the complete LaTeX source. The bibliography
  is included directly in this file; no separate BibTeX database, image files,
  or font files are required from this package.
- `README.md`: these build and scope notes.

## Build

From this directory, run the following command three times:

```sh
pdflatex -interaction=nonstopmode -halt-on-error surcomplex_automorphisms.tex
```

Alternatively:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_automorphisms.tex
```

The source uses standard LaTeX packages, including `newtxtext`, `newtxmath`,
`amsmath`, `amsthm`, `mathtools`, `geometry`, `microtype`, `xcolor`, `booktabs`,
`array`, `longtable`, `enumitem`, `ragged2e`, `tocloft`, `fancyhdr`, `hyperref`,
and `cleveref`. Install missing packages through the package manager of your
TeX distribution. No shell escape or network access is needed to compile.

## Subject and scope

The article distinguishes unrestricted field automorphisms from automorphisms
preserving the surreal real axis, conjugation, valuation, strong Hahn sums,
modulus, simplicity, the omega-map, and exponential or differential structure.
It includes explicit monomial and phase automorphisms, support-certified
flows, class back-and-forth arguments, real-form constructions, fixed fields,
and the fine zero-derivative example obtained by doubling all Hahn exponents.

Repository comparison is pinned to:

```text
VladimirReshetnikov/Surreal
dcf86662b574988e75d08d515d3a2a5ba7bbc0d7
```

The repository's existing exponential-automorphism rigidity manuscript is
prior work and is attributed as such. Its main proof is included for its
role in the article; no discovery or priority claim is made for it.
The article records which repository interfaces and documents were inspected,
and distinguishes that inspection from an independent build of the project.

## Verification and limitations

The supplied PDF was compiled successfully with resolved cross-references
and no LaTeX warnings. The page layout was inspected, including the contents,
mathematical proofs, and summary table. Symbolic finite checks also confirmed
the norm product and polarization identities, the Cayley inverse, and the
rational-flow composition and inverse identities. Such finite checks are not
proofs of infinite summability or of the full surreal theory.

This is a written mathematical research exposition, not a peer-reviewed
publication or a Lean-certified development. Classical prerequisites are
identified and cited. The main reductions and constructions have written
proofs. No complete classification of all unrestricted automorphisms and no
exhaustive claim of historical novelty is made. No repository files were
modified, and no third-party papers or font files are redistributed.
