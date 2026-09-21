# Rigorous Foundations for Surreal and Surcomplex Numbers
## Sets, Classes, Universes, and Formalization in Lean

Prepared September 21, 2026.

The 40-page article compares foundational approaches and applies them to the three supplied surcomplex manuscripts. It contains 17 main sections, two appendices, and 36 bibliography entries.

## Contents

- `surreal_surcomplex_foundations.pdf` — typeset article with linked contents and references.
- `surreal_surcomplex_foundations.tex` — standalone LaTeX source, including its bibliography.
- `source_audit.md` — inspected source versions, repository pins, and assessment boundaries.
- `build_report.txt` — actual document-production and preflight results.

## Mathematical scope

The article covers ZF/ZFC, explicit class theories, recursion strength, Grothendieck universes, Tarski–Grothendieck foundations, birthday-bounded surreal fields, constructive set theory, dependent type theory, and higher inductive-inductive approaches. It explains why small cuts, properly coded quotients, and small well-ordered Hahn supports avoid the standard size contradictions.

The manuscript-specific discussion preserves the distinction between fine-local analytic germs, Hahn-coherent functions on ordinary complex bases, and full-scale coherence. It includes an explicit nonpolynomial internally all-scale coherent function on C((t^Q)) to demonstrate why the full-surreal rigidity argument does not transfer to every fixed Hahn field.

The Lean section records the existing separate combinatorial-games library and generic Mathlib infrastructure, then proposes a layered implementation plan. It distinguishes source-verified declarations from bridge theorems that were not verified in the inspected files.

## Build

From this directory, run:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surreal_surcomplex_foundations.tex
```

Alternatively, run `pdflatex` repeatedly until cross-references stabilize. Standard TeX Live packages suffice. No external images, bibliography database, or bibliography processor is required.

## Verification boundary

The PDF was compiled, all pages were rendered, page layouts were inspected, and the final LaTeX log was checked for missing glyphs, unresolved references, and overfull boxes.

No Lean or Lake executable was available in the working environment. The illustrative Lean designs were not compiled, the external Lean project was not rebuilt, and the three supplied mathematical manuscripts were not machine-verified. No Mizar run was performed. This archive is an article and implementation design, not a certified Lean package.

“Paradox-free” denotes the explicit exclusion of the invalid constructions analyzed in the article. It is not an absolute consistency claim about the underlying set theory or proof assistant.
