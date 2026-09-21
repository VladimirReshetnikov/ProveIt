# Foundations for Surreal and Surcomplex Mathematics

Prepared September 21, 2026.

## Main deliverables

- `surcomplex_foundations.pdf`: the complete article.
- `surcomplex_foundations.tex`: self-contained LaTeX source with embedded bibliography.
- `lean/FoundationsSketch.lean`: an elementary no-universal-strict-bound proof and
  size-conscious data declarations.
- `lean/ComplexifySketch.lean`: a small complex-pair arithmetic illustration.
- `lean/InspectCurrentLibrary.lean`: inspection commands for a pinned external repository.
- `SOURCE_AUDIT.md`: source provenance and exact software revisions.

## Scope and verification status

The PDF is a mathematical exposition and formalization blueprint. It is not a
completed Lean formalization of surreal numbers or of the two supplied analytic
manuscripts. The accompanying Lean examples were NOT compiled in this environment;
no Lean or Lake executable was available. They are clearly marked illustrations,
not a tested standalone package. No claim that the inspected external repository
was independently rebuilt or completely axiom-audited is made.

The supplied manuscripts' mathematical claims are distinguished from published
background and from deductions proved in this article. The article is a
foundational audit, not an independent line-by-line verification of all analytic
proofs in those manuscripts.

## Build the article

Use a standard TeX Live distribution with pdfLaTeX, Latin Modern, AMS packages,
geometry, microtype, booktabs, longtable, enumitem, xcolor, fancyhdr, listings,
hyperref, cleveref, xurl and needspace. No custom fonts, shell escape, external figures or BibTeX
run are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error surcomplex_foundations.tex
```

Alternatively run `pdflatex` three times to settle the table of contents and
cross-references. The distributed PDF was actually compiled and rendered for
layout inspection; this is separate from the unexecuted Lean sketches.

## Exploring the Lean files

`FoundationsSketch.lean` uses `Init` only. `ComplexifySketch.lean` requires a
Mathlib project. Run a file with `lake env lean <filename>` from an appropriately
configured project. These are commands for a future local validation, NOT a
recorded successful run.

The inspection script targets:

- Repository: https://github.com/vihdzp/combinatorial-games
- Revision: `02b4a908ea2ecfefffecb438f691951a814a5264`
- Checked-in toolchain: `leanprover/lean4:v4.35.0-rc2`
- Mathlib revision: `dec5b2b780537b6eaf7f5e5f000c12f7387fb24d`

A future formalization should record clean builds and transitive `#print axioms`
reports for the actual theorem declarations it claims to verify. Do not interpret
an import, a module title, or `#synth Field Surreal` as proof of real closedness,
normal-form equivalence, or the analytic theorems.
