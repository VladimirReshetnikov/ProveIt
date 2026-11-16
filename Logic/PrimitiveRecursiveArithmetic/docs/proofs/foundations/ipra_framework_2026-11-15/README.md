# iPRA certificate-and-modulus framework

Main document: `framework.tex` / `framework.pdf`.

This is a cross-domain research framework, not a verified solution of all 48 existing proof packets. Core results: bounded PR search and descent, certificate composition, arithmetic of quantitative names, apartness-conditioned inverse, an exact-choice computability obstruction, and conditional height-bound enumeration.

Formalization: `lean/FiniteCore.lean` (native Lean starting point), `lean/ObjectTheoryBlueprint.lean` (object-level integration sketch), `lean/ROADMAP.md` (unsolved steps). No Lean check was run. LaTeX is compiled in the archive.

Rebuild PDF: `pdflatex -interaction=nonstopmode -halt-on-error framework.tex` (twice for TOC).
