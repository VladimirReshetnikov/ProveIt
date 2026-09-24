# Vopenka reflection in hidden Prikry cores

Research continuation prepared for Vladimir Reshetnikov, 18 September 2026.

## Files

- `Vopenka_Reflection.tex`: standalone LaTeX article with an embedded bibliography.
- `Vopenka_Reflection.pdf`: compiled 17-page article.
- `README.md`: build instructions and theorem inventory.

## Main contribution

For an ultraexacting cardinal lambda, construct a fixed bijection
b : lambda -> V_lambda and a critical-sequence finite-change class q.
In N = HOD_{b,q}, the normal tail measure U contains E_A for every
A in P(V_lambda)^N, where E_A is the set of cardinals extendible
below lambda for the predicate A. The embedding graphs all have rank
below lambda and belong to N.

Consequently N regards lambda as a measurable Vopenka cardinal, and U
extends its Vopenka filter. The statement quantifies over N's predicates,
not over all predicates in the ambient universe.

## Theorem inventory

- Theorem 2.5: full hidden-core theorem, including the Prikry extension.
- Theorem 5.3: all-predicate tail concentration (the central strengthening).
- Propositions 6.1-6.2: the Vopenka consequence and filter inclusion.
- Corollary 6.3 / Proposition 6.4: diagonal and simultaneous reflection.
- Corollary 7.1: Vopenka reflection after removing q, retaining b.
- Theorem 7.2: exactingness plus V_lambda contained in HOD implies
  that HOD regards lambda as a Vopenka cardinal.
- Theorem 8.2: equiconsistency of the explicitly defined
  predicate-reflecting normal-measure and normal-trace principles.
- Proposition 9.1: a cofinal omega-sequence, used as a new predicate,
  has an empty below-lambda predicate-extendibility set.

## Build

Use a normal TeX Live or MiKTeX installation with newpxtext, newpxmath,
amsmath, mathtools, tcolorbox, hyperref, and the other packages listed
in the preamble. No external source files or BibTeX run are required.

```sh
pdflatex -interaction=nonstopmode -halt-on-error Vopenka_Reflection.tex
pdflatex -interaction=nonstopmode -halt-on-error Vopenka_Reflection.tex
pdflatex -interaction=nonstopmode -halt-on-error Vopenka_Reflection.tex
```

The supplied PDF was compiled with pdfLaTeX. Cross-references and citations
were resolved; the final build reported no LaTeX warnings or overfull boxes.
All pages were rendered and visually inspected; the final bibliography
layout was inspected after the last layout revision.

## Scope and status

The article continues `docs/Large_Cardinals_Synthesis.tex` in the supplied
Cardinals4.zip. It does not repeat the prior normal-trace theorem as a
new result: that theorem is reconstructed as a prerequisite.

Detailed English proofs, an internal/external scope ledger, and primary
references are included. The mathematical arguments are research proofs,
not independently refereed or machine-checked. The supplied Lean project
was used as a reference; no new Lean formalization was attempted.

The consistency calibration concerns the explicitly stronger
predicate-reflecting measure principle, not a bare measurable cardinal
or merely a cardinal that is both measurable and Vopenka. No improvement
of the published I0-equiconsistency of ultraexactingness is claimed.
Novelty is asserted relative to the supplied synthesis, not as a verified
worldwide priority claim.
