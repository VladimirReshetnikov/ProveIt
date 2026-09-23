# Provenance and verification boundary

## Repository snapshot

Repository: VladimirReshetnikov/Surreal
Inspected commit: 2cb9c0200af749fbbd27796c97d017e7f16fbf33
Inspection date used in the manuscript: 22 September 2026

The native GitHub connector was used to inspect repository metadata, its
recursive tree, README.md, docs/README.md, and the relevant opening portion
of docs/NORMAL_FORM_BRIDGE.md at that snapshot. This was a targeted source
review, not an audit of every source file or a rebuild of the formalization.
The manuscript does not claim that the proposed new statements are already
formalized in the repository.

## Imported mathematical inputs

1. Conway normal forms and arithmetic; the normal-form characterization of
   omnific integers; real closedness of No; set-sized cut bounds.
   Sources: Conway, On Numbers and Games; Gonshor, An Introduction to the
   Theory of Surreal Numbers; L'Innocente--Mantova, arXiv:1710.07304v5.
2. Quantifier elimination and elementarity for real closed fields.
   Source: Tarski, A Decision Method for Elementary Algebra and Geometry.
3. Undecidability of integer polynomial solvability.
   Sources: Matiyasevich's 1970 theorem and Poonen's author-hosted survey.
4. The specific infinite-prime example omega^(sqrt(2)) + omega + 1.
   Source: L'Innocente--Mantova, Advances in Mathematics 442 (2024), 109513.
   This deep result is cited, not reproved or used in the main Diophantine proofs.

## Current-source qualification

Dan Abramov's September 18, 2026 announcement and the README of
`gaearon/conway-refinement` were inspected. Their claimed Lean refinement
proof was not independently rebuilt or audited. The manuscript does not
assume that claim. It mentions it to avoid presenting the 2024 problem
status as necessarily current.

## Proof status of this article

The mathematical deductions are proved in the manuscript, with hypotheses
and size restrictions explicit. Their novelty has not been established by
an exhaustive literature search. There was no independent peer review or
Lean verification of this article.

The included Python checks establish only the exact finite identities and
listed finite-support cases they execute. They do not verify arbitrary
surreal supports, class-sized statements, real-closed-field quantifier
elimination, or MRDP. The output file records the actual run.

The LaTeX document was compiled using pdfLaTeX/latexmk. Rendered pages were
visually inspected. The deliverable contains no third-party papers, repository
code, font files, or unverified proof-assistant scripts.
