# Targeted repository coverage audit

## Snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `e260237db9b71da8b74a0c13c8e6355119091100`

Commit timestamp returned by GitHub: 2026-09-21 21:43:38 UTC.
Audit reference date: September 21, 2026.

## Inspected evidence

1. **Collection map** — `docs/README.md`.
   It describes fifteen packages in surreal, surcomplex, and
   foundations-and-computation families. Its existing coverage includes analysis,
   analytic geometry, finite deformations, contours, global divisors, polynomial
   algebra, trigonometry, foundations, and computer algebra.

   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/README.md

2. **Trigonometry report description** —
   `docs/surcomplex/trigonometry/README.md`.
   The section “What is not proved” explicitly leaves the derivation on No
   unchosen and distinguishes the phase-extension classification from a
   differential-equation solution classification. This is the primary evidence
   for the selected gap. The existing finite-angle and global character results
   are not described as absent or incorrect.

   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/trigonometry/README.md

3. **Trigonometry article introduction** —
   `docs/surcomplex/trigonometry/article.tex`, source lines 1–210.
   The title, abstract, organizing distinction between angles and lengths, and
   introductory provenance were read. They distinguish canonical finite phases
   from additional choices at infinite real arguments.

   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/trigonometry/article.tex

4. **Computer-algebra report description** —
   `docs/foundations-and-computation/computer-algebra/README.md`.
   Its capability and limitation discussion separates semantic transseries and
   differential results from executable universal algorithms. The delivered
   article's certificate-oriented section respects that distinction rather than
   claiming a complete solver.

   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/foundations-and-computation/computer-algebra/README.md

## Selection and scope

Selected topic: the chosen Berarducci–Mantova differential structure on No and
No[i], with exact finite-phase compatibility criteria and oscillation obstructions.

The principal gap is an interface explicitly left open by the trigonometry
report. No claim is made that all other files were exhaustively searched or that
none contains an isolated observation about derivations. Repository code search
was not reliable for this audit; empty code-search results were not used as
negative evidence. The conclusion rests on the actual retrieved descriptions
and article introduction, not inferred absence from search snippets.

The new article does not depend on the repository's difficult analytic-geometry,
Noetherianity, divisor, or contour claims. It imports the differential foundation
from primary scholarly sources and proves the subsequent deductions explicitly.

## Suggested integration

A possible location is `docs/surcomplex/differential-algebra/`, with cross-links
from trigonometry and computer algebra. This is only a placement suggestion.
No repository mutation or upload was performed.
