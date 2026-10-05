# Source audit and provenance

Audit date: October 4, 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected source path:

```
SetTheory/Cardinals/docs/reports/enumerative-combinatorics/
valley-monotone-bargraphs/article.tex
```

Snapshot commit returned by the repository search:
`70ab31a1ec77852d411bc8ca1fc81d86d0c9985e`

Fetched source blob:
`f37593705acecfdc8dc158e9079ae36887e96609`

Title: *A Pole Hierarchy for Valley-Monotone Compositions*.
Manuscript date: October 1, 2026; placement notes: October 2, 2026.

The relevant definitions, decomposition, analytic results, inversion section,
and further-research section were inspected. The previous report proves
unweighted exponential asymptotics, a positive-pole hierarchy, and a
bottom-valley central limit theorem. Its subsection “Joint limits and extreme
heights” explicitly asks for a maximum-height lattice-Gumbel law and its phase.
That is the direct continuation point for the present article. The previous
report is treated as a research manuscript rather than as an independently
reviewed publication; the analytic prerequisites needed here are reproved.

## OEIS

https://oeis.org/A001523

The entry identifies the weakly unimodal-composition / stack sequence,
provides generating-function formulas and classical asymptotic information,
and links the bargraph paper below. Its initial values through n=20 are used
as an exact implementation check. We do not claim a new leading asymptotic
for A001523 and do not assign an unverified OEIS identifier to the restricted
bargraph sequence.

## Published background

R. Flórez, J. L. Ramírez, D. Villamizar,
*Restricted bargraphs and unimodal compositions*,
Journal of Combinatorial Theory, Series A 208 (2024), 105934.
https://doi.org/10.1016/j.jcta.2024.105934

The publisher bibliographic record and OEIS link were accessible. The full
publisher article was not accessible during this session. The minimum-part
combinatorial decomposition is independently proved in the new article.
No assertion about uninspected passages of the publisher text is made.

P. Flajolet and R. Sedgewick, *Analytic Combinatorics*, Cambridge, 2009.
Author-maintained book information:
https://algo.inria.fr/flajolet/Publications/books.html

Cited for standard analytic-combinatorial methods, not for the new
model-specific constants, formulas, or conclusions.

## Novelty boundary

Targeted searches combining the published title and restricted/non-decreasing
bargraphs with maximum height, phase transitions, and Dirichlet refinements
located no earlier matching result. This was not an exhaustive review of all
publications or repository archives. The article therefore distinguishes
proved statements from claims of priority. The weighted and multicritical
questions are formulated and answered in this continuation; they are not
represented as previously advertised OEIS conjectures.

No third-party paper, repository source file, or font file is bundled.
