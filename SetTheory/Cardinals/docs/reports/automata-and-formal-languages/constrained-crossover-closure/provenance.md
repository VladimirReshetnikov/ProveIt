# Provenance and bounded source audit

Date: 29 September 2026.

## Repository connection

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit (verified through the GitHub commit endpoint):
`9b24a3a8d545af9624f6ac455f5b548be62818b6`.
Its commit message catalogues incoming batches 40–41.

Principal consulted source:
`SetTheory/Cardinals/docs/reports/automata-and-formal-languages/insertion-degree-spectra/article.tex`.
The original material and its later Part II were distinguished. The report
studies insertion-degree spectra, supplies arbitrary binary profiles, and
leaves the unrestricted both-singleton insertion question outside its proofs.
It cites Hughes's 2026 preprint. The present work follows that citation to the
separate constrained-crossover decision question; no theorem in this package
requires the truth of a repository research claim.

The collection README was also consulted. It explicitly treats its reports as
AI-assisted, unrefereed drafts rather than machine-checked mathematical results.
Other subjects were considered during selection but are not dependencies.

## Primary sources actually consulted

1. Charles E. Hughes, *Undecidability of Adjacent Equality for Insertion,
   Shuffle, and Crossover Language Operations*, arXiv:2608.27755v1,
   submitted 27 August 2026.
   https://arxiv.org/abs/2608.27755v1
   The definition on printed page 2 and the declared one-step open question
   on printed page 3 were inspected in rendered PDF pages, not merely inferred
   from search snippets. The paper's iteration terminology is not silently
   imported: our parallel and frozen-source clocks are separately defined.

2. Esparza, Ganty, Kiefer, Luttenberger, *Parikh's Theorem: A simple and direct
   automaton construction*, IPL 111(12) (2011), 614–619.
   https://arxiv.org/abs/1006.3825
   Used for effective Parikh semilinearity, not for the new crossover count.

3. Kevin Woods, *Presburger arithmetic, rational generating functions, and
   quasi-polynomials*, JSL 80 (2015), 433–449.
   https://arxiv.org/abs/1211.0020
   Theorem 1.10 was checked in the full HTML text. Only its Presburger-counting
   implication is imported. The one-dimensional affine consequence and the
   product-to-geometric-series deduction are supplied in the article.

4. Daniel Kirsten, *Distance desert automata and the star height problem*,
   RAIRO–TIA 39(3) (2005), 455–509.
   https://www.numdam.org/item/ITA_2005__39_3_455_0/
   Used for PSPACE decidability of limitedness, including ordinary distance
   automata. The source also identifies the earlier Hashiguchi and
   Leung–Podolskiy work. The distance automaton for aligned rank is constructed
   explicitly here. No limitedness solver is included in the executable audit.

5. Krötzsch, Masopust, Thomazo, *Complexity of Universality and Related
   Problems for Partially Ordered NFAs*, Information and Computation 255,
   Part 1 (2017), 177–192.
   https://arxiv.org/abs/1609.03460
   Full PDF checked: Theorem 3 states PSPACE-completeness over every fixed
   alphabet of size at least two. This supplies the classical binary NFA
   universality hardness used in our ternary reduction.

The standard Post-correspondence input is credited in the bibliography;
the usual reduction to binary CFG universality is recalled explicitly.

## Scope of the novelty assessment

Targeted searches used constrained/one-point crossover, closure and
universality, coordinate or Cartesian hulls, and the above primary-source
terminology. No prior answer to the exact Hughes question or equivalent
combined package was identified in that search. Search results were uneven;
the search is not an exhaustive exclusion of all prior formulations.

The coordinate-hull observation is deliberately not claimed as a first
discovery. Likewise, all four major classical algorithmic inputs are credited.
Possible prior equivalents of the fragment invariant or the counting theorem
in recombination/splicing literature remain a priority-review task.

No statements about repository contents after the pinned commit are needed.
No file in the user's repository was edited or committed.
