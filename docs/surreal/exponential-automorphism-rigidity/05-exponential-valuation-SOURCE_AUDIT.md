# Source and novelty audit

Inspection date: 22 September 2026.

## Exact problem source

Elliot Kaplan, Lothar Sebastian Krapp, Michele Serra,
*Decomposing the automorphism group of the surreal numbers*.

- Version inspected: arXiv:2509.22374v3.
- Version submission date on arXiv: 23 April 2026.
- Printed date on the PDF: 27 April 2026.
- Version-specific reference: https://arxiv.org/abs/2509.22374v3
- PDF inspected: https://arxiv.org/pdf/2509.22374
- Page 4: Definition 2.5 and Remark 2.6 identify 1-automorphisms by leading-term preservation.
- Page 10: Proposition 5.2 and Question 5.4. This page was visually inspected in the PDF.

The manuscript proves that fixing the value group and preserving the usual
exponential imply identity, even for endomorphisms. Leading-term-preserving
automorphisms satisfy the value-fixing hypothesis, so the result directly
answers the identified question. The proof does not use the source's
operator-logarithm route.

The inspected version still explicitly poses the question. This is not a
claim that all subsequent literature has been exhausted. Targeted searches
for follow-up resolutions and faithful value-group action did not locate an
independent solution, but a number of search results were irrelevant. No
priority conclusion is inferred from those unhelpful results.

## Other primary references

1. Harry Gonshor, *An Introduction to the Theory of Surreal Numbers*,
   Cambridge University Press, LMS Lecture Note Series 110, 1986.
   Background: the ordered field, normal forms, and usual exponential.

2. Lou van den Dries and Philip Ehrlich, *Fields of surreal numbers and
   exponentiation*, Fundamenta Mathematicae 167(2) (2001), 173–188.
   DOI: https://doi.org/10.4064/fm167-2-3
   Institutional bibliographic record inspected:
   https://experts.illinois.edu/en/publications/fields-of-surreal-numbers-and-exponentiation/
   No ordinal-length theorem from this paper is used in the proof.

3. Alessandro Berarducci and Vincenzo Mantova, *Surreal numbers, derivations
   and transseries*, J. Eur. Math. Soc. 20 (2018), 339–390.
   DOI: https://doi.org/10.4171/JEMS/769
   https://arxiv.org/abs/1503.00315v3
   Used only for the established existence of a nonzero compatible surreal
   derivation. The new global-loss obstruction is proved in the manuscript.

4. Vincent Bagayoko, Lothar Sebastian Krapp, Salma Kuhlmann,
   Daniel Panazzolo, and Michele Serra, *Automorphisms and derivations on
   algebras endowed with formal infinite sums*.
   https://arxiv.org/abs/2403.05827v2
   Version date: 22 September 2025.
   Context for formal operator exponential constructions; no such
   construction is used as a step in the main proof.

## Repository comparison

Repository: https://github.com/VladimirReshetnikov/Surreal

Recorded tree revision:
`608dd23c0539fce73723843949ee627641c27b30`

The root README, docs/README.md, and selected report READMEs were retrieved
through the GitHub connector. The catalogue lists broad analysis,
polynomial, differential, foundational, and other projects. It does not
list an exponential-automorphism report. This is a catalogue-level scope
comparison, not an exhaustive content or symbol audit of every repository
file. No files were modified in that repository.

## What is, and is not, being certified

The archive provides complete written proofs and reproducible finite
identity checks. Neither peer review nor machine verification of the
surreal theory is claimed. The main theorem is presented as a proved answer
to the specified question; first-publication priority is left unverified.
Elementary supporting facts are not relabeled as novel surreal theorems.
No PDF of any third-party source is redistributed.


---

## Correction appended when this manuscript was filed (2026-09-22)

The repository comparison above is wrong in its conclusion, and the error is
recorded here so it is not read again as fact.

This audit pins revision `608dd23c0539fce73723843949ee627641c27b30` and reports
that the collection held no report on the exponential-automorphism question.
At that exact revision:

    git ls-tree -d --name-only 608dd23c docs/surreal/

lists `docs/surreal/exponential-automorphism-rigidity`, holding a 1310-line
article that proves this manuscript's Theorem 1.1 by this manuscript's own
proof. What the audit actually inspected was `docs/README.md`, whose surreal
table had six rows and no exponential row at that revision. The catalogue claim
is literally true; the inference drawn from it -- that the manuscript therefore
takes a different direction -- is false.

The fault is shared. The report was committed in `d3d9688` without a catalogue
row, and `docs/README.md` only caught up two commits later in `e5791a8`, so the
tree and the catalogue genuinely disagreed for the window this audit sampled.
Nothing mathematical in this manuscript depends on the claim.
