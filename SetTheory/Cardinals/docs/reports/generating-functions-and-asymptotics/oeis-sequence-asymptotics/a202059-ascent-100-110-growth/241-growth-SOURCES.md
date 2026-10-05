# Sources and scope for Report241

Checked 5 October 2026. Sources below identify the mathematical model and the
specific published conjecture. This is a bounded actual-content comparison,
not an exhaustive bibliography or priority certificate. The package does not
redistribute any third-party paper.

## Exact models

- https://oeis.org/A202059: ordinary ascent sequences avoiding 100; offset 0
- https://oeis.org/A202060: ordinary ascent sequences avoiding 110; offset 0
- The inspected official OEIS record snapshots identify revisions 39 and 18,
  respectively, both dated 5 November 2025
- The common class avoids 000, 100, and 110; it is already catalogued in the
  2025 triple-pattern paper listed below

An ordinary ascent sequence x has x_1=0 and
0 <= x_i <= 1 + asc(x_1,...,x_(i-1)), where asc counts strict adjacent rises.
The entering rise at position i is excluded when checking that position.
Forbidden triples use arbitrary i<j<k and literal equality/order:
100 means x_i>x_j=x_k; 110 means x_i=x_j>x_k; 000 means all three equal.
These are not contiguous-factor, weak-ascent, modified-ascent,
restricted-growth, or unrestricted-inversion-sequence models.

## The final 2022 journal article

Andrew R. Conway, Miles Conway, Andrew Elvey Price, and Anthony J. Guttmann,
Pattern-Avoiding Ascent Sequences of Length 3,
Electronic Journal of Combinatorics 29(4) (2022), P4.25.

- DOI: https://doi.org/10.37236/11266
- Publisher: https://www.combinatorics.org/ojs/index.php/eljc/article/view/v29i4p25
- PDF: https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/
- Published 4 November 2022; the final journal PDF has 32 pages
- Related preprint: https://arxiv.org/abs/2111.01279, version 1, 1 November 2021;
  that PDF has 38 pages and different pagination
- SHA256 of the inspected final PDF:
  73515090bb5b933f9d488974f9fe772db6f0493807b87e986e19e7b9a7acc7b4

All page references in Report241 are printed journal page numbers:

- Page 2: ordinary ascent condition, strict rises, classical subsequence patterns
- Page 3: both 100 and 110 assigned the conjectured (3n/4)! exponential scale
- Sections 2.3 and 2.4, page 7 and following: actual 100 and 110 recurrences
- Section 6, pages 19-22: A202059 and conjectural Gamma(alpha n+1) scale,
  with alpha approximately 3/4
- Section 7, page 23, equation (11): A202060 and the corresponding scale
- Page 24: explicit statement assigning dominant factorial term (3n/4)!
  to both sequences

The final article's abstract reverses the labels of the polynomial/set-state
algorithms relative to Sections 2.3-2.4. A sentence in Section 7 also repeats
“100” where the section treats 110. Report241 relies on the actual sections,
identifiers, formulas, and explicit two-sequence statements, not those slips.
It claims a contradiction to the conjectural leading exponent, not an error
in finite enumeration or a refutation of an established source theorem.

The doubled increasing seed followed by fresh labels is already used in
Section 7. Report241 credits this. Its constructive refinement repeatedly
exposes a fresh interval by spending guaranteed internal ascents, yielding
an exact product family and uniform all-length lower bounds. A separate
increasing-run subset encoding proves matching logarithmic upper bounds for
both classes, using monotone non-first (110) or non-last (100) occurrences.

## The 2025 common-class source

David Callan and Toufik Mansour,
Ascent sequences avoiding a triple of length-3 patterns,
Electronic Journal of Combinatorics 32(1) (2025), P1.40.

- DOI: https://doi.org/10.37236/12720
- Actual PDF: https://emis.de/ft/35384
- Published 14 March 2025; 25 pages
- Theorem 1 groups the triples into 62 Wilf classes
- Table 2, page 25, Class 36 lists {000,100,110}, a singleton class
- Its positive-length counts through n=11 are
  1,2,4,9,22,58,163,486,1526,5019,17208

The inspected article lists this class and finite counts; it does not supply
the logarithmic factorial-order theorem proved here. The paper's nontrivial
Wilf-equivalence arguments must not be mistaken for an asymptotic solution
of singleton Class 36.

## Related work and limits

The 2015 Baxter-Pudwell paper on pairs of avoided patterns was checked for
model and nearby-class overlap; its inspected results do not supply this
triple-class factorial lower bound. Related cap-two and fixed-multiplicity
reports concern larger classes. Avoiding 000 alone does not enforce 100 or
110 avoidance, so their lower bounds cannot be transferred to this subclass.
The related models are distinguished without treating a different theorem as
a duplicate. The public report sources were verified by full-content reads:

- https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a202058-ascent-000-growth/article.tex
- https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a294220-ascent-multiplicity-caps/article.tex

These are cited for related-model comparison only. Their finer root-constant,
remainder, and ratio claims are not assumptions used in Report241.

Bounded searches and actual-content checks did not locate this exact-model
two-logarithmic-order result or a published correction of the specified conjecture.
This negative result does not establish global priority, absence of all prior
work, or correctness of any unrelated report. Report241 makes no claim of
external peer review, formal proof-assistant verification, or publication.

## Numeric fixtures

The public code records source URLs beside the single-class and common-class
prefixes. It recomputes the single classes by the source recurrences and checks
small cases by independent literal enumeration. It separately enumerates the
common triple class. The fixed finite prefixes are preserved as published;
none is replaced by a fitted or extrapolated value.

## P-recursive and D-finite equivalence

Richard P. Stanley, Differentiably Finite Power Series, European Journal of
Combinatorics 1 (1980), 175-188.

- DOI: https://doi.org/10.1016/S0195-6698(80)80051-5
- Author-hosted primary paper: https://math.mit.edu/~rstan/pubs/pubfiles/45.pdf
- Theorem 1.4 treats finite initial changes
- Theorem 1.5 identifies P-recursive sequences with D-finite ordinary series
- The definitions and equivalence are over the complex numbers

Report241 supplies its own radial companion-system/Gronwall argument that
entire D-finite functions have finite order. Cauchy's coefficient estimate
then contradicts the lower bound b_n^(1/n) >= c/(log n)^2 for b_n=u_n/n!.
Dividing a hypothetical recurrence for u_n by n! gives a polynomial
recurrence for b_n. Thus the proof distinguishes the entire exponential
generating function from the radius-zero ordinary formal series. It relies
on no arithmetic asymptotic theorem and no finite numerical fit.
