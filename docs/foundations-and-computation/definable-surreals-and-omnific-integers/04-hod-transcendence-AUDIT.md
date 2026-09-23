# Research and verification audit

## Mathematical status

The article supplies written arguments for the proposed results. It has
not been refereed, independently certified, or formalized in Lean.

The principal proposed original theorem is support-subfield amplification
and its HOD-surreal consequence (Theorems 8.2–8.3). The proof reduces
polynomial evaluation to disjoint normal-form support cosets. It does
not assume a class transcendence basis or Global Choice.

The fixed-leading-term coefficient code and one-interval universe tests
are proposed contributions or consequences. The complementary two-term
code is an elementary observation and is not presented as a major
independent novelty claim. The birthday threshold is identified with the
standard first subset disagreement between HOD and V, not presented as
an entirely new set-theoretic invariant.

## Critical proof boundaries checked

1. Ambient set-theoretic definability is distinguished from intrinsic
   ordered-field definability throughout.
2. Standard external formulas in arbitrary models are distinguished
   from internal formula codes; nonstandard models are explicitly
   handled only where the external pointwise-definability proof applies.
3. OD surreals are identified with HOD using canonical sign codes.
   Whole normal forms, not merely their entries, control HOD membership.
4. Denominator clearing in the definable integer part uses one ordinal
   selected from the whole support; it does not require every support
   element to be parameter-free definable.
5. The omnific floor includes the negative-infinitesimal correction at
   an integral real constant coefficient.
6. Every displayed normal-form sum is set-sized, even though the
   constructed independent family is indexed by all ordinals.
7. Independence is proved for every finite polynomial, not inferred
   from pairwise distinctness or individual transcendence.
8. The localization theorem uses infinite monomial interval widths,
   not intervals of width less than 1.
9. Fixed-fragment truth predicates are not collected into a purported
   uniform truth predicate for V.
10. Forcing claims distinguish no new reals, old arithmetic absoluteness,
    and possible changes to ambient parameter-free definitions.

## Literature and repository scope

The bibliography contains classical sources on surreal normal forms,
omnific integers, real closed fields, HOD, forcing, and definability.
Chen–Hamkins–Yang's announced birthday-expanded bi-interpretation is
explicitly credited and is not an unverified black-box dependency.
Hamkins–Linetsky–Reitz's pointwise-definable model existence theorem is
credited. The August 2026 Benhamou–Cummings–Goldberg–Hayut–Poveda preprint
is credited for the singular first-HOD-disagreement restriction.

The repository was pinned to:
9a385d3957bdfe3d9ea79f9a524751c90bd2c894

The README, report catalogue, and introductory/provenance sections of
these files were inspected through the GitHub connector:

- docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.tex
- docs/surreal/omnific-diophantine-geometry/article.tex

This was not a complete review of all 51 reports or preserved source
manuscripts. No nonclassical Diophantine, quotient, or automorphism result
from the drafts is needed for the new proofs. No repository writes or
Lean compilation were performed.

The literature search did not locate the precise support-subfield
amplification theorem or the fixed coefficient-template code. This
negative search evidence is limited and does not establish priority.

## Executed verification

The included Python script uses only finite formal exponents and exact
fractions; it never substitutes a large real number for omega.
Its delivered result file reports all checks passing:

- 8,191 finite sign-code round trips and injection checks;
- 11 malformed-code rejections;
- 3,121 rational normalization inversions and 3,120 order comparisons;
- 2,157 formal infinitesimal floor cases;
- 500 finite support-coset polynomial evaluations, with 55,105
  noncancelled formal support terms;
- one dependent-exponent negative control that correctly vanishes.

These checks are regression evidence only, not proofs of the class,
HOD, forcing, or definability assertions.

The final 26-page PDF compiled without LaTeX warnings, unresolved
references, or overfull boxes. All pages were rendered; the complete
page overview and selected pages at readable scale were visually checked.
The table of contents and appendix pagination were adjusted after review.
