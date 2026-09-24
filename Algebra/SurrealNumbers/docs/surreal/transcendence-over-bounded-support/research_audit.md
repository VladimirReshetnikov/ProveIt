# Research audit and mathematical dependency boundary

Audit date: 22 September 2026. This record describes the work actually done;
it is not a guarantee of publication priority or a full repository audit.

## 1. Repository material examined

Repository: `VladimirReshetnikov/Surreal`.

The initial inspected revision was
`048b72cf7cbfc8ab246e4f73788c10460cb3f6e0`.
The root overview, documentation catalogue (`docs/README.md`), `docs/new`
tree, and the detailed README of
`docs/surreal/tail-spans-and-differential-transcendence/` were read through the
GitHub connector. The catalogue describes 36 reports. At that revision the
`docs/new` tree contained its README, not an additional collection of unseen
article files.

A later `main` commit was observed:
`6e34651fe640631d96cbb8ba61d7967cea9d9061`, whose parent is the initially
inspected revision. Its displayed commit description concerns Hahn–Hilbert
restrictions and closed range. This observation is not a claim to have fully
reaudited the later commit or later repository history.

Targeted repository code searches for `lacunary` and `bounded support` returned
no indexed matches. Negative indexed search is not evidence of exhaustive
absence. The substantive comparison uses the catalogue's topics and the
closest report's expressly described base fields, witnesses, and conclusions.
All 36 article sources, retired source archives, and Lean declarations were
not read line by line.

The closest thematic report uses independent square classes, coefficient
sign changes, cofinite vector spans, and radical coefficients to prove
algebraic and differential independence over specified full Hahn coefficient
fields. The present construction instead uses positive integer coefficients,
cofinal support gaps, and finite-pattern tables, and proves independence over
the fraction field of *all bounded-support series*. It also treats arbitrary
cofinality and simultaneous coefficient–exponent linear disjointness. These
are different base-field problems. Neither entire package is claimed to
subsume the other; in particular no differential-independence theorem is
claimed in this article.

## 2. Primary published source and earlier results

Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
power series and omnific integers*, Advances in Mathematics 442 (2024),
109513, DOI `10.1016/j.aim.2024.109513`.
Version examined: `arXiv:1710.07304v5`, 22 January 2024.

Relevant inspected portions are Fact 2.1.1, Section 2.3, Fact 2.4.2,
Proposition 2.4.5, Proposition 3.5.1, and the question following Example 9.1.3.
The arXiv HTML was used for the relevant text; the PDF front page was also
checked. The bibliography in `article.tex` includes source links.

Proposition 2.4.5 already provides a cofinality obstruction to representing all
Hahn series by fractions of one-sided series, using a cofinal gap construction.
The article explicitly credits that result. Merely showing that the bounded
fraction field is proper would not constitute its principal novelty claim.

The proposed strengthening is a family of 2^cf(G) elements algebraically
independent over the entire bounded-support fraction field, with positive
integer coefficients, one common optimal support, an optimal order-type
threshold, and explicit actual-surreal specializations. The additional descent
theorem concerns linear disjointness, rather than only nonmembership or
intersection of fields.

The source's rank-one upper-support multiplicativity is imported when
classifying units. Standard Hahn-field real/algebraic closedness and
lexicographic regrouping are also imported. They are not new results of this
draft. Conway normal form and the associated ordered-field realization are
standard foundations, cited through Gonshor's book and the above paper.
Gonshor's complete book was not freshly audited in this task.

The Stacks Project, Tag 09IC, was consulted for the standard language and
consequences of linearly disjoint extensions. The particular Hahn-field
cofinality theorem is proved in full in the article, not attributed to that
reference.

## 3. Literature-search scope

The targeted search included combinations of Hahn/generalized power series,
bounded support, fraction fields, lacunary algebraic independence, cofinality,
linear disjointness, and pre-Schreier arithmetic. Primary sources were used
for the mathematical comparisons. This was not an exhaustive MathSciNet or
Zentralblatt search, an exhaustive citation-network audit, or a review of
all unpublished work. A lack of relevant search hits does not prove novelty.

The warranted formulation is: these theorem statements were not identified
in the reviewed material, and are proposed contributions supported by the
proofs supplied here. Expert review may identify earlier equivalents or
simpler formulations.

## 4. Conditional GCD appendix

Appendix A assumes that the bounded-support real-exponent Hahn ring over an
algebraic closure of the coefficient field is a GCD domain. It proves descent
to each nonzero subgroup of the real exponent group and the original
coefficient field, using normalization, exponent characters, and coefficient
Galois automorphisms. The existence of the ambient GCD remains an explicit
hypothesis. The proof of the conditional implication is complete.

This gives a conditional answer to the bounded-support pre-Schreier question
following Example 9.1.3 of L'Innocente–Mantova. A universal coefficient-field
version of the input also implies the GCD property at arbitrary divisible
rank, by the article's structural reduction.

The public project `gaearon/conway-refinement` advertises a recent Lean proof
of the relevant one-sided real-exponent GCD statement. Its README and
`ConwayRefinement/Standalone/Mathlib/HahnSeriesGCD.lean` were read. The
standalone definition uses nonpositive real support and a characteristic-zero
coefficient field, but the full proof was not built, audited, or semantically
validated here. The project's provisional status is retained. Neither that
claim nor Conway's refinement conjecture is imported as an established new
result in this article.

No part of the main independence or cofinal-descent theorem depends on the
GCD appendix or that external project.

## 5. Proof-risk checklist

The written proofs explicitly handle the following potential failure points:

- Relations over a fraction field first have their denominators cleared.
- At a transfinite index the earlier partial Hahn series can have infinite
  support; boundedness, not finiteness, is used.
- A top homogeneous polynomial is forced to be nonzero on a chosen finite
  integer tuple; arbitrary coefficient sequences would not suffice.
- Polynomial expansions are finite, with genuine Hahn convolution. There is
  no use of an unsupported infinite rearrangement or a topological limit.
- Coset extraction and coefficient-linear functionals are module maps, not
  ring homomorphisms.
- Cofinality is what keeps projected coefficients bounded in the smaller
  exponent group. Without it, the entire smaller Hahn field is already
  bounded in the larger exponent group.
- Rank-one upper-support multiplicativity is not silently applied before
  reducing to an Archimedean quotient.
- Cardinal upper bounds are separate arguments, not consequences of the
  constructed lower-bound family. Regularity is explicit in the arbitrary-
  cardinal surreal examples; no continuum hypothesis is assumed.
- The Conway realization sends t^g to omega^(-g). Boundedness is relative to
  the fixed exponent workspace, not the full proper class of surreal numbers.
- Maximum cardinality of an independent family is not a transcendence-basis
  claim, and no transcendence over all surreal numbers is asserted.

## 6. Computational and document checks

`verify.py` exercises 12 finite mechanisms using exact integer and rational
arithmetic. The delivered run has 3,163 assertions, all passed. This is a count
of assertions, not of independent theorems. It is not a proof of arbitrary-
support summability, any infinite or cardinal independence statement,
publication novelty, or the ambient GCD hypothesis.

The PDF was built by pdfLaTeX in three final passes with shell escape disabled.
Its final 24 pages were rendered and visually inspected; the contents page
was also rendered with Poppler. The delivered `build_audit.json` records
layout bounds and log checks separately from mathematical testing. No
Lean code, Lean build, or proof-assistant certification is supplied.
