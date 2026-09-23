# Source, novelty, and verification audit

Date: 23 September 2026.

## 1. Deliverable scope

The request was for substantive research on surreal numbers, surcomplex
numbers, and omnific integers, building on the Surreal repository where
useful, with a comprehensive article, further questions, and TeX/PDF files.

The selected topic is finite testing of omnific-preserving rational maps.
The deliverable does not claim to settle a named longstanding conjecture.
It develops explicit scale-adapted finite certificates, a pole-free
counterexample to every set-sized coefficient-independent test set,
set-sized-exception removal, and real/Gaussian arithmetic consequences.

## 2. Repository inspection

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit:
`bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59`.

The GitHub connector was used to inspect the repository, including:

- `README.md`;
- the recursive tree and documentation directory listings;
- `docs/README.md`, its research catalogue and review-status descriptions;
- the opening 180 lines of
  `docs/surreal/omnific-diophantine-geometry/article.tex`;
- the opening 220 lines of
  `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`;
- the full
  `docs/surreal/omnific-diophantine-geometry/08-fractions-SOURCE_AUDIT.md`.

Some large connector responses were truncated. The repository was not
checked out, the complete million-character formalization ledger was not
read, and the main articles were not read in full. An empty code-search
result for “integer-valued” was **not** taken as proof that the phrase or
related theorem is absent from the repository.

The inspected materials already credit the normal-form splitting,
constant-term retraction, fraction-field identity, and set-uniform fraction
clearing to earlier work. Those facts are not presented as new here. The
repository also clearly distinguishes written manuscripts, finite scripts,
and Lean-checked statements; the delivered article follows that distinction.

No repository contents were modified. No Lean build or independent audit of
repository proofs was performed. The new article's proofs do not import
unreviewed geometric conclusions from those manuscripts.

## 3. Primary literature used

### L'Innocente–Mantova

Sonia L'Innocente and Vincenzo Mantova,
*A factorisation theory for generalised power series and omnific integers*,
Advances in Mathematics 442 (2024), 109513.

DOI: https://doi.org/10.1016/j.aim.2024.109513

Author version used:
https://arxiv.org/html/1710.07304v5

The normal-form and ordered-group framework in Sections 2.3–2.4 was
inspected, including Proposition 2.4.5 and its statement that
`Frac(Oz) = No`. These are imported framework facts, not discoveries of
this article. Elementary fraction clearing and the needed fresh-scale
construction are proved again in the manuscript.

### Liu and the D-ring antecedent

Baian Liu, *Ring Structure of Integer-Valued Rational Functions*,
arXiv:2208.09935v3, 26 February 2024.

https://arxiv.org/html/2208.09935v3

Definition 1.9 and Proposition 1.12 were inspected directly. The latter
attributes the criterion to H. Gunji and D. L. McQuillan,
*On rings with a certain divisibility property*, Michigan Mathematical
Journal 22 (1976), no. 4, 289–299.

For an **infinite** domain with finitely many units, a nonconstant polynomial
cannot take only unit values; the D-ring criterion therefore has the bare
univariate denominator-collapse conclusion as a consequence. The qualifier
“infinite” matters: a finite field would be an exception to the naive
finite-unit argument.

During this investigation this antecedent was identified, and the bare
collapse was removed from the novelty target. The article gives its own
support-based proof, avoiding an unexamined transfer of all set-ring
machinery to proper classes. The original 1976 paper was not independently
read; attribution is explicitly through Liu's proposition.

### Elliott and classical integer-valued polynomials

Jesse Elliott, *Birings and plethories of integer-valued polynomials*,
Actes des rencontres du C.I.R.M. 2 (2010), no. 2, 53–58.

https://www.numdam.org/articles/10.5802/acirm.34/
https://www.numdam.org/item/10.5802/acirm.34.pdf

DOI: https://doi.org/10.5802/acirm.34

The polynomial/binomial framework was inspected, including a rendered PDF
page. The classical Newton basis and free-binomial-ring viewpoint are
credited, not claimed as new. Cahen–Chabert's *Integer-Valued Polynomials*
(AMS, 1997) is listed as background; the full monograph was not re-read.

### Gaussian universal sets

Jakub Byszewski, Mikołaj Frączyk, and Anna Szumowicz,
*Simultaneous p-orderings and minimising volumes in number fields*,
arXiv:1506.02696 (2015).

https://arxiv.org/abs/1506.02696

The abstract and bibliographic record were inspected. They identify the
existing Gaussian universal-set problem and its relation to simultaneous
p-orderings, including preceding work by Volkov and Petrov. No detailed
optimal-cardinality theorem from this paper is used in the article.
The new manuscript proves a transfer of finite constant test sets to the
omnific setting and supplies a self-contained square-grid bound. It does
not present the ordinary Gaussian testing problem as a newly discovered
open question.

### User-provided overview

https://en.wikipedia.org/wiki/Surreal_number was inspected as orientation.
It is not the authority for the research proofs and was not used in place
of the primary normal-form source.

## 4. Qualified novelty assessment

The targeted search and selected repository inspection did not locate the
exact combined package consisting of:

1. a separated-block Laurent detector at one fresh monomial scale;
2. the explicit multivariate bound
   `(d+1)^m + m*(2*d*d+2*d+1)^(m-1)`;
3. one common scale for a set-sized coefficient family;
4. a degree-one, pole-free-on-Oz rational function deceiving an arbitrary
   set of inputs, with numerator and denominator coefficients in Oz;
5. the empty-or-proper-class failure alternative;
6. the joint real/Gaussian finite-testing and constant-test lifting formulation.

This is not proof of originality. Some components may be elementary or
known specializations of broader Hahn-field, interpolation, or D-ring
results. The integer-valued polynomial basis, resultant method, arithmetic
splitting, and ordinary universal-set theory are established antecedents.
The manuscript labels the scale-sensitive package as a proposed contribution
and includes full arguments rather than relying on novelty assertions.

The repository contains many AI-assisted manuscripts, and only selected
excerpts were inspected here. No assertion of exhaustive nonduplication
is made. The unrefereed manuscript may still contain errors or admit
substantial simplification.

## 5. Mathematical boundaries explicitly checked in the text

- Supports are sets; the ambient surreal field is a proper class.
- The fresh exponent dominates the **whole additive group** generated by
  coefficient supports, not only leading exponents.
- Laurent powers occupy disjoint ordered blocks. Their union and the
  multiplication regrouping are justified, not treated as numerical limits.
- Constant term is multiplicative only on the nonnegative-support ring.
- Positive support refers to exponents, not coefficient signs.
- Rational presentations are reduced before pole tests are interpreted.
- The specialization polynomial includes both leading coefficients and
  the resultant, preventing degree loss and accidental cancellation.
- The symmetric point-count bound is sufficient, not claimed optimal.
- The no-universal-set construction has no omnific or Gaussian omnific pole,
  although it does have a pole elsewhere in the ambient field.
- “Set-sized exceptions” and “a set of successful samples” are not confused.
- Gaussian arithmetic is not replaced by an invalid Gaussian binomial basis.
- Image ideals are not assumed principal, and no gcd conclusion is inferred.
- Birational rigidity assumes an actual rational inverse in both directions;
  it is not a Jacobian-conjecture or arbitrary-bijection statement.
- The fixed-workspace extension requires an available dominating scale;
  a set-sized ring cannot satisfy the literal no-set-test conclusion.
- Omega powers are normal-form monomials, not an assumed analytic exponential.
- The tensor statements are finite-presentation/class identities, not claims
  that the full omnific ring is a set in the original universe.

## 6. Verification and build evidence

`verify.py` passed 1,776 deterministic exact assertions using Python 3.13.5
and SymPy 1.14.0. The reports enumerate the actual categories. The program
checks finite identities, specializations, and sampled lexicographic signs;
it does not implement all surreal numbers or prove any proper-class theorem.

The LaTeX source is self-contained and was compiled with pdfLaTeX. All
cross-references resolved. The resulting 24-page PDF was rendered and
visually inspected, including the title page, dense proof pages, and the
bibliography. There are no external figures or font files in the archive.

No Lean formal verification, Wolfram computation, independent referee
review, or certified priority investigation was performed.
