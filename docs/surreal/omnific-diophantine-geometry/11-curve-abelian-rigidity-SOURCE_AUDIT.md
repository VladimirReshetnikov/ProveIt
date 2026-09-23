# Source and novelty audit

Date: 23 September 2026.
Article: *Curve and Abelian Rigidity over the Omnific Integers*.

## 1. Repository snapshot and actual comparison

Repository: https://github.com/VladimirReshetnikov/Surreal

Immutable snapshot:
`f6e031a8ebe78203f7d7b449d7e97cb7a540c949`.

The GitHub connector was used to retrieve the repository tree, directory
listings, the report catalogue, and selected report documentation and
source text. The decisive comparison for this article is the documentation
of the omnific Diophantine geometry report:

https://github.com/VladimirReshetnikov/Surreal/blob/f6e031a8ebe78203f7d7b449d7e97cb7a540c949/docs/surreal/omnific-diophantine-geometry/README.md

That documentation records Euler derivations and separated-power rigidity
in Section 7, and records the general affine-curve question, including
`Y^2 = X^3 + aX + b` with `a != 0`, as Question 14.1. It also distinguishes
reviewed Sections 1-7 from later unreviewed material and distinguishes
mathematical exposition from Lean coverage. The article compares against
this documented boundary; it does not claim an exhaustive proof audit of
all repository manuscripts, companions, or Lean files.

The broader catalogue was also inspected:

https://github.com/VladimirReshetnikov/Surreal/blob/f6e031a8ebe78203f7d7b449d7e97cb7a540c949/docs/README.md

Selected material on set-sized quotients and holonomic rigidity was
inspected while choosing a problem. Their results are not used as new
claims or as necessary inputs to the present proofs.

## 2. Primary mathematical sources actually checked

### Properness and invariant differentials

* Stacks Project, Tag 0BX4, especially Lemma 29.43.1: the proper valuative
  criterion, including arbitrary valuation rings rather than only discrete
  valuation rings. Statement and relevant proof text were read.
  https://stacks.math.columbia.edu/tag/0BX4
* Stacks Project, Tag 047I, Lemma 39.6.3: cotangent sheaves of group schemes
  and their invariant trivialization over a field. Statement and proof were
  read.
  https://stacks.math.columbia.edu/tag/047I
* J. S. Milne, *Abelian Varieties*, version 2.00 (2008): relevant discussion
  of invariant differentials, Chapter IV, Propositions 6.4 and 6.7, printed
  page 152. The relevant PDF page was also inspected as a screenshot.
  https://www.jmilne.org/math/CourseNotes/AV.pdf

### Curves

The following Stacks Project pages were read for the exact standard inputs:

* Smooth projective models and function fields, Tag 0BXX:
  https://stacks.math.columbia.edu/tag/0BXX
* Duality and the identification with regular one-forms for smooth curves,
  Tag 0BS2: https://stacks.math.columbia.edu/tag/0BS2
* Riemann-Roch, Tag 0BS6:
  https://stacks.math.columbia.edu/tag/0BS6
* Plane-curve genus, Tag 0BYD:
  https://stacks.math.columbia.edu/tag/0BYD
* Genus-zero curves and the projective-line criterion, Tag 0C6L:
  https://stacks.math.columbia.edu/tag/0C6L

The article supplies the deduction that regular one-forms generate the
cotangent sheaf of a positive-genus smooth proper curve. It does not
attribute the new Hahn-ring rigidity theorem itself to these references.

### Omnific factorization context

S. L'Innocente and V. Mantova, *A factorisation theory for generalised power
series and omnific integers*, Advances in Mathematics 442 (2024), 109513.
The abstract and bibliographic/version information were checked; the whole
paper was not audited and its factorization theorems are not needed here.

https://doi.org/10.1016/j.aim.2024.109513
https://arxiv.org/abs/1710.07304v5

Conway's *On Numbers and Games* and Gonshor's *An Introduction to the Theory
of Surreal Numbers* are cited as classical background. Their complete texts
were not newly read during this task. The article explains the normal-form
passage and size restrictions used in its own applications.

## 3. An important older precedent and the access limitation

Lou van den Dries, *Which curves over Z have points with coordinates in a
discrete ordered ring?*, Transactions of the American Mathematical Society
264 (1981), no. 1, 181-189, DOI 10.2307/1998418.

Its bibliographic entry and reproduced abstract were checked in the author's
Celebratio Mathematica bibliography:

https://celebratio.org/vandenDries_LP/article/788/

The paper's full text was not successfully retrieved. Therefore this work
makes no claim of a complete theorem-by-theorem comparison with that paper.
The abstract concerns existence in **some** discretely ordered ring, whereas
this article concerns the **fixed** Hahn polynomial part and the canonical
omnific integer part. Section 13 proves a concrete separation: an explicitly
constructed discretely ordered ring has a nonconstant elliptic point and
cannot embed into the canonical omnific integers. This distinguishes the
formulations, but does not by itself establish historical priority for the
new classification.

## 4. Imported versus proposed contributions

The following are imported background or already documented repository work,
not new claims: Hahn arithmetic and Conway normal forms; the constant-term
retraction; existence transfer to ordinary integers; support-preserving
Euler derivations; Pell and separated-power rigidity; the proper valuative
criterion; Riemann-Roch; invariant differentials on algebraic groups; and
the general Artin-Schreier telescoping construction.

The proposed contributions of this article are the differential-overlap
rigidity principle; its complete smooth-affine-curve classification over
algebraically closed characteristic-zero fields and over the reals; the
proper/abelian/semiabelian applications; the exact arithmetic-fiber theorem;
the extension to arbitrary reduced coefficient algebras; and the explicit
boundary package, including the dual-number defect and the separation of
arbitrary discretely ordered rings from the canonical omnific integers.
The elementary squarefree-superelliptic argument is given as an independent
extension of the repository's Euler-derivation method.

The characteristic-two counterexample is not presented as a new
Artin-Schreier identity. Its role is to prove that the characteristic-zero
hypothesis cannot be omitted, even for an elliptic curve over a rank-one
Hahn field.

## 5. What remains unestablished

The search was targeted, not exhaustive. No priority certification or
independent referee review is claimed. No named longstanding published
conjecture is asserted to be solved. The exact repository question answered
is its smooth-curve portion, including nonsingular short-Weierstrass curves.

The article does not classify all singular curves, prove rigidity for all
proper varieties without rational curves, permit arbitrary omnific
coefficients in the arithmetic equations, or resolve primitive
non-unimodular Fermat triples. It does not identify projective points over
a ring with arbitrary homogeneous tuples over its fraction field.

No Lean formalization of these new results was built or checked. The Python
program supplies exact finite regression tests, not a replacement for the
mathematical proofs.
