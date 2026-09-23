# Source, dependency, and novelty audit

Date: 23 September 2026.  
Article: *Recovering Surreal Coefficients from Monomial Extensions*.

## 1. Claim boundary

The main objects are R[M], F[G], and K_F(G) = Frac(F[G]), with **finite
supports**, a set-sized cancellative torsion-free commutative monoid M,
and a set-sized torsion-free abelian group G. All positive results assume
characteristic zero unless their statement says otherwise. F is real
closed or algebraically closed where the quartic detector is used. The
root-covered-ring results instead use the explicitly stated root-cover
hypothesis. No arbitrary Hahn summation is being introduced by adjoining G.

The article treats the proper-class coefficient cases No, No(i), Oz, and
Oz[i] elementwise. It uses minimum-rank fraction codes rather than
proper-class equivalence classes, and a set-subfield descent when applying
the published defect theorem. A notation such as Aut(Oz) is shorthand for
the classification of each class automorphism and its data; the collection
of all class functions is not asserted to be an NBG object.

These are proof-bearing proposed results. Their historical priority has
not been certified. No independent referee review or Lean verification of
the new results has occurred in this workflow. No named published Conway
factorisation conjecture is claimed solved.

## 2. Repository actually inspected

Repository: https://github.com/VladimirReshetnikov/Surreal

Final observed **commit**:

    1ab41af1e699a268909a05bc13791e9f4930f608

The commits API reported author/committer time 2026-09-23T23:04:37Z. Its
Git tree is fba47f20d8a0709d1c7c5f823cdd21a86be3aed8; that tree identifier
is not being confused with the commit identifier.

The GitHub connector supplied the root contents, root README, docs README,
targeted directory listings, and the following maintained guides/audits:

* `docs/surreal/omnific-preserving-automorphisms/12-automatic-strongness-SOURCE_AUDIT.md`
* `docs/surreal/omnific-preserving-automorphisms/11-coefficient-gaps-SOURCE_AUDIT.md`
* `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`
* `docs/surcomplex/hahn-hilbert-geometry/README.md`

Some long guide responses were truncated. Earlier reads used the then-current
`main`; they are not retrospectively described as pinned reads of the final
commit. This was a targeted content comparison, **not an exhaustive review**
of all proofs or all reports. A local clone failed because container network
name resolution was unavailable. No repository build or Lean run took place.
No new theorem in the draft is accepted merely because a repository guide
claimed it; elementary inputs used here are proved or credited to primary
literature.

The supplied Wikipedia article was consulted for orientation only:
https://en.wikipedia.org/wiki/Surreal_number
It is not the technical basis for any claimed new result.

## 3. Earlier manuscript retrieved separately

The user's Library contained the manuscript:

*Algebraic-Parameter Rigidity of the Omnific Integers: Strong cancellation,
finite-type embeddings, and nonalgebraizable formal flows*, prepared by
OpenAI ChatGPT for Vladimir Reshetnikov, 23 September 2026.

Source: `article(20260923-180340).tex`, version 1.  
Companion: `article(20260923-180339).pdf`.  
Its recorded comparison pin: `fb5c4b530e3ec04b5661347d51d5382526d5aa02`.

The abstract, contents, relevant statement snippets, and the contiguous
scope/limitations/further-questions section were inspected through Files.
The entire earlier article was not independently audited, and its bytes
are not redistributed in this package.

It already supplies the root-covered framework, the no-order-unit
monomial-divisibility mechanism for Hahn integer rings, polynomial and
finite-Laurent coefficient rigidity, strong cancellation, finite-type
embedding obstructions, and formal-flow results. Those statements are
not presented here as newly discovered. The current article extends the
targets to arbitrary-rank monoid algebras, gives finite existential
coefficient formulas, treats rational group fields, and proves an exact
finite/infinite cancellation boundary. It does not repeat the earlier
formal-flow or Makar–Limanov calculations.

## 4. Primary public sources

### L'Innocente–Mantova: normal forms and omnific fractions

Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for
generalised power series and omnific integers*, arXiv:1710.07304v5 (2024).

https://arxiv.org/html/1710.07304v5

Proposition 2.4.5 records the cofinality-dependent fraction-field statement
and credits Frac(Oz)=No to Conway's Theorem 32. This prevents a false transfer
of that equality to every set-sized Hahn integer ring. The needed full-class
fraction argument is printed independently in the present article.

### Mattarei: sparse root multiplicity

Sandro Mattarei, *Root multiplicities and number of nonzero coefficients
of a polynomial*, Journal of Algebra and Its Applications 6 (2007),
no. 3, 469–475; arXiv:math/0512239v2.

https://arxiv.org/abs/math/0512239

The characteristic-zero bound “nonzero root multiplicity is less than the
number of terms” is a classical antecedent. Our article prints its
Vandermonde proof. The further claim proposed for review is the uniform
rational-function power bound across arbitrary coefficient and torsion-free
monomial extensions, with a careful specialization of support differences.

### Baek–Lee: Mason–Stothers

J. Baek and S. Lee, *Formalizing Mason–Stothers Theorem and its Corollaries
in Lean 4*, arXiv:2408.15180v1 (2024).

https://arxiv.org/html/2408.15180v1

This is a primary modern treatment of the polynomial abc theorem and related
non-parametrization arguments. The quartic obstruction used here is a
classical application, with a full proof in Section 3. The existence of this
published formalization does **not** verify the current article or imply
that its quartic specialization and class-field applications were checked
in Lean.

### Lin–Wang: the crucial general structural input

Jinyu Lin and Xiaodong Wang, *Reconstruction of Torsion-Free Abelian Groups
from Rational Group Fields*, arXiv:2608.10381v1, 11 August 2026.

https://arxiv.org/pdf/2608.10381

The twelve-page PDF was read in parsed form and relevant pages were inspected
as screenshots, including Theorem 4.5. The general input is precisely:

    For a set-sized characteristic-zero field k and torsion-free abelian
    group G, K_k(G)^× / (k^× X^G) is a free abelian group.

The article does not claim to have discovered or independently formalized
that result. It also credits their two-frame/intersection reconstruction
method. Main Theorem C in full generality and the arbitrary-group pair
reconstruction theorem depend on this input, followed by the deductions
printed here. The divisible/prime-local automorphism argument instead uses
the independently proved sparse bound. No peer-review status is inferred
from the preprint's availability.

The new coefficient-recovery application is not a claim to solve Lin–Wang's
already addressed rational-coefficient reconstruction problem a second time.

### Freudenburg: cancellation context

Gene Freudenburg, *Laurent cancellation for rings of transcendence degree
one*, arXiv:1309.4737v2 (2013).

https://arxiv.org/abs/1309.4737

Used for comparison with the established Laurent cancellation problem, not
as a premise in the article's cancellation proof.

### Kaplan–Krapp–Serra: surreal automorphism context

Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra,
*Decomposing the automorphism group of the surreal numbers*,
arXiv:2509.22374v3, accessed 23 September 2026.

https://arxiv.org/html/2509.22374v3

Used for context and class-function cautions. No unrestricted surreal
field-automorphism conjecture is inferred to be solved by classifying the
external extensions in this article.

## 5. What is old, what is proposed, and what is not proved

| Item | Status in this article |
| --- | --- |
| Conway normal forms, closure properties, Frac(Oz)=No | Classical background; needed fraction argument reproved |
| Polynomial abc and quartic non-parametrization | Classical mechanism, full elementary proof printed |
| Sparse univariate multiplicity | Classical, credited and reproved |
| Root-covered hypothesis and Hahn absorption | Earlier user manuscript, explicitly credited |
| Finite polynomial/Laurent cancellation | Earlier manuscript; not a new claim here |
| Monomial defect freeness and two-frame method | Lin–Wang input, explicitly identified |
| Uniform quartic coefficient recovery in the stated extensions | Proposed application and reconstruction result |
| Quantitative power obstruction under arbitrary monomial refinements | Proposed sharpened finite-support formulation |
| Arbitrary-monoid coefficient rigidity and divisible-monoid formulas | Proposed extension/application with proofs |
| Hom(G,Z)=0 criterion over recovered closed coefficient fields | Proved deduction; general case depends on defect freeness |
| Closed coefficient field plus whole exponent-group recovery | Proved extension using the credited two-frame method |
| Exact finite/infinite rank cancellation threshold | Proved comparison with explicit failure examples |
| All automorphisms of No or No(i), or Gaussian stabilizers | Not classified by this article |
| Strong Hahn summation or compatibility with conjugation | Not automatic and not claimed |
| Worldwide historical novelty | Not established by a targeted search |

In particular, the main theorem is not a definition of Oz inside the pure
field No. The omnific formula is interpreted in Oz[M] (or its Gaussian
analogue) and uses an inequation. It is not asserted to be a single
Diophantine equation. The all-order-root characterization is infinitary,
unlike the fixed quartic formula. Coefficient invariance is not being
confused with first-order definability of the monomial subgroup.

## 6. Proof checkpoints

The most failure-prone steps are explicitly addressed in the article:
finite specialization is not a homomorphism on the entire multivariable
fraction field; denominators remain nonzero; the support-difference set
rather than only the separate supports must be separated; roots need not
lie in one fixed exponent lattice; the class defect argument descends to
one set subfield; omnific and field characters have different unit groups;
and infinite-rank cancellation counterexamples deliberately leave the
recovered coefficient family. Characteristic-p, noncancellative-monoid,
and Hahn-completion counterexamples demonstrate genuine boundaries.

## 7. Computation and document validation

`verify.py` passed 1,314 checks with exact integers and rational numbers,
using only the Python standard library. The seed is 20260923. The report
records twelve categories. These are finite algebra tests, not formal
verification of any infinite or proper-class theorem. No Wolfram run is
claimed.

The final standalone source was compiled through three pdfLaTeX passes.
The final log has no LaTeX warnings, unresolved references/citations,
overfull boxes, or underfull boxes. The PDF has 24 pages. All pages were
rendered and inspected in contact sheets; the title, principal statements,
dependency table, automorphism proof, and final bibliography were additionally
inspected at larger resolution. Final appendix/bibliography pagination was
re-rendered after adjustment. `build_report.json` and `SHA256SUMS.txt` record
the delivery's reproducibility and file integrity information.

No repository files, borrowed papers, separate font files, or failed clone
outputs are redistributed. The final ZIP contains only the newly prepared
article and its own reproducibility/audit files.
