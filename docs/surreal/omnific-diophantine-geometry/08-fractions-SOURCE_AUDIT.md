# Source and novelty audit

Date: 23 September 2026.

## Scope of the deliverable

The user's request was to develop fractions of omnific integers, their
relationship to Q, and interesting potentially new theorems. The article
focuses on exact representation and denominator classification rather than
renaming No as a new fraction field. It makes no claim to solve a named
longstanding factorization conjecture.

## Repository snapshot and material inspected

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `9a385d3957bdfe3d9ea79f9a524751c90bd2c894`.

The GitHub connector supplied the main README, recursive tree and directory
listings, the documentation catalogue, and these relevant report guides:

- `docs/surreal/omnific-diophantine-geometry/README.md`;
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`;
- `docs/surreal/omnific-diophantine-geometry/06-definability-reconstruction-SOURCE_AUDIT.md`.

The detailed Diophantine catalogue already attributes the normal-form ring
structure, constant-term arithmetic, set-uniform common divisors and
fraction clearing, the irrational-real gcd obstruction, and primitive
constant real directions to prior repository manuscripts. These are
explicitly credited and the elementary dependencies are proved anew.
The quotient report's result is mentioned only as an antecedent, not used
as an imported theorem.

The connector responses were sometimes large and truncated. This audit does
not claim a complete read of every report or of the whole formalization
ledger. Citations to the repository's theorem numbers are explicitly to its
detailed catalogue. An empty GitHub code search was not used as proof of
absence. The repository was not checked out, built, modified, or formally
verified in this task.

## Published and public primary sources

### L'Innocente and Mantova

Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
power series and omnific integers*, Advances in Mathematics 442 (2024), 109513.

DOI: https://doi.org/10.1016/j.aim.2024.109513

Author manuscript v5, 22 January 2024:
https://arxiv.org/abs/1710.07304v5
https://arxiv.org/html/1710.07304v5

The normal-form conventions and the support-based fraction-field result
(Proposition 2.4.5) were inspected directly. The retraction setup of Lemma
9.2.1 was also inspected and is acknowledged as a methodological precedent.
The article's cited theorem numbering refers to this author version. This
source is not used to infer the current status of unrelated conjectures.

### Conway and Gonshor

Conway's *On Numbers and Games* and Gonshor's *An Introduction to the Theory
of Surreal Numbers* are the classical sources for the imported surreal
normal-form and field framework. Their publisher records were checked;
they were not read cover to cover in this task.

https://www.routledge.com/On-Numbers-and-Games/Conway/p/book/9781568811277
https://www.cambridge.org/core/books/an-introduction-to-the-theory-of-surreal-numbers/312AE504A3E88E804054BFB390446374

### Hamkins

Joel David Hamkins, *The omnific integers are strange*, 4 November 2025:
https://www.infinitelymore.xyz/p/omnific-integers-not-like-integers-after-all

Its publicly accessible introduction explicitly discusses failures of lowest
terms and irrational real numbers expressed as omnific fractions. Only that
publicly accessible content was used; the article does not claim to have
read or relied on an inaccessible continuation.

### Flatness

Stacks Project, Lemma 10.39.11, Tag 00HK:
https://stacks.math.columbia.edu/tag/00HK

The standard equational criterion is credited. The explicit relation and
Tor calculation for the polynomial omnific scale extension are proved in
the article, not attributed to the Stacks Project.

## Proposed contributions and limitations

The targeted search did not locate the exact complete classification of
all ambient omnific representations of a real rational-function tuple by
its projective specialization at zero. Likewise, the exact principal-versus-
Pi denominator package, scale-extension quotient and paired-residue package
were not found in the material inspected. This is a qualified novelty
assessment, not proof of priority.

The basic pullback-ring construction, ordinary polynomial Bezout algebra,
Chinese remainder theorem, and nonflatness criterion are classical. The
article does not present those methods as newly discovered. Some proposed
results may be useful specializations of wider commutative-algebra results.

## Important checked mathematical boundaries

1. Normal-form supports are sets; the ambient surreal field is a proper class.
   Positive support margins use full surreal cut bounds, not a fixed real
   exponent group.
2. The parameter tau is nonzero and purely infinite. Merely infinite elements
   with an arbitrary nonintegral constant part are not silently substituted.
3. The polynomial vector must have gcd one in a one-variable polynomial ring.
   The key argument is a Bezout identity, not a multivariate gcd assertion.
4. Rational projective residues require a common real normalization to a
   primitive integral vector before the principal generator is stated.
5. Primitive and unimodular are not assumed equivalent over all of Oz.
   They coincide for the representations classified in this article.
6. Denominator ideals include zero, while actual denominator representations
   require a nonzero multiplier.
7. The scale-defect dimension is a real coefficient-vector dimension, not
   a finite module-length assertion over a ring missing real constants.
8. All tensor and Tor computations use set-sized polynomial rings.
9. Rational specialization and real standard part have distinct domains;
   neither defines a ring retraction from the entire field No to a smaller
   field.
10. A pure unit-coefficient monomial denominator is more restrictive than an
    arbitrary omnific denominator. The example 1/(omega-1) separates them.

## Verification evidence

The self-contained written proofs are the mathematical evidence. The
supplied deterministic Python program passed 833 exact assertions with
SymPy 1.14.0. Its verification report lists the categories and exclusions.
The finite checks are not Lean verification, do not establish class-size
claims, and cannot certify originality. The final PDF was compiled and
visually reviewed after rendering. No external reviewer or referee has
validated the arguments.
