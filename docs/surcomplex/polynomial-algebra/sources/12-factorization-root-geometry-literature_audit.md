# Literature and provenance audit

Prepared for the article **Surcomplex Polynomial Algebra**, September 21, 2026.

## 1. Requested basis: the three supplied manuscripts

The source manuscripts are treated as supplied research documents, not as
independently refereed publications. No authorship is inferred from filenames.

### surcomplex_analysis(3).tex

Read foundations and the all-scale rigidity section, with the paper's supplied
organization and terminology retained. Inherited concepts include No[i],
set-sized Hahn workspaces, the normal-form valuation, finite standard-part
thickenings, strong summability, and the distinction between fine-local,
Hahn-coherent, and all-scale analytic conditions. The all-scale polynomial
rigidity argument in the new article is explicitly credited to this source.
The polynomial modulus-circle theorem in the new article is instead justified
by a fixed-degree real-closed transfer argument; it is not presented as an
unqualified extension of the source's contour theory.

### surcomplex_research.tex

Used its fixed-domain parameter framework, finite algebras, residue/trace
comparison, simple-root-cover discussion, and exact cubic collision example.
The new article explicitly attributes the cubic example. Its universal
monogenic-ring residue dual basis is proved directly. It does NOT claim that
this one-variable calculation proves the source's separate multivariable
Jacobian compatibility question.

### surcomplex_global_theorems.tex

Used the symmetric-support divisor criterion and the restricted interpolation
picture to explain the boundary between finite polynomial CRT and infinitely
many coherent prescriptions. The descending-root, complete-cluster, and
root-selector examples are source results, not new results of this article.
No inference of a general Noetherian analytic geometry is drawn from them.

The new notation H_{Gamma,>=0} and H_{Gamma,>0} avoids the different uses of
"+" in the two continuation manuscripts. This change is explained in the
article rather than silently identifying the conventions.

## 2. Public primary sources and their actual roles

### Surreal/Hahn field algebra

- Harry Gonshor, *An Introduction to the Theory of Surreal Numbers* (1986):
  established background for normal forms and real closedness, also cited in
  the supplied framework. No new full-text inspection or precise page claim
  about this book is asserted here.
- B. H. Neumann, "On ordered division rings" (1949): the classical support
  lemma used in the supplied papers. The article explicitly marks this as a
  foundational input, not a newly proved summability theory.
- Bjorn Poonen, "Maximally complete fields" (1993), author-hosted PDF:
  https://math.mit.edu/~poonen/papers/amsval.pdf
  Corollary 4 was inspected for algebraic closure of the relevant Hahn fields
  with divisible value group and algebraically closed coefficient field. The
  page containing the corollary was also inspected as a rendered PDF page.

### Real-closed transfer and polynomial geometry

- Lou van den Dries, "Alfred Tarski's elimination theory for real closed fields,"
  *Journal of Symbolic Logic* 53(1) (1988), 7–19:
  https://doi.org/10.2307/2274424
  The publisher record and extract verify quantifier elimination uniformly
  over real closed fields. The article uses the corresponding classical
  completeness/transfer principle with fixed finite degrees.
- Cyril Cohen and Assia Mahboubi, "Formal proofs in real algebraic geometry:
  from ordered fields to quantifier elimination" (2012):
  https://lmcs.episciences.org/844
  https://arxiv.org/abs/1201.3731
  Publisher/preprint metadata and abstract were consulted. This is a reference
  for the logical background, not a claim that the present paper is formally
  verified.
- Michael Eisermann, "The Fundamental Theorem of Algebra made effective:
  an elementary real-algebraic proof via Sturm chains":
  https://arxiv.org/abs/0808.0097
  The preprint record and abstract identify an algebraic route to polynomial
  root counting over real closed fields. No implementation or full proof from
  this work is reproduced or claimed as a new algorithm.
- Manuel Eberl, "Two theorems about the geometry of the critical points of a
  complex polynomial," Archive of Formal Proofs (2023):
  https://isa-afp.org/entries/Polynomial_Crit_Geometry.html
  Its record confirms the classical Gauss–Lucas and Jensen content. The new
  article gives its own elementary real-closed barycentric proof of the
  Gauss–Lucas instance; it does not reuse a proof-assistant certificate.

### Root uncertainty and non-Archimedean critical points

- Rida T. Farouki and Chang Yong Han, "Robust plotting of generalized
  lemniscates," *Applied Numerical Mathematics* 51 (2004), 257–272:
  https://doi.org/10.1016/j.apnum.2004.05.007
  https://www.sciencedirect.com/science/article/abs/pii/S0168927404000881
  The primary publisher abstract was consulted for the weighted pseudozero
  interpretation. The new uncertainty formulas are proved directly. No
  detailed plotting algorithm or full-text derivation is attributed here.
  A related 2007 root-neighborhood paper appeared in discovery results, but
  its attempted publisher retrieval failed; it is not a relied-on full-text
  source in the article.
- Xander Faber, "Topology and Geometry of the Berkovich Ramification Locus for
  Rational Functions, II":
  https://arxiv.org/abs/1104.0943
  The preprint record and abstract establish the relation to prior
  non-Archimedean Rolle and ramification work. They are not used as a theorem
  transferring rank-one Berkovich geometry to arbitrary surreal value groups.
  The exact polynomial ball-count proof in the article is given directly.

### Algebraic geometry

- The Stacks Project, Tag 00FV (Hilbert Nullstellensatz):
  https://stacks.math.columbia.edu/tag/00FV
  Consulted as the standard algebraic reference. The article supplies a
  finite-type field lemma and Rabinowitsch proof in a set-sized workspace,
  then interprets its finite certificate over No[i].

The user's Wikipedia anchor was used to identify the requested subject,
not as the principal source for technical proofs:
https://en.wikipedia.org/wiki/Surreal_number#Surcomplex_numbers

## 3. Interpretation of originality

The paper does not assert that finite algebra, Gauss–Lucas, Newton polygons,
Hensel factorization, residue duality, or the Nullstellensatz become new simply
because they are expressed over surcomplex numbers. Many proofs apply to a
larger familiar class of real-closed or algebraically closed valued fields.

The article's developed package consists of explicit all-scale normalizations,
residue directions, critical allocation, positive-support factor recursion,
an exact root-specific precision threshold, discriminant-only sufficient
precision, preservation of every pairwise root-distance valuation, and
compatible finite-ring residue identities. Each has a mathematical proof in
the text. The search did not establish a complete priority history of these
formulations, and no exhaustive absence claim or named-conjecture solution is
made. The strict-boundary quadratic counterexample proves the stated failure
at equality, not optimality of the discriminant bound for every polynomial.

## 4. Verification boundaries

The exact computations verify the finite identities and worked cases listed
in verification.txt. They do not prove arbitrary well-order statements,
class replacement principles, real-closed transfer, or the universal root
matching statement. Those rely on the explicit proofs and the named
foundational inputs. The manuscript has not undergone independent review.
