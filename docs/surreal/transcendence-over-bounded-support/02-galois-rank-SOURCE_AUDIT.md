# Source, contribution, and proof audit

Manuscript: **A Galois Rank Dichotomy for Omnific Fraction Fields**

Date: 23 September 2026.

## 1. Exact claim boundary

The paper concerns the fraction fields F_Gamma(k) of the bounded-above-support
subrings of full Hahn fields k((t^Gamma)). For the canonical real and Gaussian
omnific subrings with the specified exponent group, these are precisely their
fraction fields. The paper does not identify F_Gamma(k) with the entire Hahn
field without proving the necessary hypothesis. It does not assert a
nontrivial algebraic extension of the full surcomplex field No[i].

The proposed contribution is the following package of applications and
consequences of cofinal support descent.

1. At an order unit, realization inside the ambient Hahn field of every finite
   group, and jointly of every product of at most continuum many finite groups.
2. Explicit independent radical towers with exact finite degrees and profinite
   groups, together with symmetric-polynomial and real-conjugation variants.
3. An exhaustive change-of-scale alternative for inclusions of exponent groups
   with divisible source: cofinal inclusions preserve every finite extension
   and all finite Galois data, while noncofinal inclusions split every finite
   complex extension after scalar extension. The corresponding restriction on
   absolute Galois groups is surjective or trivial, respectively.
4. A concrete countable tower of subfields of No[i] in which each stage realizes
   every finite group, every old finite extension splits at the next stage,
   and the union is algebraically closed.

These have written proofs. The status “proposed contribution” concerns
historical novelty, not a replacement of proof by speculation. No independent
refereeing, Lean certificate, exhaustive priority search, or resolution of a
named published conjecture is claimed. Several conclusions are deliberately
short consequences of known mechanisms once the correct fraction fields are
identified.

## 2. Repository actually inspected

Repository:

```text
https://github.com/VladimirReshetnikov/Surreal
```

Pinned snapshot:

```text
343dc2c471212bb9b53ff4623bace2e1943f255b
```

The connected GitHub reader was used for the recursive repository tree,
selected directory metadata, and these targeted files:

- `README.md` and `docs/README.md`;
- `docs/surreal/omnific-preserving-automorphisms/12-automatic-strongness-SOURCE_AUDIT.md`;
- `docs/surreal/omnific-preserving-automorphisms/13-omnific-isomorphisms-SOURCE_AUDIT.md`;
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`;
- `docs/foundations-and-computation/large-cardinal-embeddings-and-normal-forms/README.md`;
- `docs/surreal/transcendence-over-bounded-support/README.md`.

Some long connector responses were truncated. The relevant bounded-support
claims were included in the returned guide text. The repository's full main
articles and formalization ledger were not read exhaustively. A repository
code search was incomplete and is not evidence of absence. A local clone
attempt could not proceed because network name resolution was unavailable.
No repository build, proof-assistant run, or repository modification occurred.

The overview's automatic-strongness question was not selected as a new target:
the newer audit files already record proposed answers. Existing universal
quotient, arithmetic, and large-cardinal results were also treated as prior
repository material rather than reproduced under a novelty claim.

### The decisive predecessor

The guide **Bounded-Support Hahn Arithmetic: Cofinal descent, optimal support
thresholds, and maximal transcendence** identifies:

- Theorem 3.2: cofinal linear disjointness, including coefficient-field descent;
- Corollary 3.3: intersection, relations, and finite algebraic-degree preservation;
- Corollary 3.4: the exact Laurent-series intersection at an order unit;
- Theorem 7.1 and Corollary 7.2: the bounded ring is a field without an order
  unit and is algebraically or real closed under the appropriate hypotheses;
- Section 8.4: a noncofinal exponent enlargement can make an old full Hahn
  field bounded-supported in the larger scale.

All of those facts are credited. The present article reproves the same-coefficient
cofinal descent theorem, its cyclic instance, the no-order-unit union argument,
and the elementary support-translation formulas needed for the new applications.
Thus the proof does not rely on the correctness of an uninspected repository
argument. The guide comparison did not identify the full Galois package above,
but this is not a claim that no uninspected companion or published source
contains it.

## 3. Primary public mathematical sources

The following primary sources were accessed for mathematical background and
source checking. No borrowed full paper is redistributed in the archive.

### L'Innocente and Mantova

Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
power series and omnific integers*, Advances in Mathematics 442 (2024), 109513;
arXiv:1710.07304v5.

```text
https://arxiv.org/html/1710.07304v5
```

The relevant inputs are the standard Hahn-field construction and closedness
statement, the relation with Conway normal forms and omnific integers, and the
care needed concerning fraction fields and cofinality. In particular, the full
identity Frac(Oz)=No is classical, not a new result of this manuscript. The
paper's GCD or factorization conjectures are not assumed or claimed solved.

### Milne: field theory

James S. Milne, *Fields and Galois Theory*, version 5.10, September 2022, 144 pages.

```text
https://www.jmilne.org/math/CourseNotes/FT.pdf
```

Chapters 3, 5, 7, and 8 supply standard finite Galois, Kummer, infinite Galois,
and finite-etale-algebra background. Version information, the relevant chapter
locations, and selected mathematical passages were checked. The article's exact
radical degree argument is supplied directly by valuations and Eisenstein,
including composite root degrees; it does not assume independence from
coefficient transcendence.

### Milne: Riemann existence

James S. Milne, *Lectures on Etale Cohomology*, version 2.21, 22 March 2013,
202 pages, Theorem 21.3.

```text
https://www.jmilne.org/math/CourseNotes/LEC.pdf
```

Riemann existence is the classical geometric input that supplies finite covers
of the complex projective line. The relevant PDF page was rendered and inspected.
The finite-group realization over C(z) is not claimed new. The article explains
how to choose all branch points away from zero and infinity and how a split
local place embeds the whole Galois function field in C((z)). Its proposed
application is transport of this data to the specified omnific fraction fields.

### Other background

The user-supplied Wikipedia article was consulted for orientation, not as the
primary proof source:

```text
https://en.wikipedia.org/wiki/Surreal_number
```

Conway's *On Numbers and Games* and Gonshor's *An Introduction to the Theory of
Surreal Numbers* are cited as classical background books; they were not freshly
reviewed cover to cover. Additional Riemann-existence lecture material was used
as a cross-check, but the final proof citation is Milne's stated theorem. Failed
web fetches and inconclusive searches are not used as mathematical evidence.

## 4. Critical proof checkpoints

**Fraction field versus ambient Hahn field.** Every use of equality is justified.
The canonical omnific ring recovers arbitrary constant coefficients in its
fraction field by shifting a numerator and denominator. Bounded support depends
on the named group, not merely on the represented surreal number.

**Linear disjointness, not only intersections.** All finite denominators are
cleared before projecting a relation onto a coset. Cyclic slices are finite
because a well-ordered bounded support has both a lower and an upper bound. The
general cofinal version uses bounded Hahn slices, not finite ones. Transport of
joint Galois groups uses the full finite compositum.

**A whole local field, not one root.** The selected finite Galois cover is
unramified over zero, with residue field C. Its completion at a point over zero
is C((z)), which embeds its full function field. This is enough to apply the
linear-disjointness theorem to the complete splitting field.

**Infinity is included among possible branch points.** In the arbitrary-product
construction, all finite covers have disjoint branch loci on the full projective
line, with zero and infinity excluded. An intersection cover is therefore
unramified everywhere and trivial. The radical construction instead allows
shared ramification at infinity and proves independence at distinct finite
branch points; these are two different arguments.

**Divisibility.** It is not needed for the finite-group or explicit radical
realizations at an order unit. It is needed for ambient Hahn algebraic closedness
and hence for the assertion that every finite complex extension is absorbed at a
noncofinal enlargement. These scopes are distinguished in the statements.

**The exponent-inclusion alternative is exhaustive.** For an ordered subgroup
Gamma of Delta, noncofinality means that some positive h in Delta exceeds every
member of Gamma. There is no third inclusion case between cofinality and this
form of domination. The research question about intermediate behavior is
therefore stated for more general, nonmonomial field embeddings.

**Finite splitting versus persistence.** In the noncofinal case the old full
Hahn field contains an algebraic closure of the old fraction field. The new
fraction field contains that full old field by one uniform shift. Every finite
minimal polynomial then has all of its distinct roots in the new field, and the
Chinese remainder theorem gives the displayed product algebra. In the cofinal
case, the cofinal descent theorem instead keeps the tensor product a field.

**Absolute Galois groups.** The paper gives explicit quotients and induced
restriction maps, not a complete classification of any absolute Galois group.
The infinite group topologies are profinite; claims of group cardinality are not
claims about minimal topological generating cardinality. Surjectivity and
triviality coincide when the target group is trivial.

**The real case is separate.** The corresponding real field absorbs a compatible
real closure, not an algebraic closure. For example, X^2+1 remains without a root
in an ordered field. Complex conjugation acts by inversion on compatible roots
of unity in the generalized-dihedral construction.

**No proper-class field extension is hidden.** Each Galois group and each tensor
product is formed for set-sized fields. The final full-surreal discussion records
why Frac(Oz)=No and why this does not contradict any of the restricted-scale
obstructions.

## 5. Computational and document validation

The deterministic script `code/verify.py` passed 8,950 exact assertions in 18
groups, using Python 3.13.5 and SymPy 1.14.0. Its seed is 20260923. All numerical
arithmetic used for coefficient and support checks is exact. No floating-point
approximation, external network service, or large-cardinal simulation is used.

These checks test finite identities only. They do not verify well-ordered Hahn
support arguments, Riemann existence, infinite Galois theory, cardinalities, or
the complete proofs. There is no Lean or other proof-assistant certificate.

The final article was compiled, checked for unresolved references, citations,
and box warnings, and rendered to 27 page images. All pages were inspected in
contact sheets, with selected title, theorem, and explicit-example pages also
inspected at full resolution. The final build facts and file hashes are recorded
in `data/build_audit.json`. A clean extracted copy was built separately before
release. PDF byte-for-byte reproducibility across TeX installations is not
promised. No font files, third-party articles, or repository source tree are
included.
