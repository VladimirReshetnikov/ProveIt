# Proof-obligation audit

This is an internal proof checklist, not an independent referee report or
proof-assistant certificate. References below are to the final article.

## 1. The statement matches C1

Section 1 reproduces the universal least-representative statement. The
counterexample is binary but excludes least representatives among all
total numerical functions as well. The proof never replaces “least” by
“minimal,” or a Turing minimal pair by a coarse-degree minimal pair.

## 2. Description conventions

Section 2 uses total coarse descriptions with a density-zero disagreement
set. Nonuniform reducibility quantifies separately over each input
description; uniform reducibility has one functional valid for all
input descriptions. Booleanization handles numerical descriptions of a
binary target. Effective-dense descriptions use explicit omissions and
never make an incorrect numerical assertion.

## 3. Density bookkeeping

Lemma 3.1 proves the exact prefix counts. Lemma 3.2 proves the bound
rho_N(E) <= M/N + 2^(-K). This justifies “finite errors in every column”
using the special summable tail; no countable-union-of-null-sets assertion
is used. The common error support in Section 8.1 obeys the same bound.

Finite checks verify count formulas and instances of this inequality.
They are not proofs of convergence for the constructed infinite sets.

## 4. Description-computing spectrum

Lemma 4.1 proves the needed relativized limit principle. Theorem 4.2
extracts A by limits of column majorities from any coarse description
computed by B; the majority error estimate is supplied explicitly.
Conversely, a B-computable approximation to A gives a description by
D(n) = a(v_2(n+1), n). This yields the exact condition A <=_T B'.

The classical unrelativized result is attributed to Jockusch--Schupp.
The proof does not confuse A <=_T D' with A <=_T D.

## 5. Actual representatives, not merely computing degrees

Lemma 5.1 codes a prescribed B into a B-computable description on the
computable null set of powers of two. The result has exact degree B and
is density-zero equal to the target. Proposition 5.2 supplies both
inclusions of the actual-spectrum identity. This is essential to the
jump-cone formula and to handling representatives beyond the descriptions
themselves.

## 6. The splitting decision is only c.e. with finite parameters

Definition 6.1 has a finite stem and a finite vector of locked column bits.
Admissibility can be decided by an ordinary program with those finitely
many bits hardcoded. A cross-splitting witness consists of finite strings,
an input, and two halting computations with different outputs.

Lemma 6.2 therefore uses 0', not A' or 0'', for the existence decision
once the finite parameters have been read. Obtaining those parameters
requires A, explaining the overall A join 0' bound.

No terminating finite search is claimed to decide the unbounded negative
case. The executable finite-table model has a different, explicitly
bounded specification.

## 7. The no-split conclusion computes an ordinary function

For fixed finite conditions and a fixed functional, search admissible
left strings for the first convergence on the requested input. Existence
of a total common function supplies termination. A genuine right
computation makes every possible left output equal to that function's
value, because a different output would be a forbidden cross-split.

The resulting program hardcodes only finite data. It does not consult A,
0', or the actual infinite oracles. Nonuniform dependence of a program
index on a finite stage is legitimate for Turing computability.

## 8. Preservation and density of the constructed pair

Refining a stem admissibly preserves the old lock condition. Adding a
column constrains future positions and never releases an old lock.
Pre-lock errors already in a stem are allowed, but are finite. Padding
makes the final oracles total and makes each requested output bit
accessible in a finite number of oracle-construction stages.

At the end of stage k, all later positions of column k are correct.
Finite disagreements witnessing a requirement persist. A no-split
conclusion persists when both completion classes are restricted later.
Every pair of functional indices is handled. Theorem 7.1 verifies all
these facts and the A join 0' complexity bound.

## 9. Nonzero class and no least degree

When A is not below 0', a computable coarse description is excluded by
Corollary 4.3. The constructed pair is therefore noncomputable. Any least
representative would be below both and consequently computable, which
would make the target coarsely computable. Corollary 7.2 gives the
contradiction. It does not assert that the spectrum lacks all minimal
elements.

The original target R_A and a constructed description are not incorrectly
called a minimal pair; when A >=_T 0', the target computes each constructed
description.

## 10. Perfect family

At every stage the construction splits each leaf at an unrestrained
coordinate, then handles all distinct leaf pairs and all index pairs up
to that stage. All later operations are admissible refinements, preserving
both positive and negative outcomes of previous splitting tests.

Two distinct infinite paths have separated by some finite level. For any
fixed functional indices, a later stage handles their leaf pair with
those indices. This proves the pairwise common-information property.
Common lengths give column stabilization uniformly over the family.
Continuity, injectivity, compactness, and absence of isolated points are
proved in Theorem 8.1.

The map is computable in A join 0' plus its input branch. The report does
NOT claim that uncountably many outputs are all computable in A join 0'.

## 11. The explicit degree-0' example

Section 9 defines D_K through bounded K-oracle halting simulations, so it
is computable in K. Each column eventually equals K'. Sparse K coding
makes the degree exactly K without changing coarse equivalence. Thus G
has degree 0', while its coarse class has the high-degree spectrum and
no least degree. No ordinary computation of K is purported.

## 12. Effective-dense boundary

Lemma 10.1 finds the first non-omitted answer in a positive-density
column. It decodes A without a jump. Theorem 10.2 constructs exact-degree
representatives above A by a computable null modification; the reduction
explicitly erases that computable support. It does not pass incorrect
answers as valid descriptions.

Proposition 8.3 shows that the perfect family's common null error support
has no computable null envelope when A is noncomputable. The general
least-representative question for effective density is not settled.

## 13. Historical versus mathematical dependencies

The pair and perfect-family proofs are self-contained finite-extension
arguments. They do not invoke a minimal-pair theorem, jump inversion,
a basis theorem, randomness, or cone-avoiding compactness as an unproved
black box.

Only Section 11 invokes HJKS Theorem 4.3. It shows that the literal
negative answer to C1 was already implicit in published results. No
historical priority is claimed for the refinements.

## 14. Limits of the checks

All 12 finite unit tests pass. The PDF compiles without warnings in the
final run and was rendered for visual review. Neither fact is Lean
verification or external mathematical peer review. The infinite proof is
the written argument, not the test log.
