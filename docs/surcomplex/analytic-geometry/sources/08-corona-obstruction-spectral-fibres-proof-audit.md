# Proof audit and scope

## Exact category

The coefficient ring throughout is the global fixed-disk ring
O(D)((t^Gamma)), with D the ordinary unit disk and one well-ordered global
support. Every coefficient is holomorphic on all of D. Coefficient magnitudes
need not be uniformly bounded in the ordinary absolute value. All sums are
set-sized. The surreal interpretation uses the canonical monomials
omega^(-gamma). No proper-class topological limit or proper-class sheaf
cohomology is used.

For Gamma = R the valuation gives a genuine real-valued non-Archimedean norm.
The article proves completeness and its equality with the supremum of actual
surcomplex evaluations. This norm is not the ordered surreal modulus and is
not the fine topology induced from the entire surreal field.

## Inputs and dependencies

1. Hahn multiplication and the positive-support Hahn–Neumann summability
   lemma are classical inputs, explicitly stated and cited.
2. The ordinary analytic tools are Taylor expansion, the identity theorem,
   removal of isolated removable singularities, and compact-uniform convergence
   of ordinary holomorphic series. The discrete interpolation theorem needed
   here is proved explicitly with damped cardinal functions.
3. The ultrafilter-based results assume a nonprincipal ultrafilter on the
   positive integers, available in ZFC. The explicit corona counterexample,
   exact Bezout criterion, and geometric local-ring proofs do not depend on
   that choice.
4. General elementary ring facts used include prime ideals in ultraproducts,
   residue-field base change, and the preservation of prime chains under
   localization below a fixed maximal ideal.
5. Canonical identification of Hahn subfields with surreal and surcomplex
   subfields is credited to the standard normal-form theory. The main algebraic
   proofs can be read independently of that embedding.

## Load-bearing proof checks

### Global units and the interpolation quotient

The evaluation image consists exactly of value families with one well-ordered
union of supports. Inversion requires both the leading-valuation set V and -V
to be well ordered, hence V finite. The converse has an explicit common support
certificate from finite normalization and positive-support inversion. The
criterion concerns finite leading spectrum, not merely bounded valuations.

### Corona pair

The ordinary divisor has precisely the simple zeros a_n = 1 - 1/n.
The exponent support 2 - 1/n is well ordered, while its negative is strictly
decreasing. Evaluation at an ordinary point can delete exponents but cannot
create new ones; this also proves persistence under value-group enlargement.
Taylor estimates cover every infinitesimal displacement, not only the
ordinary centres. The pointwise infimum e^(-2) is sharp and is not attained.
The proper ideal is nonprincipal by a separate leading-coefficient argument.

The bound is a valuation-norm bound in a complete uniform Banach algebra.
It does not purport to contradict Carleson's theorem for ordinary bounded
holomorphic functions or an affinoid Nullstellensatz in a different category.

### Prime fibre, coefficient reduction, and closures

Every Hahn function has a uniform lower bound on its evaluation valuations;
this is essential when multiplying by an arbitrary ring element in the proof
that the growth conditions define ideals. Primality is proved using ultrafilter
complements, not inferred from a vague growth analogy.

The extended classical ideal Q is characterized by zero values on one
ultrafilter-large set. The coefficientwise ideal J instead requires each
coefficient separately to belong to the classical maximal ideal. They differ.
The fibre H/Q is a domain. The maximal quotient H/J is explicitly a Hahn field
over the classical ultraproduct residue field. The displayed corona element
lies in J but not in Q or any growth prime.

All growth primes contract to the same classical maximal ideal, so the prime
chain is genuinely in one fibre rather than inherited from a classical chain.
An explicit ascending chain, not infinite dimension alone, proves failure of
Noetherianity. The coefficient-reduction maximal ideal contains the whole chain,
which proves infinite dimension of its localization.

The norm-closure argument permits infinite Hahn truncations below a finite
valuation threshold. It never replaces such a truncation by a finite sum.
The corona series itself is not the norm limit of its finite partial sums.
All growth primes share the same closure, while their algebraic inclusions
remain strict. The distance from the corona element to that closure is e^(-2),
with nonattainment.

### Geometric regularity

Division by z-a is established globally on the original ordinary disk with an
explicit Hahn support bound. A nonzero leading ordinary coefficient has finite
vanishing multiplicity at the standard part, bounding the order of vanishing
at the displaced point. Repeated division gives the DVR and completion results.
This does not assume a false global Noetherian theorem.

## Repository boundary

The snapshot is aa846271b4dcae2c055b216126a87210292ec19b. The fixed-domain
structure attribution in docs/surcomplex/analytic-geometry/article.tex is
contradicted by the examples. The article explicitly distinguishes that
attribution from the same report's common-domain germ and radius-free germ
rings. The counterexample divisor has infinitely many ordinary zeros; it is
not a counterexample to results whose hypotheses require an isolated finite
ordinary zero scheme.

The repository's global-divisors report already develops restricted
interpolation and global support obstructions. Those antecedents are cited;
the simple interpolation quotient is not presented as an unqualified discovery.

## Verification delivered

verify.py uses exact rational arithmetic and symbolic identities. The recorded
JSON has status PASS. Its finite checks validate examples and inequalities,
not the infinite structural theorems. In particular, no arbitrary real-rate
ultrafilter prime, infinite support, or universal local-ring statement is
machine-verified. No Lean code, compiled formal proof, or proof-assistant
certificate is supplied.

The PDF was compiled without LaTeX warnings, rendered, and visually inspected.
A separate page-boundary audit found no out-of-bounds text on its 26 pages.
These are typesetting checks, not mathematical verification.

## Novelty limits

No named published open conjecture is claimed solved. The literature search was
targeted, not exhaustive. The normed corona obstruction, exact finite-valuation
criterion, integral-domain fibre with continuum prime chain, coefficientwise
base-change failure, and common-closure refinement are proposed contributions
in this precise fixed-domain framework. Independent mathematical review and
broader priority checking remain necessary before publication-level claims.
