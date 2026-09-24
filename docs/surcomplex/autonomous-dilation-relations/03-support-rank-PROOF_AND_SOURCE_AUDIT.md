# Proof and source audit

Date: 23 September 2026.
Repository pin: `efc5446229dbf61a97bdd5edae91dba20af9d131`.

## Contributions and boundaries

1. **Arbitrary-support rank obstruction.** Over an ordered scalar subfield F
   of the coefficient field, support rank at least m modulo an F-linear
   coefficient core forces independence of any m distinct positive F-dilates.
   The proof works in a set-sized ordered F-vector exponent group. No quotient
   order, Archimedean embedding, generic coefficients, or finite-support
   hypothesis is used.
2. **Exact finite-support order.** For rational dilations, the upper bound from
   a finite monomial field matches the lower bound. This answers the first
   question "Exact order from finite support" in the pinned autonomous-dilation report, not a
   purported named open conjecture from the published literature.
3. **Infinite-support rank bound.** An equation of autonomous order r forces
   rational support rank at most r. This answers only the rank component of
   the repository's next question, not its order-type or denominator-growth
   components.
4. **Rational monomial functions.** Support-linear projection descends a
   rational function to its support subgroup. Exact order then follows from
   the main theorem. A reduced-quotient difference-span formula makes the
   support rank computable from finite data. The individual projection and
   Laurent-factorization ingredients are elementary; no separate priority
   claim is certified for them.
5. **Explicit orbit independence.** A countable-support omnific integer has
   its positive-real dilation orbit independent over C. An ordinal family
   has a jointly independent tail over the full Hahn core containing any
   prescribed set of parameters. This is not a claim that large independent
   families of surreals were previously unknown, and not a transcendence-basis
   or generation theorem.
6. **Prime-field complement.** The finite-support formula in characteristic p
   uses the support-generated lattice and the p-free parts of the positive
   integer dilations. Arbitrary coefficient Frobenius twists are not covered.

## Proof obligations explicitly checked

- Greedy maxima exist because each relevant subset of the support is nonempty
  and reverse well ordered; the rank hypothesis establishes nonemptiness.
- The vector quotient G/H need not be ordered. All comparisons occur in G.
- Every support exponent greater than the j-th greedy choice lies in H plus
  the span of the preceding choices. This gives coordinatewise dominance of
  any projected-independent tuple, even after unused coordinates are discarded.
- Strict rearrangement holds in an ordered vector group, without embedding it
  in the real numbers. Positive distinct weights are both necessary.
- The leading determinant tuple is unique as an ordered tuple, so equal
  exponent collisions from different terms cannot cancel it.
- Every coefficient of the expanded Hahn determinant has finitely many
  contributions. No topological convergence or infinite determinant is used.
- Coordinate derivations preserve supports and annihilate the entire Hahn
  coefficient core, not just selected coefficients.
- The derivative-matrix criterion has a self-contained minimal-degree proof.
- Finite rational dilation sets permit one common denominator. An infinite
  set need not, so no finite-degree assertion for the entire rational orbit
  is made merely from its finite transcendence degree.
- Rational support projection is linear with one factor in the subfield;
  it is not treated as a ring retraction. A shifted denominator has a nonzero
  constant coefficient, ensuring its projection is nonzero.
- The reduced-quotient formula uses coprime Laurent polynomials. Coprime pairs
  remain coprime after a purely transcendental scalar extension. Their common
  unit has zero monomial exponent because a finite support cannot be invariant
  under nonzero translation.
- The real-scalar theorem uses real support rank; the exact rational-scalar
  theorem uses rational rank. These are not substituted for one another.
- The ordinal family uses real-linear independence of distinct Conway
  monomials. Its parameter-relative proof bounds second-level supports of
  every exponent in the set-sized core.
- Proper-class independence is proved only through finite instances in
  set-sized workspaces. No global basis of No and no proper-class sum is used.
- In characteristic p, greedy rank is taken over F_p but exponent comparisons
  use positive INTEGER weights in an ordered group. There is no order on F_p.
- Prime-field perfection handles the all-zero formal-gradient case in a
  minimal algebraic relation.

## Explicit negative cases and limitations

- Negative dilation: X + X^(-1) + Y + Y^(-1) has rank two and is fixed by S_-1.
- Repeated dilations repeat observations; d=1 is excluded from the order formula.
- Infinite rank-one support need not have order one: the repository example
  sum omega^(d^(-n)) has exact order two. A separate character-twist proof is
  included rather than assuming the repository's first-order classification.
- Real rank is not an exact upper bound for arbitrary real dilations: omega
  and omega^(sqrt(2)) are independent despite the original real support rank one.
- Positive-characteristic Frobenius breaks the characteristic-zero statement.
- Overlapping support spans require coefficient-sensitive analysis; disjoint
  supports alone do not imply the block theorem's hypothesis.
- The auxiliary logarithmic derivations are not the natural surreal derivative.
- No result is asserted on omnific factorization, normalization-fibre
  radicality, full first-order decidability, or exponential automorphisms.

## Repository evidence

Read through the GitHub connector:

- Root README and documentation catalogue.
- `docs/surcomplex/autonomous-dilation-relations/README.md`.
- `docs/surcomplex/autonomous-dilation-relations/article.tex` and its directory.
- Selected portions of `docs/surreal/set-sized-quotients-of-omnific-integers/`
  while selecting a direction; no normalization result is claimed here.

The relevant source report explicitly leaves finite-support equality open in
rank >= 3 (source label `adr:prop:rank-bounds` and the question "Exact order from finite support").
Its next question asks whether finite order bounds support invariants including
rational rank. The report itself distinguishes its questions from named
published open problems. The source comparison is pinned; it is not a claim
about every later commit or every unexamined manuscript in the repository.

Pinned target source:
https://github.com/VladimirReshetnikov/Surreal/blob/efc5446229dbf61a97bdd5edae91dba20af9d131/docs/surcomplex/autonomous-dilation-relations/article.tex

## External comparison and reading scope

- Harry Gonshor, *An Introduction to the Theory of Surreal Numbers* (1986),
  Chapter 5, normal forms. Publisher metadata checked. Conway normal form is
  an explicit classical input, not an independently reproved theorem here.
  https://doi.org/10.1017/CBO9780511629143
- Jack Edmonds, “Matroids and the greedy algorithm” (1971). Publisher abstract
  and record checked; the needed greedy lemma is proved in this article.
  https://doi.org/10.1007/BF01584082
- Salma Kuhlmann and Mickael Matusinski, “Hardy type derivations on generalized
  series fields,” arXiv:0903.2197v4. Abstract-level context only; our support
  derivations and their product rule are independently proved.
  https://arxiv.org/abs/0903.2197
- Hana Melanova, Bernd Sturmfels and Rosa Winter, “Recovery from Power Sums,”
  Experimental Mathematics 33(2) (2024), 225–234. Full HTML text checked,
  especially Proposition 3. The independent-monomial power-sum case is prior.
  https://arxiv.org/html/2106.13981v1
  https://doi.org/10.1080/10586458.2022.2061650
- Sonia L'Innocente and Vincenzo Mantova, “A factorisation theory for generalised
  power series and omnific integers,” Advances in Mathematics 442 (2024),
  109513. Abstract/metadata context only; no factorization theorem is a premise.
  https://doi.org/10.1016/j.aim.2024.109513
- User-supplied Wikipedia page: orientation, not a proof dependency.
  https://en.wikipedia.org/wiki/Surreal_number

This is not an exhaustive priority search. No claim of unprecedented
breakthrough status is certified by the absence of a search match.

## Verification actually performed

- Complete written proofs and the issues above reviewed during preparation.
- Deterministic exact Python run: 1,490 recorded check units passed.
- 217 polynomial Jacobian expansions matched their predicted leading terms.
- Four cleared rational-function Jacobians agreed with the expected rank,
  including one expected zero determinant.
- Additional exact checks cover Frobenius, matrix inverses, a sign boundary,
  and the power-sum reconstruction identity.
- PDF built with pdfLaTeX; final compile had no warnings, undefined references,
  missing citations, overfull boxes, or underfull boxes.
- All PDF pages rendered; contact sheets and selected full-sized mathematical
  pages inspected. This checks presentation, not mathematical truth.

No independent referee review, Lean formalization, repository-wide Lean build,
or Wolfram verification was performed. The Python tests do not verify any
infinite Hahn or proper-class theorem. All twelve research questions remain
questions in this article; only the stated partial data for them are proved.
