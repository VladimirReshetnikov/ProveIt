# Proof audit and verification boundary

## Status

This file records an internal audit of the written arguments. It is not an
independent referee report and is not a proof-assistant certificate. The
article is the authoritative source for definitions, statements, and proofs.
No Lean proof of the new theorems is included or claimed.

## Exact hypotheses

The ambient field is `K = k((t^Gamma))`. The coefficient field `k` is
characteristic zero and trivially valued. `Gamma` is a nonzero set-sized
ordered abelian group. No divisibility, rank-one, order-unit, countable
cofinality, algebraic-closedness, or real-valued-norm assumption is used.
All derivatives are in the formal function variables and kill `K`.
Strong evaluation is tested on coefficient families before cancellation.
Entireness is relative to one specified Hahn workspace, not all of No[i].
For the multivariable theorem, the evaluation family is joint and all Euler
weights are positive integers.

## Dependency chain

1. **Hahn-family algebra (Lemma 2.1).** Finite sums of well-ordered support
   sets are well ordered, with finitely many decompositions at each exponent.
   This proves closure under products and scalar multiplication. Derivatives
   only reindex and multiply coefficients by scalars. The normalized residue
   contains only finitely many monomials because exponent zero has only
   finitely many contributors. Thus residue lands in `k[X]`, not `k[[X]]`.
   The elementary sequence proof uses ordinary set-theoretic choice.
2. **Scaled initial polynomial (Section 2).** The family minimum
   `h = min_n(v(a_n)-n*r)` exists only at a strongly admissible scale. The
   initial polynomial `p` is nonzero and has a largest active degree `N`.
   This Gauss value must not be replaced by `v(f(t^-r))`: evaluation at
   `X=1` could cancel the entire first layer.
3. **Escape of active degree (Lemma 2.4).** For any fixed `M`, one nonzero
   coefficient of index `m > M` defeats every index at most `M` at all
   sufficiently large admissible scales. Only finitely many comparisons
   are needed. There is no appeal to a countable cofinal sequence.
4. **Corner identity (Lemma 3.1).** At fixed total differential degree `D`
   and shift `W`, the coefficient of degree `D*N+W` after substitution of
   a polynomial with leading coefficient `A` is `A^D H_P(N)`.
   Falling factorials are used for ordinary derivatives, with `N >= s`.
5. **Finite certificate (Theorem 4.1).** The three displayed groups of
   strict inequalities make every noncorner scalar have positive valuation
   after normalization by `t^(-beta-D*h+W*r)`. Corner scalars have nonnegative
   valuation. Residue therefore leaves exactly the corner identity. Choose
   `N` above all integer roots of `H_P` to obtain a contradiction.
6. **Automatic nondegeneracy in first order (Section 5.1).** At fixed
   `(D,W)`, an exponent `j` of `f'` determines the other exponents uniquely:
   `i=D-j`, `k=W+j`. The resulting powers `T^j` cannot cancel. At least one
   residue coefficient is nonzero. This is the step that does not extend
   automatically to unrestricted higher order.
7. **Positive Euler extension (Section 7).** Bounded positive weight admits
   only finitely many monomials. The highest homogeneous part satisfies
   `E_q p_N = N p_N`. The corner residue is `p_N^D H(N,X)`, nonzero outside
   finitely many integer exceptions. Retaining all auxiliary variables is
   essential; cancellation after diagonal substitution is not admissibility.

## Three critical sign and support checks

- `h <= v(a_m)-m*r` is multiplied by `d-D < 0`. The inequality therefore
  reverses, giving the *lower* bound needed for positive scalar valuation.
- Derivative scaling is `f^(j)(t^-r X) = t^(h+j*r) g^(j)(X)`. The sign of
  `j*r` is positive. Combined with `z^k`, this produces `d*h-w*r` for
  `w = k - sum(j*m_j)`.
- Taking residues requires each summand to be in the nonnegative coefficient
  subring. The proof verifies this term by term before using multiplicativity
  or extracting the coefficient of the corner degree.

## Degree bounds and extension of constants

The candidate-degree set uses the full-coefficient polynomial `I_P`, not
only its residue `H_P`. An integer root of `I_P` is an integer root of `H_P`,
but the converse can fail. The low-degree cutoff is an ordinary rational
number and does not divide an element of `Gamma`. Candidate degrees are
necessary, not sufficient; exact polynomial substitution supplies the
remaining equations. Constants are checked separately.

The finite entire-solution locus is asserted only for fields and the stated
injective Hahn-field extensions. The proof applies the rigidity theorem
again over the extension, and integer-root vanishing in `I_P` is preserved
and reflected by injectivity. It is not a functorial assertion over arbitrary
rings with nilpotents. It does not imply that the number of solutions is finite.

For higher-order degree bounds, all degrees below the equation order are
retained separately; derivative leading terms can vanish at these degrees.

## Counterexamples and sharpness audited

- `f'=f^2` admits `f_lambda=t^lambda/(1-t^lambda*z)`. Its exact strong
  domain is `{0} union {x != 0: v(x)+lambda > 0}`. This rules out a final
  ray depending on the equation alone. The geometric-series summation
  step uses the standard Hahn–Neumann positive-support lemma, cited in
  the article rather than reproved in full.
- `z^2*f*f''+z*f*f'-z^2*(f')^2=0` has residue corner identically zero and
  precisely the formal solutions zero and `c*z^n`. There are polynomial
  solutions of unbounded degree. This is **not** a nonpolynomial entire
  counterexample and does not settle the unrestricted higher-order question.
- With zero or mixed Euler weights, explicit nonpolynomial strongly entire
  functions can be killed by the Euler operator. Positive weights matter.
- In characteristic `p`, `sum t^(n^2) z^(p*n)` is strongly entire over a
  rational-exponent Hahn field and has zero derivative. Characteristic zero
  matters independently of support considerations.
- Enlarging the exponent workspace can destroy entireness of a fixed
  nonpolynomial series. This is compatible with extension invariance of the
  polynomial degree classification.

## Finite checks actually performed

`code/verify.py` uses exact integers and rational sparse polynomials.
The delivered run passed 2,113 checks in six separately recorded groups.
It tests finite corner identities, first-order nondegeneracy, finite Hahn
layers and exclusions, positive-weight top-part identities, finite
lexicographic ordered-group inequalities, and worked equations.

It does not test arbitrary infinite supports, cofinality, all Hahn elements,
nonexistence of all annihilating equations, or historical novelty. None of
those conclusions is inferred from a finite test. The written support and
polynomial arguments carry those conclusions, subject to independent review.

## Remaining research boundary

No unrestricted theorem about all algebraic differential equations of order
two or higher is claimed. The present sufficient condition can fail. No
all-order differential independence follows merely from independence of
`f` and `f'`. No statement concerns algebraic independence of a point value
from its own ambient field, and no scalar Berarducci–Mantova result is claimed.
