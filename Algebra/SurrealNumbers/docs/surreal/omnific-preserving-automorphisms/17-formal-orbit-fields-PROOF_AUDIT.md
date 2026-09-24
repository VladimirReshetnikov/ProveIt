# Mathematical proof audit

## Status

This is an author-side logical audit of the supplied conventional proofs.
It is not independent peer review, a Lean proof, or a certificate of novelty.
The finite test program has a separate and much narrower role.

## Main proof obligations

### 1. The normal-form derivation

For the exponent character `h(g)=ct(g)`, only additivity of constant extraction
on the surreal field is required. At each coefficient of a product, the
Hahn convolution is finite and `h(g1+g2)=h(g1)+h(g2)` gives Leibniz. Multiplying
existing coefficients by real numbers cannot enlarge their supports.
The manuscript explicitly warns that constant extraction is NOT a ring map
on the full surreal field. It is a ring map on the nonnegative-support
omnific ring.

The constant field is the field of normal forms supported on `ker h`, not
just the real field. No convexity of `ker h` is assumed. The derivation has
no additive slice because the exponent-zero coefficient of every derivative
vanishes. This is checked before applying the rational constants theorem.

### 2. Rational constants in additive time

For `delta=D-partial_s`, expand a nonzero rational horizontal function at
infinity. Its leading coefficient is constant. A nonzero leading degree
forces a coefficient with derivative 1 after division by a nonzero constant.
If the leading degree is zero, subtract that constant and repeat with a
negative leading degree. The argument treats poles and proper rational
functions, and requires no valuation on the coefficient field.

The example `D(t)=1` demonstrates why the no-slice hypothesis is necessary.
No version of the parameter-exclusion theorem is asserted for such a field.

### 3. Constants and linear disjointness

A minimum-length dependence among horizontal elements is normalized to have
one coefficient 1. Differentiating removes that term; minimality forces the
remaining coefficients to be constants. This contradicts independence over
the base constant field. All relations here are finite.

The full horizontal field in the formal Laurent field is identified exactly,
not merely bounded below: the lowest-power argument excludes negative powers,
and the coefficient recurrence uniquely recovers a Taylor or binomial series
from its degree-zero coefficient.

### 4. Polynomial relations, algebraicity, and degrees

The equality of relation ideals follows from injectivity of scalar extension,
or equivalently by choosing a basis of the finitely many evaluated monomials.
A finite extension basis remains independent and spanning after base change.
The constant field is relatively algebraically closed by differentiating the
separable minimal polynomial. Therefore the additive algebraic-trajectory
criterion really is `x in C`, not merely `x algebraic over C`.

### 5. Exclusion of the additive parameter

A purported algebraic relation for `s` over the full orbit field uses only
finitely many field operations. A common denominator produces a finite sum
of polynomials in `s` times Taylor images. Choosing a constant-field basis
of the inputs and using independence over `No(s)` forces every coefficient
to vanish. This distinguishes an ordinary generated field from a closure
under arbitrary formal sums or logarithms.

### 6. The explicit omnific witnesses

For every ordinal alpha:

    A_alpha = omega^(alpha+1)
    a_alpha = omega^(-A_alpha)
    B_alpha = omega^(alpha+2)
    M_alpha = omega^(B_alpha)
    X_alpha = sum(n>=0) omega^(B_alpha-n*(A_alpha+1))/n!

`a_alpha` and `M_alpha` are constants because their exponents have constant
term zero. Distinct `a_alpha` are Q-linearly independent by uniqueness of
normal forms. The support of each `X_alpha` is a decreasing sequence, hence
reverse well ordered. Every exponent is strictly positive because the
leading term `omega^(alpha+2)` dominates `n*omega^(alpha+1)+n` for every
ordinary finite n. Fractional real coefficients at positive exponents are
allowed in omnific integers.

With `z=omega^-1` and `partial=-omega*D`, we have `partial z=1`, the same
constant field C, and `partial X_alpha=a_alpha*X_alpha`. A minimum-monomial
polynomial relation would force a nonzero rational function over `C(z)`
to have nonzero constant logarithmic derivative; degree comparison excludes
that. This proves independence over `C(omega)`, sufficient for BOTH clocks.

The proof does not require any global surreal/surcomplex exponential. The
only Hahn exponential used is written out as an admissible countable sum.
No step identifies coefficientwise Hahn summation with s-adic convergence.

### 7. Proper classes

The ordinal family is explicitly defined; each of its members has a countable
support. Independence means absence of every finite polynomial relation.
Restricting to any initial ordinal gives a set family of the desired size.
The no-set-basis conclusion is a consequence of these set statements, not
a numerical assignment of a 'proper-class cardinal'. Global Choice or the
stated class framework permits selection of finite witnesses on any chosen
set of indices. Every algebraic argument can also be read locally on a set
of coefficients and their differential-field closure.

### 8. Multiplicative clock

The binomial operator includes a factor D in every positive degree, ensuring
omnific preservation. The mixed derivative is `D-u*partial_u`, with
`u=1+v`; its invariant coordinate is `w=omega*u`, not `omega/u`.
Since `D(omega)=omega`, it kills w. Rational constants are exactly `C(w)`
by writing a horizontal rational function with coprime numerator and monic
denominator. The denominator divides its own derivative, which has smaller
degree, so both polynomials have constant coefficients.

The base isomorphism is `C(omega) -> C(omega*u)`. Linear disjointness is over
that enlarged field, not over C. This distinction is necessary: the target
contains `u=U(omega)/omega`. The exact finite-degree assertion follows from
this correctly identified base.

The formal substitution `s=log(1+v)` carries `No(s)` to `No(log(1+v))`, NOT
to `No(1+v)`. The different algebraicity answers are therefore consistent.

### 9. Monomial test and complexification

A monomial exponent splits as `g=(g-ct(g))+ct(g)`, factoring out a nonzero
constant. Rational weights give degree equal to the reduced denominator by
Eisenstein for `Y^q-W` and Bezout. Irrational weights give disjoint additive
`ker h` cosets in any purported relation after clearing denominators.
No order on the quotient group is used.

For complexification, D kills i and conjugation commutes with both flows.
The no-slice argument holds in real and imaginary parts. The independent
exponential-solutions lemma can be applied directly over `C(i)(z)`, so no
unproved assertion about preservation of independence under arbitrary
coefficient extension is needed.

## Deliberate boundaries and corrections during preparation

- Kept the full constant field C explicit; did not replace it by R.
- Distinguished additive coefficient extraction from its restricted ring-map role.
- Identified the *entire* horizontal Laurent field through its recurrence.
- Made no class-sized sum or class-valued cardinal calculation.
- Specified the scalar extension field separately for each clock.
- Stated the internal-evaluation research question over a smaller base field:
  evaluation into No cannot preserve independence over No itself.
- Corrected LaTeX theorem-reference types so lemmas and corollaries are not
  incorrectly called theorems by the cross-reference package.

## Finite checks

The actual run passed 30,900 assertions in 24 groups. The checks include
finite Hahn multiplication, exact rational exponential/binomial identities,
formal group and clock identities, finite witness coefficient recurrences,
finite ordinal-polynomial support inequalities, and small Vandermonde and
Kummer certificates. They do not constitute proofs of the quantified
infinite statements. See verification.json for exact counts and versions.
