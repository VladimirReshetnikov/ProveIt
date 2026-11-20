# Finite polynomial-division route to norm nonvanishing

**Status:** a formalization roadmap, not compiled Lean and not a completed
`Prf PRAAx` theorem. The companion and determinant API was inspected at
ProveIt commit `3ee850b4c2d650cf01263823fd5415963747c5d0`. The parent
package's `SemanticSquarefreeTargets.lean` describes ordinary Mathlib
goals; those host-level goals and the numerical object-iPRA goals below
must be proved separately and connected by codec correctness.

## 1. Numerical input and the output identity

Work with the existing exact Gaussian-rational coefficient codes (or the
real-rational subcodec). A polynomial is a finite descending coefficient
list with a numerical degree cap. Normalize coefficients before zero
tests. Missing high slots are zero padding, not asserted degree facts.
Finite coefficient equality is the Boolean fold comparing all padded
slots. Every rational inversion has a displayed nonzero denominator test.

The input consists of coefficient lists for `g,h,A_0,...,A_(m-1)`, integers
`m>=1`, `e>=1`, and checked identities

`f=g^e*h`, `alpha*g+beta*h=1`, `gcd(m,e)=1`, `degree(g)>=1`.

Reducedness of `K[X]/(g)` can be supplied as the concrete polynomial
Bezout identity `U*g+V*g'=1`. This is a finite certificate, not a quotient
oracle. The output refers to the **actual existing** multiplication-matrix
norm of `G=Σ A_j Y^j` modulo `Y^m-f`.

For the exact upstream adapter, choose
`c=e*degreeCap(g)+degreeCap(h)` and `a=max_j degreeCap(A_j)`.
Supply `m` descending `Y` rows for `F`: its first `m-1` rows are zero
and its final row is `-f`, each padded to `c+1` descending `X` slots.
Supply `G` as `A_(m-1),...,A_0`, each padded to `a+1` slots. These
constructed lengths prove the existing `input F G m a c` shape guard.

For each nonzero `A_j`, compute `A_j=g^a_j B_j` with
`rem(B_j,g) != 0`. Zero `A_j` have a Boolean zero flag; they are not given
an infinity-valued order. Choose the least nonzero index minimizing
`m*a_j+e*j`. Coprimality makes the minimizing index `k` unique. Put
`s=m*a_k+e*k`. The finite output certificate is a polynomial list `Q`
and the coefficient identity

`N=g^s*((-1)^(k*(m-1))*B_k^m*h^k+g*Q)`.

The term inside parentheses has nonzero remainder modulo `g`; hence `N`
is nonzero. Its exact divisibility order by `g` is `s`. A further bounded
scan returns an index of an actual nonzero normalized coefficient of `N`.

## 2. The fixed primitive-recursive producer

Implement general univariate long division over the coefficient field
with an explicit loop of `degreeCap(A)+1` iterations. A nonmonic `g` is
allowed: divide by its nonzero leading coefficient using exact rational
arithmetic. The existing synthetic division and monic-reduction modules
are templates; **an arbitrary-divisor API is not asserted to exist**.

Repeated division by `g` uses a second loop capped at
`degreeCap(A)+1`. Start with `B=A,a=0`. While the remainder of `B` is zero,
replace `B` by its quotient and increment `a`. Once the remainder is
nonzero, freeze the state. For nonzero input maintain:

- `A=g^a*B`;
- `B` is nonzero;
- while active, `degree(B)+a*degree(g)=degree(A)`.

Since `degree(g)>=1`, the loop must freeze within the stated cap. The
degree is itself a bounded scan of normalized coefficients, with a
separate zero flag. The object induction uses the Booleanized finite
coefficient identities and numerical bounds, not an unbounded divisibility
statement. A supplied nonzero coefficient of `G` makes the minimum scan
nonempty. The horizon for each weight is
`m*max_j degreeCap(A_j)+e*(m-1)`.

## 3. The determinant certificate is a finite carry computation

For column `c<m` and a monomial `A_j Y^j`, write
`j+c=r+m*delta`, where `r<m` and `delta` is zero or one. The matrix entry
is `A_j*f^delta`. For a permutation `sigma`, its chosen indices `j_c`
and carries satisfy

`Σ j_c = m Σ delta_c`.

This follows by summing `j_c+c=sigma(c)+m*delta_c` and using the actual
permutation word's row coverage. A nonzero determinant summand has
`g` exponent `E=Σ a_(j_c)+e Σ delta_c`, so

`m*E=Σ(m*a_(j_c)+e*j_c)>=m*s`.

Equality requires every `j_c=k`, hence the unique permutation
`sigma(c)=(k+c) mod m`. Its carries sum to `k`, and its sign is
`(-1)^(k*(m-1))`. Every other nonzero summand has `E>=s+1`.

Construct `Q` directly by summing those other signed products retaining the factor
`g^(E-s-1)` after extracting `g^(s+1)`. The proven bound makes the exponent natural. This is
a finite construction, not a division by an assumed divisor. Zero summands
are omitted using their checked flags. The known scan horizon is `m^m`;
all products have `m` factors. Booleanized prefix identities give the
required quantifier-free inductions. The actual norm code is linked by
its coefficient Leibniz theorem.

## 4. Reducedness without factorization

The needed finite lemma is `g | B^r -> g | B` for `r>=1`, from the
certificate `U*g+V*g'=1`. It can be derived with polynomial gcd and Bezout,
without roots or irreducible-factor enumeration.

Compute `D=gcd(g,B)` with cofactors `g=D*C`, `B=D*E` and a Bezout identity
`a*g+b*B=D`. Cancellation gives `a*C+b*E=1`. Substitution of `g=D*C`
and its derivative into the squarefree certificate gives the explicit
second identity

`C*(U*D+V*D')+D*(V*C')=1`.

Multiply the two identities to obtain `H*C+J*B=1`. If `g | B^r`, then
`C | B^r`. The finite geometric-sum identity

`1-(J*B)^r = H*C*Σ_(i<r)(J*B)^i`

therefore gives an explicit polynomial inverse of `C`. It follows that
`g | B`. All cancellation is justified by the nonzero factor `D` in the
coefficient-field polynomial domain; when `B=0`, divisibility is direct.
This proves reducedness of the remainder ring through finite identities.

Now `rem(B_k,g)!=0` implies `rem(B_k^m,g)!=0`. The separate certificate
`alpha*g+beta*h=1` makes the class of `h` a unit, so multiplying by `h^k`
and the sign preserves nonzeroness. Thus the parenthesized factor in the
norm identity has nonzero remainder. The coefficient search for `N` is
bounded by its existing buffer length: a failed search would mean every
normalized coefficient vanishes and contradict this residue argument.

## 5. Source binding and completion order

Reuse `GaussianPolynomialMonicNorm` for the actual output,
`GaussianPolynomialMultiplicationMatrix` for its entries,
`GaussianPolynomialDeterminant.coefficient_leibniz` for the output sum,
and `RuntimePermutationWords` for numerical permutation coverage.
`GaussianPolynomialColumnAlternation` supplies an actual adjacent-swap
interface, useful for proving the cyclic-shift sign. Existing exact
coefficient operations, bounded minimum/search, and
`GaussianRationalPolynomialProductDegree` support the finite arithmetic.

The new work is: general univariate division and its degree invariant;
polynomial extended gcd and its certificates; the reducedness argument;
the specialized superelliptic entry formula and carry identity; the
cyclic-shift sign; and the coefficient-level assembly for the original
norm code. Do not treat a host theorem about `Matrix (Fin m) (Fin m)` as
this runtime-numerical derivation.

For the main squarefree rational case, take `g=f,e=1,h=1`. Compute
extended gcd of `f,f'`; a nonzero constant gcd gives `U*f+V*f'=1` after
rescaling. The unit certificate for `h` is immediate. Thus the whole
successful-case producer uses exact finite arithmetic and no root
factorization, formal-series translation, or search for a finite place.
If the gcd test fails, this particular squarefree producer reports that
its hypothesis is unsatisfied; no nonvanishing conclusion is fabricated.
