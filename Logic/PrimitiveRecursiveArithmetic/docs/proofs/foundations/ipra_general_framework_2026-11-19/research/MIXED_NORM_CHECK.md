# Independent check of the mixed-curve local/global norm theorem

## Verdict

The proposed theorem is correct with **m >= 1** and **d >= 1** over any field K. It remains valid in positive characteristic, including when the characteristic divides m. No derivative, separability, algebraic closure, or factorization hypothesis is used. For the intended applications it is reasonable to state m >= 2.

The local and global rescaling identities have the proposed signs and exponents:
\[
N_G(a+t^m)=t^{ms}D_{\mathrm{loc}}(t),
\qquad
D_{\infty}(t)=t^{mW}N_G(t^{-m}).
\]
The exact local coefficient is
\[
[(X-a)^s]N_G
=b^m\bigl((-1)^{m-1}c\bigr)^k.
\]
Here the notation on the left means the coefficient of T^s in N_G(a+T), not the coefficient of X^s before translating.

Both identities can be replaced by proofs on finite coefficient arrays. In particular the nonvanishing and degree bounds do **not** require general determinant multiplicativity; the literal Leibniz determinant and monic remainder identities suffice. The subsequent all-fiber zero-count proof still needs its own determinant transformation/factor-divisibility lemmas.

## Precise hypotheses

Let
\[
F(X,Y)=Y^m+\sum_{j<m} f_j(X)Y^j,\qquad
G(X,Y)=\sum_{j<m} A_j(X)Y^j\ne0.
\]
Let m,d be positive integers. Every nonzero coefficient polynomial f_j satisfies
\[
m\deg f_j+d j\le md.
\]
Put
\[
W=\max_{A_j\ne0}(m\deg A_j+d j).
\]

Supply a in K and e >= 1 such that
\[
\operatorname{ord}_T f_0(a+T)=e,\qquad
c=-[T^e]f_0(a+T)\ne0,\qquad
\gcd(m,e)=1.
\]
For every j with 0<j<m and f_j nonzero, assume
\[
m\operatorname{ord}_T f_j(a+T)+e j>me.
\]
Only nonzero polynomials have an order in this formulation. A program may totalize the order of zero arbitrarily, but its correctness statement must preserve the nonzero guard.

Translation by a is injective on coefficient polynomials: its inverse is translation by -a. Thus A_j nonzero before translation is equivalent to A_j(a+T) nonzero afterwards. Define
\[
\nu_j=\operatorname{ord}_T A_j(a+T),\qquad
s=\min_{A_j\ne0}(m\nu_j+e j).
\]
There is at least one eligible index because G is nonzero. If two indices give the same weight, then m divides e(i-j); coprimality and 0<=i,j<m give i=j. Hence the minimizing index k is unique. Set
\[
b=[T^{\nu_k}]A_k(a+T)\ne0.
\]

The global f_0 bound implies e<=deg f_0<=d. Also s<=W. These are consequences, not additional required inputs.

## Local nonvanishing: exact finite proof

### Construct the scaled polynomials

Define
\[
F_{\mathrm{loc}}(t,Z)=t^{-me}F(a+t^m,t^eZ),\qquad
G_{\mathrm{loc}}(t,Z)=t^{-s}G(a+t^m,t^eZ).
\]
The displayed negative exponents are only notation for deleting proved initial zeros in coefficient arrays.

For an actual nonzero coefficient [T^q]f_j(a+T), the exponent after scaling is
\[
mq+ej-me.
\]
For j=0 it is nonnegative and equals zero only at q=e. For j>0 it is strictly positive by the local hypothesis. The monic Y^m term gives Z^m. Consequently F_loc is a polynomial in K[t,Z], monic of degree m in Z, and
\[
F_{\mathrm{loc}}(0,Z)=Z^m-c.
\]
Likewise the exponents mq+ej-s in G_loc are nonnegative. Only the unique pair (q,j)=(nu_k,k) has exponent zero, so
\[
G_{\mathrm{loc}}(0,Z)=bZ^k.
\]

This is a bounded scan through finite coefficient arrays. It does not construct a Laurent series or an unbounded valuation.

### Derive the norm identity without Laurent objects

Let M(X) be the original multiplication matrix of G modulo F, in the basis
1,Y,...,Y^(m-1). Let L(t) be the multiplication matrix of G_loc modulo F_loc, in the basis 1,Z,...,Z^(m-1).

The original remainder identity in column j is
\[
G Y^j=\sum_{r<m}M_{rj}(X)Y^r+Q_j(X,Y)F(X,Y).
\]
Substitute X=a+t^m and Y=t^eZ. Since F after substitution is t^(me)F_loc, reducing the resulting identity modulo the monic F_loc yields the **polynomial** entry identity
\[
t^{s+ej}L_{rj}(t)=t^{er}M_{rj}(a+t^m)
\quad(r,j<m).
\tag{L}
\]
Every exponent in (L) is nonnegative. This avoids dividing by t.

For a permutation sigma, multiply (L) with r=sigma(j) over all j. Since
\[
\sum_j\sigma(j)=\sum_j j,
\]
the two sides have a common monomial t^(e sum_j j). Cancellation of that monomial is just injectivity of coefficient shift; it holds even over a coefficient ring with zero divisors. Thus
\[
t^{ms}\prod_j L_{\sigma(j),j}(t)
=
\prod_j M_{\sigma(j),j}(a+t^m).
\]
Multiply by the permutation sign and sum the finitely many terms:
\[
t^{ms}\det L(t)=N_G(a+t^m).
\tag{N}
\]
No general determinant-of-a-product theorem is needed for this identity.

### Compute the initial determinant directly

Monic reduction commutes with evaluation at t=0. Therefore L(0) is multiplication by bZ^k modulo Z^m-c.

In column j there is exactly one nonzero entry:
\[
r=(j+k)\bmod m,\qquad
L_{rj}(0)=b\,c^{\lfloor(j+k)/m\rfloor}.
\]
The map sigma_k(j)=(j+k) mod m is a permutation. Its tuple is
(k,k+1,...,m-1,0,...,k-1); its inversion count is k(m-k).
Exactly k columns wrap around, so the unique nonzero determinant term gives
\[
\det L(0)=(-1)^{k(m-k)}b^m c^k
=b^m\bigl((-1)^{m-1}c\bigr)^k\ne0.
\tag{C}
\]
The parity identity uses the evenness of k(k-1). The argument covers k=0, m=1, and characteristic two.

From (N) and (C), the least nonzero exponent of t in N_G(a+t^m) is ms. Since the coefficient of t^(mq) there is the coefficient of T^q in N_G(a+T), it follows that
\[
\operatorname{ord}_{X=a}N_G=s,\qquad
[T^s]N_G(a+T)=\det L(0).
\]
In particular N_G is nonzero.

## Global upper degree: a cleaner bounded invariant

The proposed Laurent rescaling at infinity is sound. A direct weight proof is easier to compile and avoids Laurent encoding.

Give a monomial X^iY^r the weight mi+dr. Replacing a term C(X)Y^h with h>=m by its remainder contribution
\[
-C(X)\sum_{r<m}f_r(X)Y^{h-m+r}
\]
does not increase any monomial weight: for a term X^q of f_r,
\[
mq+dr\le md.
\]
Hence, during monic reduction of GY^j, every current nonzero coefficient
[X^iY^r] has weight at most W+dj. This is a finite coefficient-support invariant.

The final multiplication matrix therefore satisfies
\[
[X^i]M_{rj}\ne0
\Longrightarrow mi+dr\le W+dj.
\tag{W}
\]
This statement makes sense even when an entry is zero; it needs no degree sentinel.

Now consider a coefficient contribution to one Leibniz product,
\[
\prod_{j<m}M_{\sigma(j),j}.
\]
If it is nonzero, each selected entry coefficient is nonzero. Apply (W) to the selected exponents i_j and add:
\[
m\sum_j i_j+d\sum_j\sigma(j)
\le mW+d\sum_j j.
\]
The permutation sums cancel. Since m>=1,
\[
\sum_j i_j\le W.
\]
Thus every determinant coefficient above W vanishes. Together with local nonvanishing, this proves
\[
\deg N_G\le W.
\]

One can use an equivalent finite product-support invariant, avoiding an explicit tuple of convolution indices: after columns 0,...,ell-1, every nonzero coefficient at q has
\[
mq+d\sum_{j<\ell}\sigma(j)
\le \ell W+d\sum_{j<\ell}j.
\]
Its step is exactly finite polynomial convolution. At ell=m the sums cancel. This is particularly well suited to QF induction on the actual determinant-word product program.

## Finite point and subspace conclusions

For a supplied finite list of distinct common zeros of F and G over K, the already developed finite norm argument gives
\[
\#\text{list}\le\deg N_G\le W.
\]

The fiber argument must retain distinct pairs, not merely distinct first coordinates. For a group over X=a' with t distinct ordinates, F(a',Y) is monic of degree m, so t<=m. Completing its t evaluation rows to an invertible matrix produces t polynomial rows vanishing at a'. This contributes (X-a')^t to N_G. Distinct first-coordinate groups yield coprime linear powers; their accumulated exponent is the original list length.

The local root a used to prove norm nonvanishing need not occur in the supplied list and need not equal any of the fiber abscissae a'. Keep those two roles distinct in notation.

For a weighted monomial list B_L={X^iY^j:j<m, mi+dj<=L}, a nonzero annihilator of a proper supplied row span produces a nonzero reduced G with W<=L. The same argument gives a fiber cap L. It remains necessary either to construct the nonzero annihilator by bounded elimination or to display exactly the certificate hypothesis being used. The local criterion concerns the fixed curve F and therefore works simultaneously for every nonzero reduced G arising from any such subspace.

## Useful check examples

### Original binomial application

For F=Y^2-X^4-X, G=Y-X^2:
\[
N_G=X^4-(X^4+X)=-X.
\]
Take a=0, e=1, c=1. The unique least local weight is s=1 at k=1, b=1, so the initial coefficient is -1. The global weight is W=4; leading cancellation lowers the actual degree to 1. This demonstrates why the local criterion is stronger than a successful top-weight determinant test.

### A genuinely mixed curve

For
\[
F=Y^2+XY-X^4-X,\qquad G=Y-X^2,
\]
take m=2,d=4,a=0,e=1,c=1.
The global weights are 8 for -X^4 and 6 for XY; the local mixed coefficient has 2 ord(X)+1=3>2. In the basis 1,Y,
\[
M_G=
\begin{pmatrix}
-X^2 & X^4+X\\
1 & -X^2-X
\end{pmatrix},
\qquad
N_G=X^3-X.
\]
Again s=1 and the initial coefficient is -1; the degree is 3<=W=4.
The three common rational zeros are (-1,1), (0,0), and (1,1). This checks the sign and illustrates mixed terms without global coprimality.

### Why the conditions cannot be silently omitted

For F=Y^2-X^2 and G=Y-X, the norm is zero and the common-zero set is unbounded over Q. The only zero of f_0 has order 2, which is not coprime to m=2.

Failure of the local criterion does not imply zero norm: for F=Y^2-X^2-X^3 and G=Y-X, the norm is -X^3 although the zero of f_0 at zero has order 2. The criterion is sufficient, not necessary.

## Suggested bounded-invariant implementation plan

1. **Polynomial representation.** Use the current exact coefficient codes and their value-equality, not raw code inequality. Define shifts and monic reduction with total defaults; correctness guards state shapes and positive denominator requirements.
2. **Translation.** Prove the coefficient identity for P(a+T) and inverse translation. This supplies nonzero preservation and finite order scans.
3. **Local checks.** Express the order hypotheses by zero coefficient blocks and one nonzero coefficient. The global coefficient-degree caps and local zero blocks are fixed bounded syntax. Compile them with existing BFm/bitF machinery.
4. **Scaled arrays.** Insert each nonzero coefficient at exponent mq+ej-me or mq+ej-s after proving it nonnegative. Maintain equality of every bounded coefficient with the symbolic substitution and identify the t=0 specialization.
5. **Remainder bookkeeping.** For each column j, maintain the identity H=QF+R plus current Y-degree bound and support-weight cap. Each reduction lowers the current Y-degree; because G is reduced, GY^j starts below 2m-1.
6. **Local matrix identity.** Derive (L) at the original matrix and actual scaled matrix, using coefficient equality and monic remainder uniqueness. Do not substitute an arbitrary matrix satisfying a desired conclusion.
7. **Determinant words.** Use the existing numerical permutation scan. Derive (N) with a product-prefix invariant and permutation sum identity; derive (C) by the one nonzero cyclic word, wrap count, and inversion parity.
8. **Global support.** Prove (W) during the same reduction; then the determinant-word product-support invariant above. Sum the actual signed products to obtain zero coefficients above W.
9. **Assemble local/global norm.** Export an all-numerical endpoint: valid input and the supplied local certificate imply the actual norm program is nonzero, its first translated coefficient is the displayed value, and its degree is <=W.
10. **Point count.** Attach the remaining numerical fiber multiplicity and accumulated divisor lemmas. The current actual WZ=I fiber inverse can replace the literal Vandermonde product identity in this proof, once determinant transport is available.

Every induction invariant in these steps concerns finitely coded arrays, indices, coefficients, and numerical comparisons. Booleanizing its bounded quantifiers gives the permitted QF induction formula. A complete Lean proof still needs the displayed actual-program linkage; a native theorem about abstract polynomials alone would not establish the iPRA endpoint.

## Novelty relative to inspected sources

The coherent-methods source already proves the global weighted mixed-curve theorem under coprime infinity weights, and already gives a general noncoprime initial-determinant certificate. Those parts must be credited.

Neither that inspected source nor the finite-demand norm section contains the finite-place criterion above, or its combination with the global support cap to obtain a uniform proper-subspace bound without gcd(m,d)=1. The present local/global theorem is therefore an extension relative to those audited reports. This audit does not claim a literature-wide novelty result.

No new source access or whole-repository rebuild was needed for this independent mathematical check.

