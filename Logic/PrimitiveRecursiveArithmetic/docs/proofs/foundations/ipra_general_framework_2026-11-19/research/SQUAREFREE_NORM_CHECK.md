# Independent check: squarefree constant polynomial via a finite reduced algebra

## Verdict and assumptions

The proposed squarefree extension is correct.

Fix a field K with exact arithmetic, a nonconstant polynomial f of degree d, and a displayed polynomial Bezout identity
\[
A f+B f'=1.
\]
For every m>=1 and every nonzero reduced polynomial
\[
G(X,Y)=\sum_{j<m}A_j(X)Y^j,
\]
the multiplication norm of G modulo Y^m-f(X) is nonzero. Its degree is at most
\[
W(G)=\max_{A_j\ne0}(m\deg A_j+d j).
\]
Thus the finite zero-count and proper-subspace fiber caps extend without gcd(m,d)=1 and without a rational root or a factorization of f.

The coefficient algebra R=K[u]/(f) is generally **not a field**. The proof must use reducedness, not cancellation of arbitrary nonzero elements of R. That distinction is essential.

If f is not monic, normalize it for the quotient representation using its nonzero leading coefficient. This does not change the ideal (f), the original curve Y^m=f(X), or the Bezout certificate.

## Why the local argument applies

In R[T], f(u)=0 and
\[
f(u+T)=f'(u)T+T^2Q(T).
\]
The supplied Bezout identity gives
\[
B(u)f'(u)=1,
\]
so c=f'(u) is a unit. Hence the local constant term -f(u+T) has order exactly one.

Each nonzero A_j in K[X] remains nonzero when viewed as A_j(u+T) in R[T]. Indeed K embeds in R because deg f>=1, and translation by u is an automorphism of R[T] with inverse translation by -u. No test of algebraic roots is involved.

Let
\[
s=\min_{A_j\ne0}\left(m\operatorname{ord}_T A_j(u+T)+j\right).
\]
The residue of the weight modulo m determines j, so the minimizing index k is unique. If b is its nonzero initial coefficient in R, the finite monic-reduction and determinant-word argument gives
\[
[t^{ms}]N_G(u+t^m)
=b^m\bigl((-1)^{m-1}c\bigr)^k.
\]
This coefficient is nonzero: reducedness gives b^m!=0, and multiplication by a power of the unit c preserves nonzero elements. The sign is a unit in every characteristic.

Therefore N_G(u+T) is a nonzero polynomial over R. If the original N_G in K[X] were zero then its substituted image would be zero, a contradiction. The global weighted-support argument remains over K and gives deg N_G<=W.

The proof works when char K divides m. It does not require separability of Y^m-f over K(X).

## Reducedness without choosing an irreducible factor

Here is a completely finite proof suitable for the arithmetic development.

Suppose a polynomial representative b satisfies f|b^n with n>=1. If b=0 the conclusion is immediate. Otherwise use the polynomial Euclidean algorithm over K to construct
\[
g=\gcd(f,b),\qquad f=gh,\qquad b=gv,\qquad U f+V b=g.
\]
The gcd may be normalized to be monic. Since f!=0, g!=0, so cancellation in K[X] gives
\[
Uh+Vv=1.
\tag{1}
\]
Differentiate f=gh, and substitute it into the original squarefree certificate:
\[
\begin{aligned}
1&=Af+Bf'\\
 &=Agh+B(g'h+gh')\\
 &=g(Ah+Bh')+h(Bg').
\end{aligned}
\tag{2}
\]
Thus both g and v have explicit inverses modulo h: Ah+Bh' for g, and V for v.

The divisibility f|b^n says
\[
g^nv^n=ghq.
\]
Cancel g to obtain
\[
g^{n-1}v^n=hq.
\tag{3}
\]
Modulo h, the left side of (3) is a product of units, using (1) and (2); the right side is zero. Multiplying by the explicit inverse
\[
(Ah+Bh')^{n-1}V^n
\]
shows that 1 is divisible by h. Consequently h is a unit polynomial, and f|b.

For the canonical representative with deg b<deg f, this forces b=0. Thus R has no nonzero nilpotent, uniformly in the supplied exponent n. The argument uses polynomial Euclid, the formal product rule, finite powers, coefficient equality, and degree arithmetic. It does not choose an irreducible factor.

## Arithmetic implementation boundary

- Polynomial Euclid is padded to an explicit bound on decreasing degrees; it is a fixed PR procedure over the exact coefficient field.
- The Bezout certificate may be supplied, or constructed by the same bounded Euclid procedure and checked to have constant gcd one.
- R is represented by canonical remainders of degree less than d. Its addition and multiplication are finite coefficient operations followed by monic remainder; equality is exact coefficient equality.
- The derivative inverse is the actual remainder of B, not an asserted field property.
- Orders of zero polynomials are guarded; all order scans and minima are bounded by actual coefficient-array lengths.
- The nonvanishing proof must apply to the actual norm program after base change, using proved monic-reduction and determinant specialization identities.
- The residue algebra and the local rescaling are auxiliary proof data. The final nonzero norm and point-count sentences concern the original field, curve, coefficients, and finite point list.

## Examples

For f=X^4+1 over Q, a Bezout certificate is obtained from
\[
f-\frac X4 f'=1.
\]
There is no rational root of f. With m=2 and G=Y-X^2, the exact norm is
\[
N_G=X^4-f=-1.
\]
Thus the two equations have no common point over any field extension of Q. The global top-weight determinant vanishes, but the finite reduced-algebra local proof still certifies nonzero norm.

For f=X^d+X, squarefreeness over Q holds for d>=2: f=X(X^{d-1}+1), and simultaneous f=f'=0 would force at a nonzero root dX^{d-1}+1=1-d=0, impossible. This is an optional second certificate for the earlier family; its supplied simple root at zero already gives the shorter local proof.

## Relation to the inspected sources

The inspected finite-demand and coherent-methods norm sections do not contain this finite reduced-algebra squarefree argument. They already supply the norm and weighted-support methodology, the fiber multiplicity argument, and a leading-initial-form certificate. The present result should be described as a factor-free certificate/embedding extension relative to those sources, not as a claim that the underlying irreducibility phenomenon is newly discovered mathematics.

This is an independent mathematical check, not a compiled Lean result.

