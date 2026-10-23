# Independent proof review: encode residuals, not their sum of squares

## Statement

Let r_1,...,r_m be integer polynomials of degree at most d in n nonnegative
unknowns, with n≥2. Suppose not all r_j(0) vanish. Choose distinct positive
weights w_i that distinguish every pair of multisets of at most d positions.
More generally it suffices that the support monomials of every r_j be isolated
among all monomials of degree at most d. Let W=max w_i and s=dW+1.
Reorder and, if necessary, negate one residual so that r_m(0)>0. Put

    H_j=j s,  j=1,...,m;       K=H_m+dW.
    c_(j,alpha)=(d−|alpha|)! prod_i(alpha_i!) [z^alpha]r_j.
    D(t)=sum_(j,alpha) c_(j,alpha) t^(H_j−alpha.w).

Choose M≥1 bounding all |c_(j,alpha)| and a fixed square power of two
beta>4M(n+1)^d. For variables f,g define

    b=1+3f, B=beta b^d, ell=sum_i B^w_i,
    N0=B^(W+1), N1=4B^(K+1), N=N0 N1,
    Mask=N0−1−(b−1)ell,
    T=Mask+(B−2)(sum_j B^H_j)N0,
    J=2(1+g)^d D(B)+B sum_(v=0)^K B^v,
    S=g+J N0,
    R=(S+T+1)N+T+1, X=(N−1)R, Y=N²,
    Ccap=bB^W.

On the branch f≠0, b a square power of two, and0≤g<2Ccap,

    Y divides binomial(2X,X)

holds exactly when g=sum_i z_i B^w_i for0≤z_i<b and all r_j(z)=0.
If a common nonnegative zero exists, arbitrarily large square powers b of
two give witnesses with b≤g<Ccap. These are the same source-interface
conditions as in the single-output Sun adapter, with all witnesses and
exponents fixed as specified.

## Why the separated targets work

The j-th summand of D has support in[H_j−dW,H_j]. These intervals are
disjoint because adjacent targets differ by dW+1. Each exponent therefore
has at most one weighted residual coefficient, so the coefficient sup-norm
of D is at most M, independently of the number m of residuals.

For a decoded vector z, let C(t)=(1+sum_i z_i t^w_i)^d. Its support lies
in[0,dW]. The product with the j-th part of D has support in
[H_j−dW,H_j+dW]. Every other target H_k lies outside this interval.
Consequently no other residual contributes to the coefficient at H_j.
Within its own block, the isolated-support property and multinomial theorem
give the coefficient d!r_j(z), exactly.

The product intervals need not be disjoint. That is harmless: for any
exponent v,

    |[t^v](C D)|≤M sum_u [t^u]C
                  =M(1+sum_i z_i)^d < B/4.

This argument sums the nonnegative coefficients of C and uses the global
sup-norm of D. It does not multiply by m and does not assume that arbitrary
off-target product addresses are different.

## Positivity, ranges, and simultaneous carry tests

The highest term of D is d!r_m(0)t^H_m, whose coefficient is positive.
All other terms have lower exponent. Since B−1>M, their absolute sum at B
is less than B^H_m; hence D(B)>0. Also D(B)≤M sum_(v=0)^H_m B^v.
The estimates in the single-output proof therefore give0<J<N1,
0≤g<N0 and0≤S<N. The high mask has digits B−2 at the distinct targets,
and zero elsewhere, hence it is below B^(H_m+1)<N1. Thus0≤T<N.

The three-block identity and Legendre's formula yield

    v2(binomial(2X,X))=2log2(N)−carry_count(S,T).

The low-block no-carry test decodes the desired vector. For the high block,
write A(t)=C(t)D(t)+(B/2)sum_(v=0)^K t^v. Its coefficients a_v satisfy
0<a_v<B, and J=2A(B). Dividing both summands of the high-block addition by2
shows that there is no carry if and only if, at every selected target H_j,
the digit a_(H_j) has no overlapping1-bit with B/2−1. The only such digit
strictly between0 andB is B/2. Thus all selected coefficients d!r_j(z)
vanish. Unlike a sum or product of the residuals, this cannot hide a
nonzero residual by cancellation with another residual.

Because one residual is nonzero at the origin, a common zero is not the
zero vector. Positive positions then give g≥B≥b. Increasing an even
exponent in b=2^k ensures b=1mod3 and provides arbitrarily large admissible
source bounds. Conversely the mask and the22 selected tests recover all
source equations, not merely a necessary numerical condition.

## Application and scope

For the31-variable quadratic parent, use d=2 and m=22. Its fifth residual
at the all-one positive assignment is exactly1. Move that residual to the
last block. No change to the actual zero set is required. The source can
therefore use B2 rather than B4 positions, and it stores the coefficients
of22 quadratics rather than those of their quartic sum of squares.

The complete four-port coefficient binding and the existing proof that the
quadratic parent represents a finite ZFC refutation remain prerequisites.
The published Sun2026 Lucas/binomial bridge must then be composed with this
new source theorem. This review does not certify an unprovided final circuit
or assert that the final degree is a simple ratio of the position bounds.

The construction is a concrete synthesis of classical no-carry, factorial
coefficient, additive-number-theory, and Lucas-sequence ideas. Bose–Chowla
provides a classical source of B_h sets; a supplied finite set can instead
be certified by exhaustive integer addition. No new general B_h theorem,
universal-variable theorem, or global minimality claim is made.

Primary classical source identified for attribution: R.C.Bose and S.Chowla,
Theorems in the additive theory of numbers, Comment.Math.Helv.37(1962–63),
141–147. Journal repository record: https://repository.ias.ac.in/8578/ .
The present review relies on explicit finite certificate checks, not on an
unverified use of that theorem.
