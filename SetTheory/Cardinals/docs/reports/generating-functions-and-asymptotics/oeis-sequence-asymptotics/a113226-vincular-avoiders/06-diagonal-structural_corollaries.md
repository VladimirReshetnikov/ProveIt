# Differential structure and infinitely many singularities

Root's proposed corollaries, independently reconstructed 2026-10-01.

Let A=exp(T) be the exact A113226 EGF and u=A'/A=T'. Differentiating
(4-exp z)T'-2T=2+exp z-z gives

(4-exp z)u'-(exp z+2)u=exp z-1.

Thus near zero, where u'+u+1=3,

exp z=(4u'-2u+1)/(u'+u+1).

Differentiating and using (exp z)'=exp z gives

3(2u+1)u''-10(u')^2-(2u+8)u'+2u^2+u-1=0,
u(0)=u'(0)=1.

After substitution u=A'/A and multiplication by A^4, this is a
third-order polynomial differential equation for A. Hence A is
differentially algebraic.

On the other hand A is not D-finite. Put z_k=log4+2pi i k for every integer
k. Starting at zero, the square root w=sqrt(4 exp(-z)-1) can be continued
along any finite path avoiding these points. It never equals either i or
-i, since that would require exp(-z)=0. Consequently arctan(w) can also
be continued along the lifted path: its derivative 1/(1+w^2) has no pole
on that path. Every z_k is accessible from zero along such a path.

Near the endpoint z_k use w as local ramified coordinate; then
z=z_k-log(1+w^2). The continued arctangent extends analytically to w=0,
and its value there is an integer multiple j*pi, because
tan(arctan(w))=w under analytic continuation. Thus on every branch

T(z)=z/2+pi(1-3j)/w-3+O(w^2).

The coefficient pi(1-3j) is nonzero for every integer j.
Therefore exp(T) has an essential singularity at w=0, so it cannot have
a holomorphic continuation through z_k. A D-finite germ can have finite
singularities only among the finitely many zeros of the leading polynomial
of its linear differential equation. Infinitely many accessible z_k
contradict that property.

Finally a_n is not P-recursive. Polynomial recursiveness is unchanged by
multiplication or division by n!, since the shifted factorial ratios are
rational functions of n and denominators can be cleared. Therefore
P-recursiveness of a_n would make A D-finite.

These arguments do not estimate subdominant coefficient sectors. The
infinite singularity lattice gives a concrete starting point for that
separate problem.

Bounded searches for A113226 and 12-34 together with D-finite,
P-recursive, and arctangent did not locate this conclusion. The 2025
paper discusses non-D-finiteness for a different interval-order class;
that statement must not be transferred to A113226 as prior proof.
