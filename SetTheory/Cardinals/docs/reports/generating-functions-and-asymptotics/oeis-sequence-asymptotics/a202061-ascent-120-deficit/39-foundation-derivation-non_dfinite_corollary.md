# Non-D-finiteness consequence

Research corollary, 1 October 2026. Depends on the audited exponential growth rate and the upper stretched bound in upper_scale_proof.md. It does not require the sharper logarithmic refinement or a leading asymptotic equivalent.

## Claim

The ordinary generating function A(z)=sum_{n>=0}a_n z^n of classical 120-avoiding ascent sequences is not D-finite over Q(z). Equivalently A202061 is not P-recursive over Q[n].

## Proof

The two-sided exponential-rate estimates give radius of convergence rho=1/mu. The stretched upper bound gives, for each integer k>=0,

sum_n n^k a_n rho^n < infinity.

Consequently A and every derivative extend continuously from [0,rho) to rho, by uniform convergence of the differentiated series. In particular A is C-infinity along the real radius up to rho.

Suppose A were D-finite over Q(z). Its coefficients are nonnegative integers and are exponentially bounded. Their conjugates obey the same bound and their common denominators are 1. Thus A would be a Siegel G-function.

The regularity theorem for G-functions implies that near each finite singularity, on a slit neighborhood, a G-function is a finite sum of convergent terms

(z-rho)^alpha (log(z-rho))^beta H(z-rho),

where alpha is rational, beta is a nonnegative integer, and H is analytic at zero. See Garoufalidis–Bellissard, Algebraic G-functions associated to matrices over a group-ring, Definition 2.2 and Theorem 2.1(c), which states the consequence of the Andre–Chudnovsky–Katz theory:
https://people.mpim-bonn.mpg.de/stavros/publications/algebraicGfunctions.pdf .

A finite convergent power-log expansion of this kind that is C-infinity along a radius is analytic at the endpoint: combine terms with the same exponent and log power; a least surviving noninteger-power or logarithmic term has a finite derivative order at which smoothness fails. Hence no such term survives, leaving a convergent ordinary power series. Therefore A would be analytic at rho.

This contradicts Pringsheim's theorem, because A has nonnegative coefficients and finite radius rho. Thus A is not D-finite.

This uses the arithmetic G-function regularity theorem, not a blanket claim that all D-finite functions have regular singularities (that blanket claim is false). The integer-coefficient and exponential-bound hypotheses are essential in this route.

## Optional field extension

The same conclusion holds over C(z): any bounded-order/bounded-degree complex linear differential relation on a rational power series gives a nontrivial kernel of a matrix with rational entries and finitely many unknowns. Its rank is attained by finitely many rows, so it has a nonzero rational kernel vector. Hence complex D-finiteness would imply rational D-finiteness here.
