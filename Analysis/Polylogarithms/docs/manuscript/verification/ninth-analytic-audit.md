# Ninth-batch analytic audit, 10 October 2026

This records an independent audit, separately from immutable delivered reports
and freshly repeated finite suites. The corrected Choi coefficient families are now integrated with their
all-order proof; the other additional families retain the scope below. The 446-page book already proves the shared
Stieltjes closure, undilated derivative contacts and collective trace action.

## Corrected Choi family: all-order proof

Let E_r(n) be r! times the coefficient of u^r in the finite product
product_(j=1)^n (1+u/j). Put E_0(n)=1. Near (u,v)=(0,0), Gauss summation gives

    sum_(n>=0) (1+u)_n (1+v)_n / ((n!)^2 (n+1)(n+2))
      = Gamma(1-u-v) / (Gamma(2-u) Gamma(2-v)).

The factor is 1/2 times 2F1(1+u,1+v;3;1), since
(3)_n=n!(n+1)(n+2)/2. The series converges normally on a small closed
polydisc: its terms are O(n^(-2+Re(u+v))). Cauchy differentiation therefore
justifies every fixed coefficient. Setting v=0 gives 1/(1-u), so

    sum_(n>=1) E_r(n)/((n+1)(n+2)) = r!,  r>=1.

Differentiating first in v at zero gives

    (psi(2)-psi(1-u))/(1-u)
      = (1 + sum_(j>=1) zeta(j+1) u^j)/(1-u),

using the normally convergent digamma Taylor expansion at one. Therefore

    sum_(n>=1) H_n E_r(n)/((n+1)(n+2))
      = r! (1 + sum_(j=2)^(r+1) zeta(j)),  r>=0.

In particular sum H_n^2/((n+1)(n+2))=1+zeta(2). This is also proved directly
by summation by parts: sum H_(k-1)/(k(k+1))=1 and
sum 1/(k^2(k+1))=zeta(2)-1. The r=t=0 double-generator coefficient has an
n=0 contribution 1/2 and must retain it or subtract it explicitly.

Primary-source comparison: the publisher PDF of J. Choi, Abstract and Applied
Analysis 2014, Article 501906, printed page 6, equation (41), was independently
read through its mathematical text extraction at
https://onlinelibrary.wiley.com/doi/pdf/10.1155/2014/501906 . It prints twice the
value above. Equations (42)--(46) print the same factor-two sequence. The
sixth-order Bell formula also determines the intended harmonic-order terms.
The web PDF screenshot did not return inspectable pixels to this session and
both direct publisher downloads returned HTTP 403. Accordingly this record
claims text comparison and algebraic correction, not fresh visual inspection
of the two typography-level misprints. The delivery's visual observation
remains a separately attributed historical record.

Classical Gauss input was checked in NIST DLMF 15.4.20:
https://dlmf.nist.gov/15.4.E20 . The general corrected formulas above follow
from the displayed proof and do not need numerical recognition.

## Unequal dilations: audited overlap and the exact half-shift value

The Mellin and Stieltjes-harmonic reports independently agree with the
collective covering formula already proved in the book. They extend it to
argument derivatives and products of disjoint singular grids. Set
 d=gcd(p,q), P=p/d, Q=q/d, theta={Pa}; require 0<theta<1.
Fourier orthogonality leaves indices Q*l and -P*l. Consequently the ordinary
spectral correlation is Q^(s-1) P^(t-1) C(s,t;theta). Canonical pullbacks
and ambient-coordinate finite parts differ by their explicit local contacts.
Those contacts explain the log(lcm(p,q)) term; discarding them is invalid.

In the proposed polygamma formula, at theta=1/2 and odd total derivative
order N=r+k, the two spectral zeta derivatives and the common logarithmic
terms cancel. The remainder is

 N! P^k Q^r (-1)^(k+1) (H_k-H_r) (2^(N+1)-1) zeta(N+1).

For p=2,q=3,a=1/4,r=0,k=1, it gives pi^2. This specialization is consistent
with the already accepted undilated contact theorem and the finite Fourier
frequency reduction. Full unequal-grid and all-index covering integration
still requires its own manuscript normalization and proof presentation.

## Remaining audit boundary

Near-critical crossing, all-jet collision regularity, nested-regulator
endpoint interchange, full trilinear continuation and the depth-filtered
Cayley retraction have fresh finite replays or running suites, but this note
does not promote their all-parameter analytic statements. The frozen S6 and
S8 period identities remain conjectural. No external originality, numerical
period independence or proof-assistant certification is inferred.

## Mellin master: reviewed analytic domain

The finite Mellin-Lerch transform proof was independently reviewed in
sections/02-mellin.tex. Its common strip -1<Re(a)<N is justified uniformly
for every spectral order: shift the polylogarithm order to a positive real
part, use its Fermi integral, then apply powers of x*d/dx. On compact subsets
of the z-plane slit along the nonpositive real axis, this bounds the small-x
function by O(x) and its large-x growth by a fixed logarithmic power.
The ordinary integral is holomorphic throughout the stated strip.

For N=1, the beta-resolvent identity is proved first where its separate
partial fractions converge and then continued as their integrable difference.
Integration by parts raises N; the resulting finite polynomial kills the
first N-1 Lerch terms and places the remaining shift at N-a, safely in the
right half-plane. The residue of the Lerch continuation at log(z) is
independent of the shift, so the polylogarithmic subtraction removes the
positive-axis jump. Its germ at z=1 is a Hurwitz-zeta difference with canceled
spectral residue. The original integral proves that integer a poles are
removable. All of these restrictions must accompany canonical integration;
individually continued terms may not be combined on inconsistent sides of
the positive-axis cut. This master proof has been audited; full manuscript
integration and the other mixed-reflection and dilation claims remain separate.
