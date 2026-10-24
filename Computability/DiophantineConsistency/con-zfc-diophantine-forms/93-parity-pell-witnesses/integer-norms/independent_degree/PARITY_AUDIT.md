# Independent review of the three-root parity reconstruction

This is an ordinary mathematical audit of the proposed 15-integer reduction,
performed separately from the equation builder. It is not a formal-kernel
certificate and does not newly prove the inherited native calibration.

## Hypotheses inherited from the retained source rows

The native parameters satisfy q=beta(3J3+1)+1, W=12w3+4, X=qW,
Y=(2v_scale+1)q^3, a=(X+1)Y, Delta=(a+2)^2-1, and beta is the fixed
large positive Mersenne integer. Hence q,W,Y are nonzero and their magnitudes
make Delta>1 before any Pell root is recovered.

The retained simultaneous positivity guard proves eta(k-eta)>0. Thus
|k|>=2, eta and k have the same sign, and 0<|eta|<|k|. The definition
c=kY+eta then proves c is nonzero, because Y is a nonzero integer.
Consequently d=c^4>0.

Put m=XY^2, A0=1+m(m+1)k^2, S=k(2m+1), Q=Delta(f^2-1),
and let V be the retained integer CRT expression cTf-Rf^2-c.
For every integer m, m(m+1)>=0, so A0>=1. Also

```
S^2-A0=k^2(3m^2+3m+1)-1>=3,
```

because |k|>=2. Thus S is nonzero and S^2>A0, with no assumed sign of X.
The merged root coordinate z=n+2mk+2SV is odd, both for n=2n0+1 and
for n=2(n0-hYR)+1.

## The octic norm and its exceptional branches

For rational A,B,C, the polynomial

```
[(z^2-A-B-C)^2-4(AB+AC+BC)]^2-64ABCz^2
```

is the product over all eight choices of signs of z plus or minus their
three square roots. Thus its vanishing is equivalent over the complex
numbers to one such signed sum being zero.

Here A=4A0, B=Q/d, C=4S^2(QV^2-1)/(Q-1). The clearing denominator
is D=d(Q-1); the delivered polynomial is exactly D^4 times this norm.
Q=1 is impossible: Delta>1 is an integer and Q=Delta(f^2-1).
Therefore clearing denominators does not add zeros.

It is essential to exclude f=0 and f=+/-1 before assuming Q>1.

* If f=0, then Q=-Delta<0. A and C are positive, while B is strictly
  negative. The roots of A and C are real and every root of B is nonzero
  purely imaginary. No signed sum of them can equal the real z.
* If f=+/-1, then Q=0, B=0 and C=4S^2. Vanishing would imply
  z=+/-2sqrt(A0)+/-2S. Since z is odd, this would force 4A0 to be the
  square of an odd integer, impossible modulo four.

Thus every zero has |f|>=2 and Q>1. If V=0, then C<0 whereas A,B>0;
again a lone imaginary radical cannot occur in a real signed sum. Thus
|V|>=1 and Dy=(QV^2-1)/(Q-1)>=1.

## Why three rationally combined roots must each be rational here

For nonzero rational radicands, distinct nonsquare square classes give
linearly independent character subspaces in their multiquadratic field.
This can be proved directly by averaging against the sign automorphisms.
Therefore a nonzero rational sum of three square roots has either all
three roots rational or one rational root with the remaining two irrational
roots canceling. In the latter case their radicands are equal.

All three possible cancellations are excluded:

* A=C would give A0=S^2 Dy>=S^2>A0.
* A=B would leave z=+/-2S sqrt(Dy). This makes sqrt(Dy) rational. The
  adjacent-coefficient Pell descent for QV^2-(Q-1)y^2=1 makes y an
  integer; then z is even, a contradiction.
* B=C would leave z=+/-2sqrt(A0). Rational square-root integrality makes
  sqrt(A0) an integer; again z would be even.

Thus all three roots are rational. Write their signed roots as 2tau,i,2Snu.
A0 integral implies tau integral. Adjacent-coefficient Pell descent makes
nu integral. The signed-sum identity then gives

```
i=z-2tau-2Snu,
```

so i is an odd integer. This last step is important: the rationality of
sqrt(Q/d) alone would not establish its integrality.

It follows that

```
tau^2=A0,
(ic^2)^2=Q,
QV^2-(Q-1)nu^2=1,
```

and r=(i-1)/2 restores the old unrestricted integer scale coordinate.
These are exactly the three removed source equations. No branch assumes
positivity of f, tau, i or nu; all their signs are legitimate.

## Reverse witness construction

Starting with an old source solution, take its integer tau,nu and odd
integer i=2r+1. Define z=2tau+i+2Snu. Then z is odd and the norm vanishes.
For the uncentered version set n0=(z-2mk-2SV-1)/2. For the centered version
add hYR to this value. Both are integers, and n0 is an unrestricted
integer coordinate. Every retained source coordinate remains unchanged.
Thus completeness does not require an estimate that n0 be positive.

The reduction therefore gives existence equivalence with the source,
assuming its retained universal guard and ordinary adjacent-Pell descent
lemmas. The new exception analysis and square-class argument cover every
signed integer assignment; finite tests alone would not do so.
