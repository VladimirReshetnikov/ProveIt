# Separate extension: a convergent all-orders analytic inverse algorithm

Author proof and bounded checks are complete; the separate independent
mathematical audit reported PASS for the complex bounds and inversion
theorem. This is a separately scoped extension of the audited E1–E7
expansion packet. The series below is an analytic Lagrange-inversion
algorithm, not an assertion that a canonical exponential transseries has
been fully sorted or enumerated.

## 1. Holomorphic definitions without winding ambiguities

Fix one of the three branches and a real r0>=100. Write

    p(r)=alpha*(r+epsilon), L(r)=lambda*(r+epsilon),
    y(r)=L(r)−p(r)−1,

with (alpha,lambda,epsilon) equal to (2/3,1,1), (2/3,1,−1),
or (5/7,5/4,1). Put p0=p(r0), y0=y(r0), q0=2^(−p0),
and work on the closed complex disk |r−r0|<=1/4.

All exponentials 2^z mean exp(z*ln2). Define

    d=2^(−p)+2*2^(−p−y),
    a=2^(−2p−2y)/(1+d)^2,
    g(z)=−sum_(j>=1) [binom(2j,j)/(2j*4^j)]*z^j,
    ell_A=L*ln2+ln(1+d)+g(a),
    u=exp(−2p*ell_A),
    b=16u^2/(1−u)^4,
    ell_S=2p*ell_A−ln2+2ln(1−u)+g(b),
    v=exp(−2r*ell_S).

The logarithms here are their Taylor branches at small argument:
ln(1+z) and ln(1−z). In particular we never use principal log(S)
or principal arcosh(S) on this complex disk. S may wind repeatedly.
The displayed ell_A and ell_S are the specified holomorphic logarithms.

Define N(r) by the branch cubic from the audited expansion note, and

    E(r) = {2p(r)(r−1)[ln(1+d)+g(a)]
             +2(r−1)ln(1−u)+r*g(b)
             −(1/2)ln(1−b)+ln(1−v)}/ln2.                (L1)

On the positive real axis this equals log2(mathcal_H(r))−N(r)
by the already proved exact identity. The elementary bounds below prove
that all the formulas above are holomorphic on a neighborhood of the
closed disk, rather than assuming that their branches are well defined.

## 2. Uniform complex bounds

We will prove

    |E(r)|<18*r0^2*q0,
    |D(r;r0)|>2*r0^2,
    |f(r)|<epsilon0 :=16*q0<1/8,                         (L2)

where

    D(r;r0)=(N(r)−N(r0))/(r−r0), D(r0;r0)=N'(r0),
    f(r)=E(r)/D(r;r0).

First p0>=66, y0>=32, and |p(r)|<r0. Since the slopes of p and y
are positive and below one,

    |2^(−p)| <=2^(1/4)q0 <(5/4)q0,
    |2^(−y)| <(5/4)2^(−y0),
    |d|<2q0<=2^(−65),       |a|<q0^2.

For the a bound, use |2^(−2p−2y)|<4q0^2*2^(−2y0)
and |1+d|^(−2)<2. Thus |a|<8q0^2*2^(−2y0)<q0^2.
The convergent logarithm/binomial series now give, writing
Phi=ln(1+d)+g(a),

    |ln(1+d)|<=|d|/(1−|d|)<4q0,
    |g(a)|<=|a|/[2(1−|a|)]<q0^2,
    |Phi|<5q0.                                          (L3)

For the conjugate arguments, let h=r−r0 and z0=r0+epsilon.
Since alpha*lambda lies between 2/3 and 25/28,

    Re(pL) >= (2/3)[r0^2−(5/2)r0+7/16]
            >= (3/5)r0^2.

Indeed Re((z0+h)^2)>=z0^2−2z0|h|−|h|^2, and
r0−1<=z0<=r0+1. The last inequality holds for r0>=100.
As 5r0*q0<1 and |p|<r0, equation L3 yields

    Re(p*ell_A) >= (3/5)r0^2*ln2−1
                 > (1/2)r0^2*ln2.

Consequently

    |u|<2^(−r0^2)<=q0^4,
    |b|<=16q0^8/(1−q0^4)^4<32q0^8<q0^4.                (L4)

The first comparison uses p0<r0 and r0^2>=4r0.
This validates the Taylor branches for u and b and gives

    ell_S=2pL*ln2−ln2+Q,
    Q=2p*Phi+2ln(1−u)+g(b),       |Q|<11r0*q0.           (L5)

To bound v, compare the cubic r(r+epsilon)^2 with its value at r0.
For |h|<=1/4, its difference in modulus is at most

    (1/4)(3r0^2+4r0+1)
      +(1/16)(3r0+2)+1/64 < r0^2.

Multiplication by alpha*lambda<1 preserves this bound. Therefore

    Re(r*pL) >= (2/3)r0(r0−1)^2−r0^2
               >= (3/5)r0^3

for r0>=100. Equations L5 and 22r0^2*q0<1 imply

    Re(r*ell_S) >= (6/5)r0^3*ln2−(r0+1/4)ln2−1
                  > r0^3*ln2,
    |v|<2^(−2r0^3)<=q0^4.                              (L6)

The two elementary inequalities 5r0*q0<1 and 22r0^2*q0<1 follow
at r0=100 from q0<=2^(−66); the corresponding functions decrease
thereafter, since p0'>=2/3. This also checks the estimates uniformly
for every real r0>=100, rather than only at integer indices.

Now |2p(r−1)|<2r0^2 and |r−1|<r0. The first term in the numerator
of L1 is less than 10r0^2*q0 by L3. The other terms have total modulus
less than

    4r0*q0^4 + 2r0*q0^4 + q0^4 + 2q0^4
      = (6r0+3)q0^4 < r0^2*q0.

Using 1/ln2<3/2 gives |E|<(33/2)r0^2*q0<18r0^2*q0.

For the cubic denominator write gamma for its leading coefficient,
so gamma is 4/3 or 25/14 and in particular gamma<2. Exactly,

    D(r0+h;r0)=N'(r0)+(1/2)N''(r0)h+gamma*h^2.

The real bounds N'(r0)>3r0^2 and 0<N''(r0)<12r0 give

    |D|>3r0^2−(3/2)r0−1/8>2r0^2.

Thus D never vanishes on the disk and |f|<9q0<epsilon0=16q0.
Since q0<=2^(−66), epsilon0<=2^(−62)<1/8. This proves L2
with ample explicit slack. All strict estimates persist on a slightly
larger disk, so the claimed holomorphy holds on a neighborhood of its
closure.

## 3. Convergent all-orders inversion and a computable tail

Introduce a complex auxiliary parameter t, distinct from the radix
exponent used in the counterfamily, and consider

    h(t)=−t*f(r0+h(t)).                                  (L7)

Set rho=1/(8epsilon0)>1. On |h|=1/4 and |t|<=rho,

    |t*f(r0+h)|<rho*epsilon0=1/8<|h|.

Rouche's theorem shows that h+t*f(r0+h) has exactly one zero,
counting multiplicity, in |h|<1/4. It is simple; the analytic
implicit-function theorem therefore gives a unique holomorphic h(t)
throughout |t|<=rho, with |h(t)|<1/4 and h(0)=0.

Lagrange inversion gives the convergent series

    h(t)=sum_(n>=1) [(-t)^n/n!]
           * (d/dr)^(n−1)[f(r)^n] evaluated at r=r0.      (L8)

At t=1, the exact inverse of log2(mathcal_H(r))=N(r0) in this
disk is r=r0+h(1). Thus L8 gives an all-orders analytic inverse
algorithm involving only explicitly defined holomorphic functions.
Every finite derivative is well defined, and coefficients can be
computed successively by power-series arithmetic.

Cauchy's coefficient estimate from |h(t)|<1/4 on |t|=rho gives,
for every integer K>=0,

    |h(1)−sum_(n=1)^K [(-1)^n/n!]
       *(d/dr)^(n−1)[f(r)^n] at r0|
      <= (1/4)*rho^(−K−1)/(1−rho^(−1)).                  (L9)

This explicit geometric bound is sufficient for a genuinely convergent
algorithm; it is not a merely formal Lagrange expression. For actual
R>=100 with N(r0)=log2 H(R), the previous bound 0<r0−R<2d<1/4
places the desired real R in this disk, identifying it with the unique
solution above. Conjugation symmetry also makes h(1) real.

Endpoint scope: for an arbitrary r0=100, the value r0+h(1) can be
slightly below 100. In that case the formula refers to the local real
analytic continuation supplied by the same holomorphic definitions, not
to an inverse restricted to the half-line R>=100. In the application
starting from an actual R>=100, one has r0>R>=100, and the recovered
root is exactly that R within the original real range.

The first Lagrange term is −E(r0)/N'(r0), containing all forward
scales. Keeping only its leading 2^(−p0) sector recovers the audited
first exponential correction; the n>=2 terms are uniformly O(q0^2)
by L9. The series is ordered by the artificial parameter t. We do not
claim that every exponential sector has been rearranged into a canonical
transseries, or that this supplies a smooth x-asymptotic across radix jumps.

## 4. Verification status

The independent mathematical reviewer verified the uniform complex-disk
bounds, winding-free holomorphic definitions, Rouché/simple-root
continuation, Lagrange coefficients, and explicit L9 tail, and reported
PASS after the endpoint scope clarification above. The review's separate
packet supplies independent corroborative evidence.

The author checker disk_check.py passed in normal and optimized execution
with byte-identical receipts: 82,094 active checks, 3,601 exact-rational
r0 grid cases for the polynomial bounds, and 2,880 complex samples over
all branches, at disk radii0,1/8,1/4 and r0=100,101.5,128,160,200.
Its logarithmic conjugate estimates avoid floating underflow, and no
principal log(S) or arcosh(S) is used. The largest sampled upper bound
for |f|/(16q0) was below0.0337. Floating checks are corroboration, not
interval certification or a proof by sampling; the argument above
establishes the theorem uniformly for all real r0>=100.
