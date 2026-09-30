# Exact power-of-three geometry in 43 operations

The retained ternary positive-branch kernel, with scale q and the free
comparison of its existing `r1=r+1` register with q, has positive witnesses
**exactly when q=3^t for some integer t>=1**. It costs **43=25M+18A**,
with11 equations and17 positive auxiliaries in addition to q. This is
geometry only, without stream bounds, controller, input or acceptance.
The complete universal bound remains76.

## 1. Literal source

Supply positive q and the retained coordinates

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux.

Set `X=wq,Y=sq,Delta=a^2+6a+8,U=2r+1+jc`. The source is

    r+1=q,
    ((XY)^2+X)(kY)^2=tau(tau+1),
    c=kY+eta, k=eta+zeta, k=r+1+hXY,
    a=Y(X+1), d=X+ac+ga(6a+8),
    d^2=1+Delta*c^2,
    (ic^2)^2=Delta*(f^2-1),
    Delta*(f^2-1)(U^2-y_aux^2)=1-y_aux^2,
    U=c+of.                                             (1)

The [literal source](pell_kernel_power_three43.py) changes only the
scale references in the existing43 core to the supplied q, and adds the
free comparison `r1=q`. No power of q is computed or assumed. The full
coefficient `ic^2`, both positive congruences and all core instructions
remain. All eighteen supplied positive coordinates appear in the eleven
independently expanded polynomials.

## 2. Soundness before the exponent congruence

Positive r excludes q=1. If q is even, X,Y,a are even. Both Delta and
`6a+8` are even, and the exponent equation makes d even. Its main norm
would instead have `d^2=1 mod2`, a contradiction. Thus q is odd.
The value q=3 already has the required geometry; the projection does not
need to classify every possible kernel witness at that parameter.

Consider odd q>=5, so `r=q-1>=4`. Put `A=a+3`, `E=XY`,
`P=2XY^2+1` and `J=2r+1`. The preliminary bounds are

    X,Y>=q>=5, E>=q^2>r+1,
    a>=q(q+1)>J, P>A.

The main and first Pell discriminants are nonsquares because they are
the squares of integer parameters A,P>1, minus1. Classify their positive
solutions as `c=psi_A(p),d=chi_A(p)` and `k=psi_P(n)`.
The first congruence gives `n=r+1 mod E`, hence n>=r+1. Since P>A and
the positive interval gives c>k, parameter and index monotonicity imply
`p>=n+1>=r+2>=6`. Consequently

    c>=(2A-1)^(p-1)>A^5>A*(A^2-1)^2,
    c>J, 2p<=c.

These are the generic relaxed-rank and positive half-parameter hypotheses
already verified for the retained ternary kernel. They recover
`p=J`, with `c=psi_A(J),d=chi_A(J)`. If n were larger than r+1, its
next permitted value r+1+E would exceed J, and P>A would contradict
c>k. Thus `n=r+1` exactly.

Let `T=XY^2` and `xi=(X+1)^(2r)/X^r`. The retained shift-three estimates
give

    c/k >= xi*(1+5/(2a))^(2r)*(1+1/(2T))^(-r) > xi,
    c/k < xi*(1+3/a)^(2r).

The strict lower inequality follows from `10T>a`, already true for
X,Y>=5. Use it first: `xi<Y+1` and `xi>X^r` imply `Y>=X^r`, so
`a>X^(r+1)`. Therefore `6r/a<6r/5^(r+1)<1/2` for r>=4, and the upper
estimate becomes

    c/k < xi*(1+12r/a),
    0<c/k-xi<24r/(X+1).                                (2)

No preliminary small upper-error bound has been assumed.

## 3. Direct exponent recovery, including X=5 and X=7

Put `M=6a+8`. The sequence `H_j=chi_A(j)-a*psi_A(j)` has initial
values1,3 and the recurrence with characteristic polynomial
`z^2-2Az+1`. Since its value at3 is `9-6A+1=-M`, induction gives

    H_j=3^j mod M.

The source exponent equation thus gives `X=3^J mod M`. We have X<a<M.
For X>=9, the lower-ratio growth gives

    3^J=3*9^r<X^(r+1)<a<M.

The only smaller X possible for odd q>=5 and positive w are X=q=5
and X=q=7. Their bounds are explicit:

- At q=X=5, r=4 and `Y>=5^4=625`, so
  `M=6Y(X+1)+8>=22508>19683=3^9`.
- At q=X=7, r=6. The first two integer terms of xi give
  `xi>7^6+12*7^5=319333`. Since xi<Y+1, integrality gives Y>=319333.
  Hence `a=8Y>=2554664>1594323=3^13`.

In every case both positive representatives are below M. Therefore
`X=3^(2r+1)`. Since q divides X, q is a power of three. Combined with
the small parameter cases above, this proves soundness for every q.

For q>=5, the standard rounding conclusion follows too. Once the
exponent is known, (2) is below1/2. The fractional binomial tail is
positive and less than `4^r/(2X)<1/4`; the positive unit ratio interval
forces

    Y=floor(xi)=binom(2r,r)+sum_(j=1)^r binom(2r,r+j)X^j.

The theorem does not need or assert this classification for every
arbitrary q=3 witness.

## 4. Strictly positive converse for every power of three

Given q=3^t,t>=1, put `r=q-1`, `J=2r+1`, `X=3^J`,
`Y=floor((X+1)^(2r)/X^r)`. Doubling r in base3 makes exactly t carries,
since r has t digits all equal to2. Thus `v3 binom(2r,r)=t`. Also q
divides X, so the displayed integer-part expansion makes q divide Y.
Set `w=X/q,s=Y/q`, both positive integers.

Now r>=2 and X>=243. For the canonical choice Y, we have `Y>=X^r`.
The lower and upper ratio estimates above are consequently valid, and
`24r/(X+1)<1/2`. Together with the fractional tail below1/4, they give
both strict inequalities `Y<c/k<Y+1` at the canonical Pell indices.
Define

    a=Y(X+1), A=a+3, Delta=A^2-1, P=2XY^2+1,
    c=psi_A(J), d=chi_A(J), k=psi_P(r+1),
    eta=c-Yk, zeta=k-eta,
    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/(XY), ga=(d-X-ac)/(6a+8).                 (3)

P is odd, making tau integral. The first-index Pell congruence makes h
integral, and the exponent recurrence makes ga integral. Growth makes
all three positive; for the last, `d-ac=3c-psi_A(J-1)>2c>X`.
The strict ratio interval makes eta,zeta positive.

The smallest case q=3 gives

    X=243, Y=60027, a=14646588,
    c=736319326244035353714587840005,
    k=12266455442576373130188099,
    eta=805392503403828786821332,
    zeta=11461062939172544343366767.

Thus the endpoint is nonempty and its interval is strictly positive.
The [receipt](pell_kernel_power_three43.json) records all its materialized
main coordinates and checks the corresponding eight source equations.

For every q, the remaining five coordinates use the retained positive
auxiliary map:

    m=2cJ, f=chi_A(m), i=Delta*psi_A(m)/c^2,
    R=ic^2, y_aux=psi_R(J), u=chi_R(J)/R,
    o=(u-c)/f, j=(u-J)/c.                              (4)

The multiple-index identity proves `c^2 | psi_A(2cJ)`: write
`psi_A(Jn)=c*psi_d(n)`, use `d^2=1 mod c` to obtain
`psi_d(n)=n*d^(n-1) mod c`, and take n=2c. Hence i is integral and
positive. Since J is odd, u is integral. Here r is even and `J=1 mod4`.
The normalized odd-index polynomial identities therefore give
`u=c mod f` and `u=J mod c`, so o,j are integers. Furthermore R>=c^2>A
and J>=5 imply

    u>(2R-1)^(J-1)>(2A)^(J-1)>c>J.

Thus o,j are strictly positive. The Pell identities give the relaxed
and auxiliary norms; the definitions give both positive congruences.
This supplies every coordinate of(1). The auxiliary index is enormous
even at q=3, so this part is a parametric proof, not a materialized tuple.

## 5. Evidence and scope

The checker audits all eleven independent polynomial residuals with
the exact auxiliary norm correction and the complete43-operation DAG.
It checks744 preliminary and exponent-representative cases, canonical
main/first Pell coordinates at q=3,9,27, and the normalized odd-index
polynomial identities through J=13. These tests supplement the proofs
for all parameters and every positive auxiliary coordinate.

Default execution compares the adjacent receipt. Independent full proof,
source, and default-replay review passed. No stream typing, universal controller, Lean formalization or
complete universal bound below76 is claimed.
