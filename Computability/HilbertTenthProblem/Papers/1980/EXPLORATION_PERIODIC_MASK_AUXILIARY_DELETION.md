# The specialized periodic mask still needs an independent Pell index check

Status: an exact counterexample to the proposed auxiliary-free Boolean
predicate. This is new evidence about the fixed-radix component, not a
counterexample to the published 90-operation universal system. No published
certificate changes. Fixed numerals are free.

The 43-operation retained kernel is recorded in
`EXPLORATION_FIXED_RADIX_PELL_KERNEL.md`. Deleting its relaxed auxiliary norm
and half-parameter index block, and deleting the now-unused computation of
`J=2r+1`, leaves **28 operations: 16 multiplications and 12 additions**.
The special outer construction takes another 11 operations. The resulting
39-operation pair of components does not correctly test Boolean words.

Unlike the earlier rational-root obstruction, the counterexample below
satisfies the *exact specialized packed-r equality*, its strong size bounds,
the common squared scale, and even r. Thus those conditions do not repair
the deleted main-index check.

## 1. Exact special-mask parameters

Choose any positive integer z with z=1 modulo 3, and put

    q=2^z, Q=q^2, L=Q^8, D0=Q^12, N0=Q^6,
    Pcode=8, lambda=(L-1)/3,
    r=(L-Pcode)*(L-1)+2lambda.

All displayed powers in this counterexample describe mathematical witness
values; they are not uncharged certificate instructions. The original five
outer products still construct Q,L,D0, and the original mask geometry and
r products are unchanged.

Since L is a power of four, lambda is a positive integer. We have
0<Pcode<Q^6, N0^2<r<Q^16<N0^3, and r is even. The base-four unit digit of
Pcode is zero, so even its low-digit edge condition is respected, but its
next digit is two. It is not a Boolean base-four word.

The choice z=1 modulo 3 gives L=2^(16z)=7 modulo 9. Therefore
lambda=2 modulo 3 and r=2lambda=1 modulo 3. Define

    h=(r-1)/3, p=6h+1=2r-1, t=3h+2=r+1.

Here h is a positive odd integer and p=J-2, where J=2r+1 is the intended
main Pell index. These h and t are proof parameters, not the supplied
index quotient named h in the retained certificate.

For later scaling, 4h>24z. One elementary bound is r>L^2/2 for L>=65536,
h>L^2/12, and 2^(32z)>72z for z>=1. Hence h>6z.

## 2. Positive witnesses for every retained Pell equation

Set

    U=2^p,
    F=(U+1)^(2h)/(U^h*2^(2h+1)), Y=floor(F),
    a=Y*(U+1), A=a+2, D=A^2-1,
    E=UY, Pfirst=2UY^2+1,
    c=psi_A(p), d=chi_A(p), k=psi_Pfirst(t).

This is the same explicit rational-root family proved in
`EXPLORATION_BASE_TWO_WRONG_INDEX_RATIONAL.md`, sections 1--4. The argument
is recalled to make the new interface clear. Expanding F gives

    Y=sum_(j=h+1)^(2h) binom(2h,j)*U^(j-h)/2^(2h+1),
    F=Y+f, 0<f<1/5, Y>=2^(4h), 2^(4h) divides Y.

The fractional estimate follows from
binom(2h,h)/4^h<=3/8 for h>=2 and the remaining tail <1/(4U).
Each term in the displayed integer sum is divisible by 2^(4h).

The exact principal Pell ratio is

    R0=(2a)^(p-1)/(4UY^2)^(t-1)=F^3/Y^2,
    Y<R0<Y+2/3.

Indeed R0-Y=3f+3f^2/Y+f^3/Y^2<2/3. Elementary Pell growth, with the
positive shift A=a+2, gives

    R0<c/k<R0+48h/(U+1)<Y+1.

The last bound uses U+1>144h. The same ratio proof also gives the strict
lower bound c/k>Y. Thus

    eta=c-Yk, zeta=(Y+1)k-c

are positive integers and satisfy both interval equations.

Let chi_first=chi_Pfirst(t). The positive witnesses

    tau=(chi_first-1)/2,
    h_index=(k-t)/E,
    gamma=(d-U-ac)/(4a+3)

are integral. Odd Pfirst makes chi_first odd. The congruence
psi_Pfirst(t)=t modulo Pfirst-1 gives integrality of h_index, and strict
Pell growth gives its positivity. Finally,

    chi_A(m)-a*psi_A(m)=2^m modulo 4a+3

follows from the recurrence, since its initial values are 1,2 and the
geometric sequence 2^m satisfies that recurrence modulo 4a+3. At m=p
this gives integrality of gamma. Its positivity follows from

    d-ac=2c-psi_A(p-1)>c>U.

The two exact norms are

    tau(tau+1)=(E^2+U)(Yk)^2,
    d^2=1+D*c^2.

Also k=r+1+h_index*E, a=E+Y and d=U+ac+gamma*(4a+3).
These are every non-scaling equation of the 28-operation kernel.

Since p>24z and 4h>24z, both U and Y are positive multiples of
D0=2^(24z). Therefore

    w=U/D0, s=Y/D0

are positive integers, giving both retained scaling equations exactly.
All independent size inequalities also hold: U,Y>=D0, E>=D0^2>r+1,
a>D0^2>J, and p>=r+2. No inadequate large-r approximation or omitted
input-parity hypothesis is needed.

## 3. The intended divisibility actually fails

Write L=4^N with N=8z. The periodic mask is M=2(L-1)/3. Adding Pcode=8
to M produces exactly one binary carry, at the low bit of base-four
position one; its next binary position is zero in M, so propagation stops.
Also Pcode+M<L. The exact identity in
`EXPLORATION_PERIODIC_DIGIT_MASK.md` consequently gives

    popcount(r)=3N-1=24z-1.

Equivalently, by the central-binomial valuation identity,

    v2(binom(2r,r))=24z-1,
    D0=2^(24z) does not divide binom(2r,r).

Thus the auxiliary-free component accepts a non-Boolean word with a
one-bit deficit in the exact divisibility it was supposed to prove.
The error is the main index p=J-2, not a failure of bounds, parity,
power-of-two scaling, or interpretation of the specialized packing.

The complete retained 43-operation kernel rejects this family through
its independent index equations. A particular machine's additional
transition or initial-row equations have not been supplied here; this
is a full counterexample to the proposed *Boolean component*, not a
claim of a false history for every surrounding compiler.

## 4. Exact arithmetic receipt and limits

`../verification/explore_periodic_mask_auxiliary_deletion.py` imports
the actual retained schedule, deletes precisely the 14 auxiliary
instructions and the unused J addition, and checks all seven remaining
source residuals symbolically. It confirms the 28-operation count and
the five-product scale construction. For z=1,4,...,61 it checks the
exact r equation, parity, all outer power bounds, index arithmetic,
valuation deficit, and sufficient exponents for both scale quotients.

The very first outer case already has an intended Pell index above
eight billion. The regression deliberately does not materialize those
Pell coordinates. Their existence, positivity and identities follow
from the preceding general construction, with the previously verified
rational-root proof. The receipt distinguishes exact outer arithmetic
from that mathematical extension.
