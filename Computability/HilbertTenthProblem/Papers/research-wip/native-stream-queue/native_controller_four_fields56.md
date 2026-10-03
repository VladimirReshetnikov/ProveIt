# Four independent native fields with paid bounds and parity

This component costs **56=31M+25A**, with 16 equations and 22 positive
auxiliaries beyond five positive parameters. It types four independently
chosen native ternary fields, subject to one explicit global parity
condition and a fixed units digit. A **58=31M+27A** variant supplies the
positive repunit H as an arithmetic coordinate. These are complete typing
relations; no universal computation, ordinary-input bridge or accepting
controller is included. The established complete universal bound is76.

This source is distinct from the
[paired-complement56 module](native_controller_boolean_pairs56.md). Here
all four bit planes are free apart from parity and the initial bit; they
are not constrained into complementary pairs. The shared numerical count
does not make their interfaces identical.

## 1. Exact semantics and source

Take positive parameters q,F0,F1,F2,F3. The56 relation has positive
witnesses exactly when, for some t>=1,

    q=3^t,
    each Fi has t ternary digits in{1,2},
    the units digit of F0 is2,
    F0+F1+F2+F3 is even.                                 (1)

With the mathematical repunit H=(q-1)/2, the four decoded words Ti=Fi-H
are therefore Boolean. They can be chosen independently subject to the
units digit of T0 being1 and the total number of their one digits being
even. No coefficientwise relation among the four words is imposed.

Supply the seventeen retained positive Pell coordinates and five further
positive witnesses alpha0,...,alpha3,nu. Set

    P=F0+qF1+q^2F2+q^3F3,       D0=q^4,

and impose

    Fi+alpha_i=q   for i=0,1,2,3,
    r=P,           r=2nu.                               (2)

Attach the ten unchanged ternary Pell equations at X=wD0,Y=sD0,
explicitly displayed in Section2 of the paired-complement56 proof.
The executable source independently builds their polynomials at q^4.

The even-index condition is paid in(2). The proof here can therefore use
the even-index converse directly. A subsequent
[55-operation refinement](native_controller_four_fields55.md) checks the
generic signed-parity theorem and proves that this comparison is redundant.
The present source and receipt are preserved as the explicit-parity
reference.

## 2. Bounds before power recovery

The positive slack equations give q>=2 and1<=Fi<=q-1. Consequently

    q^3+q^2+q+1<=P<=q^4-1.

Thus all preliminary inequalities are available even at the non-power
endpoint q=2:

    D0=q^4>=16, r>=15, r<D0, D0<r^2,
    X,Y>=D0, XY>=D0^2>r+1,
    a>=D0(D0+1)>2r+1,
    6r/a<6/(D0+1)<=6/17<1/2.                            (3)

No inherited D0>=27 or D0>=81 assumption is used. As in the reviewed
kernel argument, the first Pell index n>=r+1, its base exceeds A=a+3,
and c>Yk>k. The main index therefore satisfies p>=r+2>=17. This is
enough for c>A^6>AD^2, c>2r+1 and0<2p<=c, which are the retained
auxiliary-rank and half-parameter hypotheses. They give p=2r+1, and
the same positive base comparison gives n=r+1.

The retained ratio estimates then yield

    Y>=X^r, a>X^(r+1),
    0<c/k-(X+1)^(2r)/X^r<24r/(X+1).

The direct exponent recurrence gives X=3^(2r+1) modulo6a+8. Both
representatives lie between0 and6a+8, because X<a and

    3^(2r+1)=3*9^r<X^(r+1)<a

for X>=16. Hence X=3^(2r+1). Since q^4 divides X, q=3^t for
some t>=1. The now exponentially small ratio error and retained
binomial-tail estimate give

    Y=floor((X+1)^(2r)/X^r),    q^4 divides binom(2r,r).   (4)

The detailed ratio, rank and congruence arguments are exactly those
audited in the retained43 kernel; (3) checks their actual thresholds
for this changed outer source.

## 3. Native typing and both directions

Because every supplied field was bounded belowq before invoking the
kernel, P is already the four-field base-q expansion and P<q^4.
Let N=4t. Kummer's theorem and(4) require at least N carries in
doubling P, but only N positions can generate carries. Every position
therefore does so. The units digit is2, and every higher digit is1
or2. The q=3^t field boundaries align with the native ternary blocks,
proving the digit assertions in(1). Finally r=2nu and q odd imply

    F0+F1+F2+F3=P=0 modulo2.

This proves soundness, with no inferred digit extraction or unpaid field
bound.

Conversely, given(1), set r=P, nu=P/2 and alpha_i=q-Fi. Every one of
these coordinates is positive. The packing has all N native positive
trits with units digit2, so its central binomial coefficient has exactly
N ternary carries. The scale divisibility in(4) follows. The inequalities
in(3) hold for these data, and the explicitly paid parity gives
J=2r+1=1 modulo4. Therefore the full positive witness map in Section5
of the paired-complement56 proof applies at this D0,r. Its power and
binomial divisibilities give positive integral w,s; the ratio interval,
Pell congruences and growth estimates supply the other fifteen positive
coordinates. Every retained equation is satisfied. This proves the exact
positive existential projection(1).

The58 variant supplies one more positive coordinate H and imposes
q=2H+1 using two additions. Once q=3^t, this coordinate is the true
repunit. Its converse chooses H=(q-1)/2. The condition(1) is unchanged.

## 4. Complete ledger

The13 outer instructions are

    bound0=F0+alpha0; bound1=F1+alpha1;
    bound2=F2+alpha2; bound3=F3+alpha3;
    p0=q*F3; p1=F2+p0; p2=q*p1;
    p3=F1+p2; p4=q*p3; P=F0+p4;
    q2=q*q; D0=q2*q2; even_r=2*nu.

They cost6M+7A; the kernel costs25M+18A. Compare the first four
registers with q, r with P, and r with even_r, then impose the ten
kernel comparisons. The complete count is56=31M+25A,16 equations,
22 positive auxiliaries. In particular multiplying nu by2 is counted.

For58 append

    twice_H=H+H; q_calc=twice_H+1

and compare q=q_calc. It has31M+27A,17 equations and23 positive
auxiliaries. It exposes H and2H for subsequent projections. Recovering
either from the56 interface has not been treated as free.

## 5. Evidence and scope

The [checker](native_controller_four_fields56.py) independently expands
all16 or17 source comparisons, retaining the inherited auxiliary-norm
residual correction, and audits both exact schedules and every supplied
coordinate. Its pre-power enumeration includes q=2 and both parities
before the parity comparison. Exhaustive field scans through t=3 check
the equivalence of the valuation mask and native typing, and separately
check the explicit parity restriction. Canonical four-plane inputs through
t=4 include identically zero decoded Boolean words while every supplied
field and slack remains positive.

The exact main/first Pell and ratio test uses r=44, an admitted q=3
tuple with fields(2,2,1,1). The general proof supplies the unmaterialized
auxiliary extension. Default execution compares the
[saved receipt](native_controller_four_fields56.json). No prior source
or receipt is edited. Independent mathematical/source review and fresh
default-receipt replay passed, including the q=2 bootstrap and the full
positive converse.

This interface gives four typed Boolean planes when H is exposed. It
does not itself compute joint bit selectors, bitwise products, arbitrary
four-state transition maps, shifted incidences or acceptance conditions.
Those are additional compiler obligations, and their operation counts
are not part of56 or58.
