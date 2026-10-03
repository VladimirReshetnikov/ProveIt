# A joint-bounded ordinary-input FIFO in 63 operations

The [65-operation FIFO](native_dualrail_fifo67.md) can replace its four
individual field bounds by one joint stream bound, provided its initial
queue is the ordinary integer **6x**. The result is an exact component in
**63=33M+30A**, with 15 equations and 26 positive existential coordinates
apart from x. A general affine carry controller fits in **72=38M+34A**;
equal initial and terminal carries reduce that to **71=38M+33A**.

These are component and architecture counts. A universal compiler,
ordinary-input normalization by that compiler, and sound acceptance have
not been constructed. The complete universal bound remains76. Unlike the
[64-operation source](native_dualrail_fifo64.md), this source explicitly
requires the joint inequality A+D<q. Padding a controller path to obtain
that inequality needs its own justification.

## 1. Source and exact projection

Take positive parameters x,W,q,F0,F1,F2,F3 and the seventeen positive
coordinates of the retained ternary kernel. Supply positive alpha,beta,L.
Compute

    Q=q-1, A=F0+F1-Q, D=F2+F3-Q, I=6x,
    r=F0+qF1+q^2F2+q^3F3, scale=q^4.

Here r is a supplied coordinate compared with its computed packing.
Keep all ten kernel equations from the
[three-selector source](native_controller_three_selector_53.md), with
X=w*scale and Y=s*scale. Replace the four field slack equations by

    D=I+WA, I+beta=W, q=WL, A+D+alpha=q.                  (1)

No field bound or packed-index bound is assumed in the source. Computed
registers A,D may initially have either sign; supplied coordinates are
strictly positive. The proof must recover their intended signs and digits.

The exact projection of this source consists of the following data:

- q=3^t and W=3^m, with t>=m>=2 and 6x<W;
- Fi=H+Ti, H=(q-1)/2, where each Ti is a length-t Boolean ternary word;
- the first bit of T0 is1;
- the scalar read digits of T2+T3 and append digits of T0+T1 give a
  t-step FIFO run from the ordinary integer6x to zero;
- the scalar stream values obey A+D<q.

The Boolean split of a scalar trit1 can be either10 or01, except that
the first append must have its first rail bit1. No extra regular-code
filter, finite controller, or bit conversion is implicit here.

## 2. Kernel recovery without individual bounds

The joint equality in(1) gives

    sum_i Fi + alpha = 3q-2,
    sum_i Fi <= 3q-3.

Since all Fi and alpha are positive, q>=3. Positive beta,L also give
q>=W>I=6x>=6. Put S=q^4. Positivity and the sum bound imply

    q^3+q^2+q+1 <= r < 3S,
    S<r^2, X,Y>=S, XY>=S^2>r+1,
    a>=S(S+1)>12r, 6r/a<18/(S+1)<=18/82<1/2.             (2)

Thus the enlarged-range ternary kernel argument applies before assuming
any power, parity, or digit typing. Its first Pell index n>=r+1, the main
index p>=r+2>=42, and c>A_pell^6>A_pell*Delta^2, where
A_pell=a+3 and Delta=A_pell^2-1. The auxiliary rank and half-parameter
arguments give p=2r+1 and c=psi_A_pell(p). The positive base comparison
then gives n=r+1. The ratio estimates yield

    Y>=X^r, a>X^(r+1),
    0<c/k-(X+1)^(2r)/X^r<24r/(X+1).

The direct exponent congruence is X=3^(2r+1) modulo6a+8. Both
representatives lie between0 and6a+8 because X<a and
3*9^r<X^(r+1)<a. Hence X=3^(2r+1). Since q^4 divides X,
q=3^t for t>=1. The same rounding and binomial-tail argument now gives

    Y=floor((X+1)^(2r)/X^r), q^4 divides binom(2r,r).      (3)

All numerical thresholds are stronger than those used in the reviewed
[four-field proof](native_controller_four_fields56.md); the changed
upper bound r<3S is explicitly covered by(2). The generic plus-sign
parity theorem, with the hypothesis audit in the
[55-operation proof](native_controller_four_fields55.md), also gives r
even. In particular the source has not replaced the signed auxiliary
argument by a check of canonical witnesses.

From q=WL and W>I>=6, W=3^m for m>=2, t>=m, and therefore t>=2.
These conclusions are available before the digit argument below.

## 3. The joint bound rejects every packed or field overflow

Write H=(q-1)/2 and N=4t. Normalize the first three base-q positions:

    F0=U0+q c0,
    F1=U1-c0+q c1,
    F2=U2-c1+q c2,
    F3=U3-c2,

where 0<=Ui<q for i<3, U3=floor(r/q^3), and c0,c1,c2>=0.
The nonnegative carries follow successively from the positive Fi.
Let sigma=U0+U1+U2+U3. Then

    sum_i Fi = sigma+(q-1)(c0+c1+c2).                    (4)

First suppose r<q^4. Kummer's theorem and(3) require N carries in at
most N ternary positions. Every position carries: the units digit is2,
and every subsequent digit is1 or2. Each Ui is therefore at least H,
and U0>=H+1. Thus sigma>=4H+1. A positive internal carry in(4) would
give sum Fi>=6H+1, contrary to sum Fi<=6H. All ci vanish, so every
supplied Fi is its true native q-block.

It remains to rule out q^4<=r<3q^4. There are N+1 ternary digits and
at least N carries. The all-carry case has minimal digits2,1,...,1,
whose normalized block sum is

    sigma_min=4H+q+1=3q-1>3q-3.

Increasing digits only increases this sum. Consequently precisely one
digit position must fail to carry. Its position j is below N: a positive
top digit with an incoming carry necessarily carries, and a missing top
carry without an incoming one would require two missing carries.

For j>0, the missed-carry digit is0 and its successor is2. Relative to
the all-carry minimum, this subtracts the positional weight at j and
adds the weight at j+1. For j=0, the minimal change is digits(2,1) to
(0,2), increasing the block sum by1. Within a q-block, the successor
weight is three times the preceding weight, so the change is positive.
At j=N-1 it is also positive, since the top weight in U3 is q. Only

    j=t-1, 2t-1, or 3t-1                                (5)

can decrease sigma: a weight q/3 is replaced by1 across a block boundary.
Even in those cases

    sigma>=3q-q/3,
    sigma+(q-1)>3q-3.

Equation(4) therefore forces c0=c1=c2=0. Every Fi is its normalized
block, including the extra top digit in F3.

If the missed carry is at either of the first two boundaries in(5),
the read blocks have no zero digit. Hence F2>=H and F3>=q+H, giving
D=F2+F3-(q-1)>=q. The joint bound forces A<0, and since A is an
integer, transport and I<W imply D=I+WA<=I-W<0. This is impossible.

For the remaining boundary j=3t-1, F3 has units digit2. The units
digit of F2 is1 or2: its sole zero is at its last position, and t>=2.
Thus

    D=F2+F3-(q-1) = 1 or2 modulo3.

But transport gives D=I modulo3, while I=6x and W is divisible by3.
This final contradiction excludes the extra top digit. The earlier
r<q^4 argument now proves all four individual field bounds and native
digit assertions. In particular A>=1, D>=0, and both are below q.

The factor3 in the initial queue is substantive. With I=2x instead,
q=27, W=9 and fields(14,14,5,41) give r=811040, even, with exactly12
ternary carries. They have A=2,D=20,I=2 and A+D<q, but F3>=q.
The generic positive kernel map applies, so this is a full counterexample
to that particular change of input factor, not merely a failed field
inequality.

## 4. FIFO soundness and every positive witness

Typed scalar streams have trits0,1,2. The exact transport lemma applied
to D=I+WA, q=3^t and W=3^m therefore gives the stated FIFO run with
terminal queue zero. This proves the forward projection, including its
joint inequality and first append condition.

Conversely, take any run and rail split satisfying the exact projection.
Set Fi=H+Ti, alpha=q-A-D, beta=W-6x and L=q/W. These coordinates
are positive. Telescoping gives transport, and

    sum Fi=D+A+4H=6x+(W+1)A+4H

is even. The packed word has all N native digits and units digit2, so
r is even and v3 binom(2r,r)=N. The full positive Pell map in Section5
of the [selector proof](native_controller_three_selector_53.md) applies
at scale q^4 and this r. Its seventeen coordinates are integral and
strictly positive; no astronomical auxiliary values are materialized by
the finite checker. This supplies all equations and proves the converse.

Every positive ordinary input has a bare-component witness. Choose the
least W=3^m>6x, append1 at the first step, and append0 subsequently.
After reading the initial m trits the queue is1. Read it and append0.
For this run t=m+1, q=3W, A=1 and D=6x+W, so
A+D=6x+W+1<3W=q. Split the first append as10 and choose either
allowed split of each read trit1.

For a different accepting run, one additional zero-read/zero-append step
increases q by3 and leaves A,D unchanged, so it establishes the joint
bound. A proposed controller may use this padding only when that step
is allowed at its endpoint. An affine carry endpoint cf has this loop
exactly when h=2cf. No padding claim is made for arbitrary endpoints.

## 5. Literal schedules and evidence

Delete the four bound additions and their slack coordinates from65,
replace its fixed input multiplier2 by6, and add

    joint_sum=A+D; joint_bound=joint_sum+alpha,
    compare joint_bound=q.

The resulting source has33 multiplications,30 additions/subtractions,
15 equations, seven positive parameters including x, and20 positive
auxiliaries. Every supplied coordinate appears in the source. The
[checker](native_dualrail_fifo63.py) independently expands all residuals,
including the inherited auxiliary norm correction, and audits the full
acyclic source.

The general controller from65 can use a free comparison with the fixed
constant cf-cs, removing its final constant addition. It adds5M+4A and
one equation, giving72.
With fixed K=sum ci, its paid constraint is

    sum ci*Fi + lambda*(q-1) = cf-cs,
    lambda=(h-K-2cf)/2.

The usual doubling of fixed carry data makes lambda integral without
changing the labelled language. If cs=cf, compare sum ci*Fi with
(-lambda)*(q-1): the four-term sum costs three additions, and the
comparison is free. This adds5M+3A, giving71. These source counts include the joint bound and
ordinary input. They characterize the entire Boolean-labelled affine
carry graph coupled to the FIFO; no universal simulation follows from
the ledger.

Focused checks cover pre-power positive fields, every joint-bounded
positive field tuple through q=27, the normalized minimum carry patterns,
and400 positive outer maps for the first200 inputs. Default execution
compares the [saved receipt](native_dualrail_fifo63.json). Independent
proof/source/default review passed, including the enlarged kernel range,
all overflow boundary cases, and both literal controller schedules.
No Lean formalization or improved
complete universal bound is claimed.
