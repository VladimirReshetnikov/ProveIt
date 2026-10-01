# A population excess obstructs the naive geometry/AND fusion

The geometry and joint-AND cores of the
[303-operation compiler](neary_woods_universal_joint_and_units.md)
cannot be combined merely by concatenating the population index with
the four truth fields and multiplying their scales. For **every fixed
width D>=3 and every dyadic duration n>=2**, the proposed single
population relation has a complete positive native extension on a
recoder tuple with

    x=1, z=2, Q=2^(D(n+1)),

although the intended relations require z=spread_D(1)=1 and Q=2^(Dn).
The duration can be arbitrarily large. Any correct independent high
AND can be appended without removing the defect.

The [checker](native_population_and_fusion_obstruction.py) and
[receipt](native_population_and_fusion_obstruction.json) record exact
integer scalar and population computations. The complete native
extension follows from the existing raw geometry theorem, rather than
from an approximate Pell calculation. This is an obstruction to the
specific relation below. It is **not** a false zero of the complete fixed
universal tag polynomial: no accepting chronological tag history at the
altered loader output is supplied. No arithmetic saving, lower bound,
or impossibility of other geometry fusions is claimed.

## 1. The candidate population relation

Use the notation of the
[raw joint-AND certificate](neary_woods_universal_joint_and.md).
The population geometry has index R=(2^D-1)J and desired scale Q.
The AND has dyadic scale T, native scale t=16T, and positive fields

    F0=16(T-H-M+Z)-15,
    F1=16(H-Z)+4,
    F2=16(M-Z)+2,
    F3=16Z+8.                                         (1)

Thus sum Fi=t-1 and both input ports retain their exact four-bit
padding. Put

    rF=F0+t*F1+t^2*F2+t^3*F3.

The naive fusion retains those fields and scalar equations, replaces
the two native population conclusions by one, and feeds a single raw
population kernel the index and scale

    rstar=R+t*rF,       qstar=Q*t,
    qstar=2^popcount(rstar).                          (2)

Here R<t and all Fi<t, so if t is dyadic the populations add without
lane overlap. For a genuine AND, popcount(rF)=log2(t), and(2) would
indeed recover the desired population of R. But the checksum only
implies

    sum popcount(Fi)>=popcount(sum Fi)=log2(t).         (3)

False truth fields can have a strict excess in(3). The following
family makes that excess exactly cancel a wrong geometry width.

## 2. All retained recoder scalar constraints

Fix D>=3 and a power of two n>=2. Define

    q=2^n, Q=2^(D(n+1)), B=2^(D-1)*Q,
    b=log2(B)=D(n+2)-1,
    P=B^n, J=(P-1)/(B-1), S=qP=(2B)^n,
    K=(S-1)/(2B-1), R=(2^D-1)J.                     (4)

In particular b>n, B>2n, and B>2^D. Set

    x=1, z=2, A=Q+1, Ahat=Q+2,
    input_slack=q-1, power_gap=Q-q-2,
    quotient_hat=2, ell=n,
    duration_quotient=(J-n)/(B-1),
    duration_slack=B-1-n,
    fusion_output_slack=S-Ahat.                       (5)

Every supplied coordinate in(5) is a positive integer. The duration
quotient is positive because J-n is divisible by B-1 and contains
at least the positive term B-1. The new output slack is positive
because S=qB^n>Q+2. These definitions satisfy exactly

    x+input_slack=q, Q=q+z+power_gap,
    (B-1)J+1=P, (2B-1)K+1=S,
    (B-1)*duration_quotient+ell=J,
    ell+duration_slack=B-1,
    Ahat=(Q-1)*(quotient_hat-1)+z+1,
    Ahat+fusion_output_slack=S.                        (6)

The loader's additional repunit also has a positive value:

    load_r=(Q-1)/(2^D-1)=sum_(j=0)^n 2^(Dj).           (7)

For any fixed positive program duration bound E<n, ell=E+(n-E)
uses a positive gap. Thus this defect is not confined to small
unusable durations. The other positive program coefficients produce
a positive loader value as usual; no accepting history for that
value is asserted here.

The population index is odd, R>B>Q, and R<P. Its n disjoint
b-bit cells each contain D ones, so

    popcount(R)=Dn.                                   (8)

In contrast log2(Q)=D(n+1). The geometry has a deficit of D bits.
All equations in(6)--(7) are retained scalar equations; the deleted
geometry/AND conclusions are precisely the conclusions under test.

## 3. Four fields with exactly D excess bits

Initially take only the low recoder words, at scale L=BS:

    Hr=BJ+n, Mr=BK+n-1, Zr=B*(Q+1).                   (9)

All three lie in [0,L). The true AND output is B. Indeed J and K
have one bits at positions bi and(b+1)j, respectively. Since b>n,
those positions intersect only at i=j=0. Also n AND(n-1)=0. Therefore

    Hr AND Mr=B,                                     (10)

whereas Zr in(9) is different.

Let Ftrue be(1) at scale L, inputs Hr,Mr and output B, and Fbad be
the same formula with output Zr. Both four-tuples are strictly positive
and sum to16L-1. In particular J-(Q+1)>0 and K-(Q+1)>0, since
J>=B+1 and K>=2B+1. The false F0 increases from an already positive
true value. Each field is consequently below16L.

Write C=S-J-K. Separating each field at the dyadic place16B gives

    Ftrue0=16B*C+16(B-2n)+1,
    Ftrue1=16B*(J-1)+16n+4,
    Ftrue2=16B*(K-1)+16(n-1)+2,
    Ftrue3=16B+8.                                     (11)

Every displayed remainder lies in [0,16B). Replacing the output B by
B(Q+1) changes the four high coefficients to

    C+Q, J-1-Q, K-1-Q, Q+1.                           (12)

The population changes in order are

    (2-D, D-2, D-1, 1).                               (13)

Here is the exact carry argument. Put v=log2(Q), so b-v=D-1.
The least one bit of J-1 is at b; subtracting2^v replaces that one
by b-v ones, changing the population by D-2. The least one bit of
K-1 is at b+1, giving D-1. Adding2^v to the coefficient1 gains
one bit. Finally

    C mod B=B-2,       floor(C/B) mod B=B-4.

These identities follow from J+K=2+3B modulo B^2 and S=0 modulo
B^2. Thus the bits of C from v through b-1 are all one, while its
bit at b is zero. Adding Q replaces those b-v ones by one, giving
2-D. This proves(13) for every D,n in the stated family, not merely
for the finite checker samples.

The true fields partition all bits below16L, so their total population
is log2(16L). Summing(13) gives D. Hence

    sum popcount(Fbad_i)=log2(16L)+D.                  (14)

## 4. Any correct high AND and a full native extension

Take an arbitrary dyadic Th>=1 and nonnegative Hh,Mh<Th. Put
Zh=Hh AND Mh, and concatenate exactly as in the complete raw fuser:

    T=L*Th, H=Hr+L*Hh, M=Mr+L*Mh, Z=Zr+L*Zh.          (15)

The four high truth-class values are

    C0=Th-Hh-Mh+Zh-1, C1=Hh-Zh,
    C2=Mh-Zh, C3=Zh.

They are nonnegative, partition the bits below Th, and have total
population log2(Th). The padded fields(1) for(15) are exactly

    Fi=Fbad_i+16L*Ci.

Since Fbad_i<16L, this is disjoint binary concatenation. Therefore
all fields are positive, below t=16T, sum to t-1, and satisfy both
padded input ports, but

    popcount(rF)=log2(t)+D.                           (16)

The output in(15) is still false in its low block. Since R<P<t,
its lane in rstar=R+t*rF is disjoint from the four field lanes.
Combining(8) and(16) proves exactly

    popcount(rstar)=Dn+log2(t)+D=log2(Q*t).            (17)

Moreover rstar is odd, at least9, and exceeds qstar=Qt. For example
F3>=8 implies rF>=8t^3 and rstar>=8t^4, while t>Q. Thus every
hypothesis of the
[complete raw population theorem](native_binary_input_dilation129.md#2-the-raw-geometry-theorem-at-j9-and-jq)
holds at this new index rstar and scale qstar.

Its constructive converse supplies all positive Pell, ratio, index,
exponent, odd-multiplier and strong-auxiliary coordinates. In
particular it takes X=2^(2rstar+1), the prescribed central-binomial
upper tail for Y, and the canonical positive remaining coordinates.
Both ratio slacks and the full strong auxiliary norm are preserved.
If an explicit index-bound comparison is wanted, the bound qstar
and positive difference rstar-qstar suffice. This is therefore a full
native-extension counterexample to the proposed combined relation,
not just a tuple satisfying selected outer equations while the
remaining native norms are unknown.

The failed consequences are both explicit: z=2 is not spread_D(1),
and Q is not q^D. The high AND is correct but arbitrary. It need
not encode a chronological history with the actual loader and terminal
conditions, so(17) does not establish a false zero of the complete
universal polynomial. A future sound fusion would need an additional
condition preventing this exact population compensation.

## 5. Executable scope

The source evaluates768 exact family members: widths3 through18,
durations2,4,8,16,32,64, and eight high-AND choices per pair, including
the zero-width high block. It checks every scalar equality in(6)--(7),
strict positivity, the low range bounds, the four individual changes
(13), the high concatenation, and the exact identity(17). A separate
110-case computation derives the four carry changes directly from
C,J,K,Q, without using the field constructor. The receipt stores three
small representative tuples and a digest of all finite fused indices.

The parametric proof covers the actual fixed universal width D as
well, without expanding2^D or any giant Pell witness. Finite native
witnesses are not claimed to have been materialized. The source is an
obstruction checker, not a new counted straight-line certificate; no
operation or degree bound is assigned to a rejected candidate.

```sh
python3 native_population_and_fusion_obstruction.py
```

Author writer and fresh default pass. An independent reviewer passed the
full proof/source/fresh replay with no findings, separately re-derived
all four carry changes, checked every retained scalar equation and the
arbitrary high-AND extension, and verified the actual positive raw-native
converse hypotheses. All five local links resolve. No full fixed-tag
acceptance or complete universal-polynomial counterexample was inferred.

Root also independently passed the complete proof/source/fresh-default
review, including the parametric carry argument and the precise native
versus full fixed-tag scope. No findings remained.
