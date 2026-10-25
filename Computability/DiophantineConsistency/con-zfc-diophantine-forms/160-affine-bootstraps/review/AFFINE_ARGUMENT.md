# Affine beta multipliers and an affine signed radix

Research proof note for ProveIt, 25 October 2026, prepared with AI assistance.

## Statement and exact changes

In the incoming factorial-free binomial CRT construction, make the following
three replacements, leaving all eighteen power requests and all fourteen
paired signed-Pell orientation tests present:

    R = F^2       becomes  R = F,
    y = F(2v+1)^2 becomes  y = F(2v+1),
    q = (2z+1)^2  becomes  q = 4z+1.

There are two proved horizon choices:

(A) t=16+h^2, d=2(t+1), F=d^t (the existing square-horizon proof);
(B) t=16h,   d=t+2,    F=d^t (the lower-dimension affine horizon).

All h,v,z are unrestricted integers. Every displayed power is the semantic
meaning of an unchanged ordinary polynomial power certificate. The final
polynomial itself contains only integer coefficients, addition, subtraction,
and multiplication. These are changes of certificate architecture, not
claims of a polynomial bijection between old and new semantic witnesses.
Subsequent integral substitutions and row operations are genuine zero-set
bijections and have explicit finite certificates.

For either horizon, the new source has an integer zero iff a finite C222
refutation exists. Composition with the retained C222/ZF/ZFC calibration
therefore proves in ZFC that its integer unsolvability is equivalent to
Con(ZFC). The proof below establishes the new arithmetic steps. The exact
Pell/CRT/proof-calculus dependencies are inherited, not newly formalized.

## 1. The signed power interface

The retained frame bounds every actual base, exponent, and output atom in
absolute value by W and makes |A|>W^W and |A-1|>4W^3. Once its full signed
orientation pool has been recovered, a request with |n|>=2 forces its index
k>=0 and its output m=n^k. This applies to negative bases. Unit bases have
their exact signed unit outputs but do not force k nonnegative. No zero-base
request is interpreted in the bootstrap below.

The explicit request inventory contains

    (d,t,F), (B,x,N), (BH,x,q), (q+1,R+t,U), (q,t,Q_t),
    (q,t+1,Q_{t+1}), (q,y+1,Q_{y+1}), (q,x,M),

as well as the nine actual CRT representatives and the derived semantic
label as requested exponents at base q+1. The literal (q,y+1,pow11.output)
request is request11 in the retained interface auditor; it is not inferred
from informal notation.

### Why the affine horizon does not break orientation at t=0

For choice(A), the original t>=16 argument supplies W>=258 directly.
Choice(B) must recover t>=16 only after the signed interface is available.
The following sharper form of the inherited orientation estimate closes
this ordering issue.

The frame includes q and q+1 as distinct base atoms. Since q=4z+1,
q^2+(q+1)^2>=5, hence W>=7 independently of every exponent sign. The
comparison center and dominant ordinate give each classified principal
index j_i<=|h_*|. The actual requested anchor h_* and every requested index
k_i have their squares in the frame, so h_*^2<W and k_i^2<W. Thus

    (sign(j_i)*j_i-k_i)^2 <= 2j_i^2+2k_i^2 < 4W.

Each abscissa error contributes at most4. There are fourteen principal pairs,
so the nonnegative reduced orientation error satisfies

    E < 4*14*(W+1) < 4W^3 < |A-1|,    W>=7.

Divisibility by A-1 forces E=0, orienting every pair. The exceptional
anchor index1 branch has |C|=1; the cap forces requested anchor0 and all
other ordinates0, while its anchor orientation error is positive. The same
small-error bound rules it out. This sharp squared-atom bound replaces the
older, unnecessarily large W>=258 estimate. It does not delete any of the
fourteen tests. The other signed-power size estimates require only W>=2
and therefore apply at W>=7.

## 2. Authenticate a positive horizon

Choice(A) has t>=16 and d>=34 before any semantic recovery, so F=d^t>2^32.

For choice(B), d=16h+2 has absolute value at least2 at every integer h.
The signed power request therefore forces t>=0. If t=0 then F=2^0=1 and
our new beta equation gives y=2v+1, an odd integer. The two retained endpoints
become

    x = 2 + (y+1)u_0,
    x = 1 + (y+1)u_t.

Subtracting gives 1=(y+1)(u_t-u_0), impossible because y+1 is even. This
also excludes y=-1, where the right side is zero. Consequently t>0 and
since t=16h, t>=16. Now d=t+2>=18 and F=d^t>2^32.

For either choice, d is positive and even, F>1, and v_2(F)>=t.
The label-product bound F>(t+1)^t holds in both cases.

## 3. Exclude a degenerate radix before recovering beta signs

The progression q=4z+1 gives |q+1|=|4z+2|>=2. The numerator requests at
base q+1 therefore force every actual representative C,A_1,...,A_8 to be
nonnegative, even if the tentative q is negative. Hence

    H = 2+C+A_1+...+A_8 >= 2.

The raw index row B h_B=C+F+1 excludes B=0. Thus |BH|>=2. The self-radix
power request forces x>=0 and q=(BH)^x.

At this point y=F(2v+1) is nonzero and |y|>=F>1, but its sign has not yet
been established. Nevertheless

    |1+(t+1)y| >= (t+1)F-1 > 1.

The last endpoint x=1+[1+(t+1)y]u_t therefore excludes x=0. Thus x>0,
which makes |q|=|BH|^x>=2. Since the progression q=4z+1 contains no integer
of absolute value2, we actually have |q|>=3. In particular its formerly
possible unit value q=1 has now been excluded by the arithmetic, rather
than by an extra guard.

The retained request at base q with exponent y+1 can now be interpreted:
|q|>=3 implies y+1>=0. Since y=F times an odd nonzero integer and F>1,
a negative multiplier would give y<=-F<-1. Therefore 2v+1>=1 and y>=F.
This is exactly the bound needed from the removed square. The sign is
recovered from an already required exponent, without a new witness.

## 4. Recover the positive binomial digit in a signed radix

The first endpoint x=F+1+(y+1)u_0 and y>=F show u_0>=0: otherwise x<=F-y<=0.
Thus x>=F+1>=3. The last endpoint then has u_t>=1, giving

    x >= 2+(t+1)y >= 2+(t+1)F.

Put Q=|q|. Then Q=|BH|^x>=2^x and |B|<=|BH|<Q/2.
All base-q requests are now genuine, although q may still be negative.

The first exact digit uses n=F+t and coefficients C_j=binom(n,j). For
0<=j<=t, the intentionally loose inherited estimate remains valid:

    C_j <= (F^2+t)^t <= (F^2+F)^t <= 2^(t(F-1)).

Since Q>=2^x and x>=2+(t+1)F,

    C_max/(Q-1) < 2^(-F-t-1) < 1/32,
    C_t < Q/32.

The signed low polynomial r0=sum_{j<t} C_j q^j has |r0|<Q^t/32 and is
congruent to (q+1)^n modulo q^t. The retained common denominator equations
and shared norm give an integer remainder r in that congruence class with
|r|<Q^t/2. Their difference is a multiple of q^t with absolute value less
than Q^t, so r=r0. This does not assume either q or r positive.

The exact digit equation now gives B congruent to C_t modulo q, and

    |B-C_t| <= |B|+C_t < Q/2+Q/32 < Q.

Thus B=binom(F+t,t)>0. Finally q=(BH)^x with B>0,H>=2,x>0 gives q>0.
Only after this point are ordinary positive-radix interpretations used.

## 5. Why the linear selector radius is sufficient

The inherited binomial CRT theorem requires R>=L_t^2, where
L_t=lcm(1,...,t). A separate supplied proof establishes the elementary
bound L_t<=4^(t-1). For either horizon choice, t>=16 and

    F >= (t+2)^t >= 18^t > 16^(t-1) >= L_t^2.

Thus R=F satisfies precisely the same CRT premise as the old F^2, so the
large-selector and compatible-prime-power lemmas apply unchanged.
This is the separate linear-selector contribution, composed explicitly.

All remaining coefficient and local-evaluation bounds of the factorial-free
source persist. They use y>=F, x>=2+(t+1)y, F>2^32, and F>(t+1)^t, all
already recovered. The derived-label bound by a fixed power of H persists
because H is still2 plus the sum of the actual nonnegative representatives.

The algebraic boundary y=F is still ruled out by the original argument:
the initial accumulator is0 modulo y+1, the local updates propagate0 because
all label weights are positive, and the final accumulator must be1. Thus
every genuine solution has y>F and the intended positive initial accumulator.
Bounded-row CRT recovery, label multiplicity recovery, and the
single-conclusion flow theorem yield a finite C222 refutation. The retained
named calibration yields a finite ZFC refutation.

## 6. Constructive completeness

Start from a finite C222 refutation and choose a sufficiently large horizon
in the cofinal set required by(A) or(B), padding with truth rows as before.
Set d,F and R=F. Let O be the odd part of t!. Choose an arbitrarily large
positive odd multiple w of O and put

    y = Fw,     v=(w-1)/2.

Because v_2(F)>=t>v_2(t!), y is an even multiple of t!. Choose w large
enough that y>F and that every pending-multiset accumulator is at most y.
This is the only role for which the old construction used an odd square;
an unrestricted positive odd multiple suffices. The beta moduli
1+(i+1)y are odd and pairwise coprime. CRT gives a beta code x, and its
odd period allows x to be chosen even and arbitrarily large.

Set B=binom(F+t,t) and N=B^x. Since v_2(F)>=t>floor(log_2 t), for
1<=i<=t one has v_2(F+i)=v_2(i). Thus B and N are odd. The binomial CRT
compiler supplies its nine representative classes modulo N^2. Choose the
distinguished a odd and the other eight representatives even, preserving
all congruences by lifts of the odd modulus. As in the source, take a in
[2N^2,4N^2) and the others in(0,2N^2]. The constructor identities make the
semantic anchor even and dominating, while H=2+sum of the representatives
is odd.

Now B,H are positive odd integers and x is positive even. Thus
q=(BH)^x is an odd square and in particular q congruent1 modulo4. Set
z=(q-1)/4. This satisfies the new affine radix row without any new modular
condition or enlarged representative bound. All remaining power, Pell,
CRT, range, remainder-budget, and local-rule witnesses follow from the
unchanged constructive completeness proof.

This yields a zero of the new source for every finite C222 refutation.
Both directions are ordinary arithmetic arguments formalizable in ZFC.

## 7. Verification boundary

The source changes replace selected quadratic relations by affine relations
and remove a dispensable selector square. Each resulting raw source remains
an explicit finite list of quadratic or affine integer residuals. Its single
ordinary polynomial is their sum of squares. Horn factoring, monic
substitution, coordinate translation and invertible integer row changes
supply exact finite maps to the final released quartics.

Finite checkers certify these literal identities and every coefficient; they
do not prove the unbounded signed-Pell, CRT, or logical calibration arguments.
No claim of a global simplicity optimum or new end-to-end Lean/Rocq proof
is made. The discarded q=6z+3 experiment is a valid earlier variant but is
not needed by the final construction or its completeness proof.
