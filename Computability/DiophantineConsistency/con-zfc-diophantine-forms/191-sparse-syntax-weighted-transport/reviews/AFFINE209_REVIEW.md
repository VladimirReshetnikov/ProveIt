# Independent mathematical review of the affine209 horizon construction

This review was assigned separately from the construction and does not modify
its code or proof. It checks the new unbounded mathematical argument relative
to the identified inherited Pell, binomial-CRT, local-calculus and logical
calibration lemmas. It is an internal AI-assisted review, not external peer
review, a new formal-kernel certificate, or a fresh verification of every
historical dependency.

## Sources inspected and conclusion

I inspected the complete `direct_work/affine209/PROOF.md` and the incoming
Pell Growth210 packet's `proofs/growth_proof.md` and
`proofs/AFFINE_RADIX_PROOF.md`, in the snapshot rooted at
`d123610bc98fef2006bff1c9466bc3f1221003e7`.

**Conclusion:** no mathematical gap was found in the new initially signed
affine-horizon bootstrap, the reduction of the horizon threshold to 2, or the
generalized cofinal 2-adic completeness construction. The proof correctly
changes the existence construction rather than asserting equality of the
original and modified source zero sets. The passage from the modified source
to the literal coefficient files is an additional finite algebraic obligation;
that producer/certificate replay was not independently reimplemented by this
review.

A useful clarification is to spell out one divisibility in the completeness
paragraph: `t|y0` together with `v2(y0)=19+v2(t)` implies `2^19*t|y0`,
because the odd part of t already divides y0. Thus b0=y0/(dt) is an odd
integer, not merely a rational with odd 2-adic unit part. The stated argument
is correct; this explicit sentence would improve its auditability.

## 1. Signed horizon recovery is noncircular

Let d=2^19 and m in {2,8,16}. With all witnesses initially in Z, the new
row `t=m(2z+1)` implies all of the following without any Pell classification:

* t is even, nonzero, and |t|>=m>=2.
* The retained row `F=d*t*(2u+1)` implies F is even and nonzero.
* The same row gives |F|>=d|t|>=2^20.

In particular the retained F^2 atom supplies the required large positive
square-frame bound before the signs of t and F are known. The incoming
C-anchor proof is explicitly stated for signed frame atoms; its positivity
premise is the frame's magnitude, not a positive interpretation of the
nominal exponent t. The new proof makes no premature use of the standalone
Pell parameter4t+1.

Since C and F are even, C+F+1 is odd and therefore nonzero. Hence the actual
affine base D=2(C+F+1) has |D|>=2. The retained signed exact-power request
q=D^x is consequently applicable and gives x>=0. To exclude x=0, the
terminal beta endpoint uses g=1+(t+1)y and y=F(2v+1). The inequality

    |g| >= |t+1||y|-1 >= |F|-1 > 1

is valid both for t>=2 and t<=-2. The possible exceptional integer t=-1
is excluded by the affine row itself. Thus gr_t=-1 is impossible and x>=1.
It follows that |q|>=2, so the retained q^t request forces t>=0. The
affine row excludes zero and gives t>=m.

The crucial dependency order is therefore

    affine nonvanishing -> linear F magnitude -> frame interpretation
    -> signed D^x -> x>=1 -> signed q^t -> positive t.

No classification or growth estimate for a negative standalone Pell center
is used to justify its own positive interpretation.

## 2. Pell growth remains sufficient at t=2

Once t>=2, a=4t+1>=9 is an ordinary positive odd Pell parameter. The norm
and nonzero F imply |F|=Y_n(a) for n>0. The inherited identities

    Y_n(a)=n mod(a-1),     v2(Y_n(a))=v2(n)

are valid for every such a. Because 4t divides F, the first identity gives
4t|n. The exact valuation of F is19+v2(t), so n/(4t) is a positive integer
of valuation17. Hence n>=dt. The recurrence estimate gives

    |F| >= (8t+1)^(dt-1) >= (8t)^(dt-1).

The new constructor threshold is also valid at t=2. A depth-zero leaf is
either a local parameter in [0,t), or 0 or 1. Its value plus one is at most t.
For all M>=0,

    E(M,M)+1=8M^2+14M+8 <=8(M+1)^2.

Induction at the authenticated maximum depth19 gives the strict label bound

    label < L=8^(d-1)t^d.

The exact comparison is

    (8t)^(dt-1)/L^t = 8^(t-1)/t >=1.

Thus |F|>=L^t and, in particular, |F|>t. No threshold16 estimate is hidden
in this calculation. Constants 0 and 1 remain covered at the minimum2.

## 3. The later sign recovery uses only these weaker hypotheses

The incoming initially signed-F radix proof needs t>=2 and |F|>t, both now
established. In the retained order:

1. The request q^(y+1) gives y+1>=0; since |y|>=|F|>1, this gives
   y>=|F|>0.
2. If x=1, the initial endpoint gives (y+1)r0=-F, impossible because
   0<|F|<=y<y+1. Thus x>=2.
3. The terminal endpoint now has a positive modulus and x-1>0, so
   x>=2+(t+1)y.
4. |q+1|>=3 allows all retained q+1 requests to orient their exponents.
   In particular F+t>=0. Since |F|>t, this gives F>0.
5. The C request gives C>=0, and the already authenticated C anchor
   excludes zero. Therefore C>0, D>0, and q>0.
6. With F>0 and y>=F, the initial endpoint forces r0>=0 and x>=F+1.

This retains the same exact source interpretation and uses no positive-F
premise before its proof.

## 4. The threshold 2 CRT and digit margins are adequate

The proof replaces every cited large-horizon use by explicit bounds. First,

    F>=L^t>=t^(2t)>=(t!)^2>=lcm(1,...,t)^2.

The first inequality follows from the Pell argument, and the second uses
d>=2. The factorial bound is valid by t!<=t^t. This is stronger than what
the inherited factorial-free selector radius requires.

Second, t>=2 gives L>=2^(4d-3), so F>=2^(8d-6)>2^32 and x>=F+1.
The estimate `(2x)^(2^23)<2^x` is very safe at this threshold: at x=2^32,
its logarithmic comparison is33*2^23<2^32, and log2(2x)/x is decreasing
for x>=2^32. The bound on the local input sum also remains correct:
F>t and t>=2 imply t+F<2F<=tF<=ty, and hence

    2+t+x+y+F < x+2+(t+1)y <=2x.

Third, the anchor cap yields C>F+t>t>=2. Every needed upper argument is
at most C, while the three lower cutoffs t,y+1,x are at most x. Therefore

    binom(a,j) <= C^x < q/2^x

for every relevant coefficient. The genuine low tail is strictly below

    [C^x/(q-1)]q^k <2^(1-x)q^k<q^k/32.

The encoded remainder's absolute bound q^k/2 and its congruence with that
tail force equality, since the absolute difference is below q^k. This
reasoning is unchanged at t=2 because it uses the much larger x threshold.

The initial B digit is also sound: from B eta=C+F+1 with nonzero integral
eta, |B|<=D/2<q/2, whereas the genuine binomial is below q/32. Congruence
modulo q forces exact equality. The necessary N|q is retained via B|D and
N=B^x, rather than being inferred from an omitted old factorization.

## 5. Cofinal2-adic completeness works for all three m

Write m=2^r with r=1,3,4, and choose a sufficiently large positive horizon

    t=m mod2^(r+22).

This progression is cofinal. It gives t=m(2z+1) for an integer z, exact
v2(t)=r, and a zero binary digit at position19+r. Define

    n0=dt, y0=Y_n0(4t+1), a0=X_n0(4t+1).

Since n0 is divisible by4t, the congruence modulo 4t yields t|y0. Its exact
valuation is19+r. Therefore dt|y0 and b0=y0/(dt) is odd. The index n0 is
even and the Pell center is odd, so a0=1 modulo 4 (indeed modulo 8).

For L0>r+22 with 2^L0>t, let R0=L0-19-r>0. The normalized Pell
permutation lemma for a0=1 modulo 4 is applicable. Both t/m and b0 are odd,
so the residue of their product is a unit modulo 2^R0. An odd positive index
s can be selected, cofinally, to satisfy

    (t/m)b0Y_s(a0)=1 mod2^R0.

Pell composition gives F=y0Y_s(a0)>0, and

    F/(dt)=b0Y_s(a0) is odd,
    F=2^(19+r) mod2^L0.

Consequently u=(F/(dt)-1)/2 is integral and every standalone growth row is
satisfied. Below bit L0, F has only bit19+r set, while t has that bit zero;
above bit L0, t has no bits at all. Thus their binary supports are disjoint
and binom(F+t,t) is odd. This is exactly the parity needed for the even
CRT representative C.

The choice of odd beta multiplier is also correct. It can contain every odd
prime <= t, while F supplies the factor 2. Every prime <= t then divides y.
A common prime of two moduli 1+iy and1+jy would divide j-i<=t but be coprime
to y, a contradiction. No unjustified t! divisibility or growing 2-adic
valuation of F is needed.

Finally the choices are acyclic: choose the horizon and F, then y and beta
code x, then B and N, then non-anchor representatives and the even cofinal
anchor C, then D and q, and finally the shared Pell frame. In particular the
requirement that C exceed all relevant indices is imposed after those
indices are determined, and the ability to make C even uses the already
proved oddness of N.

## Review boundary

The above checks establish the validity of the new semantic modification
relative to the explicitly imported lemmas. They do not prove the
consistency of ZFC, exhibit a Diophantine zero, or replace the separately
required literal coefficient/projection verification. No unresolved gap was
identified in the newly reviewed bootstrap, threshold, digit, or completeness
arguments.
