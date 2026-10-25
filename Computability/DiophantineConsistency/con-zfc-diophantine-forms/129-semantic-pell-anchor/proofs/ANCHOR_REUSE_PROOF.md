# Reusing the derived label index as the certified Pell bound

Independent mathematical audit for the combined direct C222 compiler.
The comparison source is ProveIt commit
`f4d8db99e060339f3306a04d507c35bc1d0d68c5`.

The argument below validates the proposed further reduction, subject to
the emitted graph implementing the stated rows. It is an ordinary proof,
not a new proof-assistant certificate or a claim of global optimality.

## 1. The general bounded-index lemma

Let W>=3, A-1>W^3, 2<=H<=W, and let r<=W-2. Fix natural requested
indices k_1,...,k_r with k_i<W. Retain one complete polynomial
indexed-Pell certificate for

    (U,V)=(X_H(A),Y_H(A)).

For every other requested index retain only its principal Pell norm.
For ordinary coordinates this is

    x_i^2-(A^2-1)y_i^2=1.

Add just the two common rows

    V = H+1+s+sum_i y_i,
    sum_i(y_i-k_i)^2 = (A-1)q,

with all new witnesses natural. Then every surviving principal pair
has ordinate y_i=Y_(k_i)(A). In particular the rows themselves imply
k_i<H; a separate nominal-index inequality is unnecessary.

Proof. Pell classification gives y_i=Y_(j_i)(A) with j_i>=0. The first
common row gives y_i<V=Y_H(A), hence j_i<H<=W. Independently, the
semantic frame bounds the intended k_i<W. Reduction modulo A-1 gives
A-1 dividing E=sum_i(j_i-k_i)^2, while

    0<=E<=r(W-1)^2<W^3<A-1.

Thus E=0 and j_i=k_i for every i. This proof did not assume k_i<H.

Conversely suppose every k_i<H and A>W+1. Choose the canonical pairs.
Their squared-error sum is a nonnegative multiple of A-1. Moreover,

    Y_H(A)>(2A-1)Y_(H-1)(A),
    sum_i Y_(k_i)(A)<=r Y_(H-1)(A).

Since r<=W-2, A>W+1, and H<=W, one has 2A-1-r>H. Also H>=2 gives
Y_(H-1)(A)>=1. Therefore Y_H(A)-sum_iY_(k_i)(A)>H. The required
aggregate slack s is natural. This supplies both new witnesses explicitly.

The full anchor certificate's bound H<=V is supplied by the aggregate
row itself. A principal norm alone cannot certify this anchor index.

## 2. The actual anchor

Use H=J, the already requested upper index in the derived-label range
binomial. The fixed C222 Cantor constructor is

    I(a,b)=2(a+b)(a+b+1)+4b.

The source's J is the sum of the nine axiom-conclusion polynomials,
a,b,I(a,b),A(a,b), and1. Every summand is nonnegative at natural
inputs. Hence

    J>=I(a,b)>=2a^2.

J is a polynomial in the encoded local columns, chosen before the
Pell frame and all its private witnesses. Its pair was already needed
to recognize N | binom(J,t+1). Reuse the full anchor pair for that
modular request and remove J from the independent seed list. The
remaining fourteen seed indices are the other exact-power exponents
and modular upper indices.

Retain the enlarged frame

    W=r+2+sum(distinct exact-power atoms and modular upper indices).

This gives J<W, every remaining k_i<W, and r<=W-2. Keep the separate
lower scale L with A=L+sigma. Exactly as in the previous audit,
A-1>W^3 and A>W+1 follow before any exact powers are interpreted.
The atom q is already in this sum, so W>=q+r+2>q+1. There is no need
to insert q+1 again as a separate frame atom.

No row J>=sum_i k_i is added. The bounded-index lemma supplies all
soundness requirements. Only completeness needs a suitable choice of
the encoded CRT representatives; it is supplied next.

## 3. One CRT representative can be made large at no new witness cost

Start from a finite refutation and the inherited bounded source data.
Set F=t!, t>=16, and

    d_i=1+F^2/i,  B=product_i d_i=binom(F^2+t,t),
    R=2+t+x+y+F,  K=2R,  N=B^K.

The strengthened CRT construction chooses positive representatives for
the eight local columns and the index C modulo each d_i^(2K), with
each representative at most

    product_i d_i^(2K)=B^(2K)=N^2.

Replace only the encoded a-column representative by

    a_new=a_old+N^2.

Then N^2<a_new<=2N^2. All eight other representatives remain in
(0,N^2]. Since N^2 is divisible by every d_i^(2K), every original
residue is preserved to exactly the same CRT precision. Polynomial
congruences for the local C222 condition and the derived J are also
preserved. The range-binomial divisibilities remain valid by the same
falling-factorial valuation argument; no false converse of the range
lemma is being invoked.

Replace the old aggregate bound by

    C+sum(eight encoded columns)+aggregate_slack=10N^2.

Its slack is nonnegative. There are still nine aggregate requests.
The coefficient10 is a bound coefficient, not a count of requests.

There is no need to introduce a new polynomial guard a>N^2. This is a
choice made only in the constructive completeness proof. Soundness is
valid for every tuple satisfying the final equations, whether or not
its a-coordinate has this extra property.

## 4. The reused anchor exceeds every other requested index

The nine CRT representatives are at most2N^2. The remaining five
nominal indices are

    t, K, y+1, x+1, F^2+t.

As F,t,x,y<R and B>=2,

    N=B^(2R)>=4^R,
    F^2+t<R^2+R<=4^R<=N,
    K=2R<4^R<=N,
    t,x+1,y+1<=R+1<=N.

The elementary inequality R^2+R<=4^R holds for every positive integer
R. Thus every nonanchor requested index is at most2N^2. But

    J>=2a_new^2>2N^4>2N^2,

because N>=2. Therefore all fourteen other requested indices satisfy
k_i<J. In fact J is much larger than their sum, but that stronger
bound is not used and incurs no extra equation.

Choose the semantic exact-power outputs and indices, compute W, then
choose L and a sufficiently large A in the required common-root
congruence class. The bounded-index lemma now supplies all cap,
seed, pooled-error, and aggregate witnesses.

## 5. Enlarging the CRT aggregate does not invalidate radix bounds

The radix remains q=N^K. For any ordinary binomial upper index
n<=10N^2 and any required lower index k<=R-1,

    binom(n,j)<=n^k<=10^k N^(2k)
        <2^(4R)N^(2k)<=N^(2k+2)<=N^(2R)=q

for j<=k, with the usual convention binom(n,j)=0 when j>n. The
unchanged strict inequality10<16 is all that is needed in place of9<16.

For the derived J, the retained literal positive-DAG majorant is

    J(a,b,c,d)<=(n+1)^ell,  ell=2^22,

when all four inputs are at most n. At n=10N^2 and N>=11,

    n+1<=N^3,  J<=N^(3ell).

The actual N is far larger than11. The inherited t>=16 factorial
estimate still gives3ell(t+1)<=2F<K. Consequently every needed lower
binomial coefficient of J is strictly less than q. The exact factorial
binomial has its separate pre-factorial radix proof and is unchanged.

Thus all modular-digit interpretations remain sound, including the
binomial containing the very large reused anchor J.

## 6. Consecutive ordinate coordinates, if selected

Instead of a principal pair (X,Y), use nonnegative (Y,Z) with

    Y^2+Z^2-2AYZ=1.

Set X=AY-Z. Then X^2-(A^2-1)Y^2=1, so Pell classification applied to
|X| gives the same canonical ordinate Y=Y_j(A), even before the sign
of X is known. The pooled-error proof therefore still recovers j=k.

Every such seed participates in a retained residue equation

    bY=Z+nonnegative terms,

where b is either an exact-power base or q+1. The exact bases occur
in the frame, while q+1<W follows from q's presence and the fixed
offset. Thus both are strictly less than A. If Y=0,
the norm gives Z=1, contradicting this equation. Hence Y>0 and
Z<=bY<AY, so X=AY-Z>0. This eliminates the conjugate orientation.
The canonical solution is Z=Y_(k-1)(A), and all requested indices
here are positive. The full anchor pair may retain ordinary coordinates.

## 7. Scope and attribution

The one-cap and pooled-square-error idea is inherited from the261
packet. The merged factorial/CRT binomial and six exact powers are
inherited from the319 packet. Dominant denominator reuse, if enabled,
is inherited from the Residue Compiler packet. The contribution
validated here is their compatible composition and the further reuse
of an existing, deliberately enlarged CRT-derived upper index as the
only fully certified Pell anchor.

The integer source/calculus calibration is inherited via
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`. Their immediate
declarations are unconditional and proof-bearing; no machine execution
hypothesis is used by the first interface. The full transitive Lean
dependency closure has not been rebuilt in this audit. The resulting
claim is an ordinary proof formalizable in ZFC plus independently
checked finite algebra, not a newly completed end-to-end formal proof.
