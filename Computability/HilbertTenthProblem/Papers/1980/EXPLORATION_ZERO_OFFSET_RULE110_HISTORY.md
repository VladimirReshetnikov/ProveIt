# A complete 75-operation Rule 110 finite-history family

A zero-offset affine local test removes the repunit addition from the
local rule. A three-field mask accommodates its two forbidden bits at
the scale q^5. Together these give **75=43M+32A**, with25 positive
supplied unknowns and16 equations, for every fixed radix b=2^d, d>=7.
Numerals and equality comparisons are free; scalar products are charged.

For positive numerical parameters I,F, the exact endpoint relation is:
I and F are Boolean radix-b words and a positive number of zero-exterior
moving steps x -> b Rule110(x) carries bI to bF. This is a complete
finite-history certificate, with a positive converse. It is decidable
and supplies no universal input/halting interface. Changing from the
radix16 certificate76 changes the numerical interpretation of I,F;
unchanged numerical endpoint predicates are not claimed equivalent.
The established universal bound remains90.

[The checker](../verification/explore_zero_offset_rule110_history.py) and
adjacent JSON provide a complete source at b=128 and complete source
and canonical-history checks at b=256,512. The general proof below covers
every fixed d>=7. The b=256 instance also permits every positive integral marker
position in the previously proved square-offset selector: its even bit
width avoids the even-position restriction that b=128 would introduce.
That observation is conditional, not an integrated Cook compiler count.

## 1. The exact zero-offset local relation

For Boolean a,b0,c,y, put

    v=18a+23b0+23c+42y.

Then v AND36=0 if and only if y is the Rule110 output. All raw values
lie in[0,106]. The full table lists the values at both choices of y:

| a b0 c | Correct y | v at y=0 | v at y=1 |
|---|---:|---:|---:|
| 000 | 0 | 0 | 42 |
| 001 | 1 | 23 | 65 |
| 010 | 1 | 23 | 65 |
| 011 | 1 | 46 | 88 |
| 100 | 0 | 18 | 60 |
| 101 | 1 | 41 | 83 |
| 110 | 1 | 41 | 83 |
| 111 | 0 | 64 | 106 |

The mask36 forbids bits2 and5. Since106<128<=b, valid aligned Boolean
planes have no radix-b carry in this relation. At larger radices the
mask need not forbid the unused high bits: the actual local formula
will bound the raw digit after Boolean source recovery.

If B=bC and its left-neighbor word is bB, substitution gives

    U=lambda_b C+42Y,
    lambda_b=18b^2+23b+23.                                  (1)

The fixed numeral lambda_b is297879 at b=128,1185559 at b=256, and
4730391 at b=512. Equation (1) costs2M+1A, compared with2M+2A for
the prior affine local expression containing J. It is not used for
digitwise inference until the geometry and Booleanity proofs below.

## 2. Complete source and operation ledger

Supply eight positive outer unknowns

    q,A,quot,H,C,Y,J,alphaI

and the same seventeen positive kernel unknowns as in the
[linear-width76 source](EXPLORATION_LINEAR_WIDTH_RULE110_HISTORY.md):

    a,c,d_p,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

Here d_p is the main Pell coordinate, distinct from the fixed bit width.
The code uses `awidth` for A and the retained name `d` for d_p. Define
by counted arithmetic

    W=bA, L=q^3, D0=q^5,
    B=bC, T=B+H, U=lambda_b C+42Y,
    P=T+qY+q^2U,
    M=J[(b-2)(q+1)+36q^2].                                 (2)

The six outer equations are

    q=W*quot,
    q-1=H(W-1),
    I+alphaI=A,
    I+WY=C+qF,
    (b-1)J=q-1,
    r=(L-P)(L-1)+M.                                       (3)

For X=wD0, Z=sD0, Delta=a^2+4a+3, and u=jc-(2r+1), the ten
retained fixed-minus kernel equations are

    X Z^2(X Z^2+1)k^2=tau(tau+1),
    c=Zk+eta, k=eta+zeta, k=r+1+hXZ,
    a=Z(X+1), d_p=X+ac+gamma(4a+3),
    d_p^2=Delta c^2+1,
    (ic^2)^2=Delta(f^2-1),
    Delta(f^2-1)(u^2-y_aux^2)=1-y_aux^2,
    u=of-c.                                                (4)

The computed integer u may have either sign in a putative solution.
Soundness uses no assumed parity; the positive converse uses the odd
index recovered from the actual new mask.

| Part | M | A | Total |
|---|---:|---:|---:|
| q^2,L=q^3,D0=q^5 | 3 | 0 | 3 |
| W=bA,W*quot,q-1,W-1,H(W-1) | 3 | 2 | 5 |
| U=lambda_b C+42Y | 2 | 1 | 3 |
| Input bound | 0 | 1 | 1 |
| Temporal equation | 2 | 2 | 4 |
| B=bC,T=B+H | 1 | 1 | 2 |
| P=T+q(Y+qU) | 2 | 2 | 4 |
| M=J[(b-2)(q+1)+36q^2] | 3 | 2 | 5 |
| Repunit equation, sharing q-1 | 1 | 0 | 1 |
| Index equation | 1 | 3 | 4 |
| Outer subtotal | 18 | 14 | 32 |
| Fixed-minus kernel | 25 | 18 | 43 |
| **Complete source** | **43** | **32** | **75** |

In particular, the mask computes q+1, (b-2)(q+1),36q^2, their sum,
and its product with J. It does not use the incorrect factorization
(q+1)(36q+b-2). The scale uses three products q^2,q^3,q^5; no variable
power is free. The source checker verifies all16 independent residuals.
Only the auxiliary norm uses the usual acyclic correction: the
preceding residual [(ic^2)^2-Delta(f^2-1)] times(u^2-y_aux^2).

## 3. Pre-power bounds and the nonsquare kernel scale

Consider an arbitrary positive integer solution. From A=I+alphaI>=2,
we have W>=2b>=256 and q>=W. All coefficients in M are positive and
at most b-1, so the paid repunit equation gives

    0<M<=(b-1)J(1+q+q^2)=q^3-1<L.

If P>=L+1, then r<=-(L-1)+M<=0, a contradiction. Initially this
only proves P<=L. Since the lower terms T+qY are positive,

    q^2U<P<=q^3, hence U<q.

Consequently C<q/lambda_b, Y<q/42, and b^2 C<q, because
lambda_b>b^2. Furthermore

    H=(q-1)/(W-1)<q/(b-1),
    T=bC+H<[b/lambda_b+1/(b-1)]q<q.

The last bracket is less than1 for every b>=128; for example
b/lambda_b<1/(18b) and1/(b-1)<=1/127. All three actual fields
T,Y,U are positive integers below q. Their concatenation now proves

    0<P<q^3,
    q^3-1<r<q^6,
    q^5<r^2.                                               (5)

For the lower index bound use L-P>=1 and M>0; for the upper use
P>=1 and M<L. Integrality gives r>=q^3, proving the scale inequality.
No power conclusion, mask test, or Booleanity entered these bounds.

The scale D0=q^5 is not assumed square. The nonsquare audit in
[the positive Life bootstrap](EXPLORATION_LIFE_POSITIVE_BOOTSTRAP.md),
Section3, applies verbatim: take proof notation n0=q^2. Then

    n0>=64, n0<r<n0^3,
    D0>n0^2, X,Z>=D0,
    XZ>=q^10>r+1, a=Z(X+1)>q^10>2r+1,
    4r/a<4/q^4<1/2.

These are the actual uses of the scale in the first-index, relaxed
auxiliary-rank, and ratio arguments. The fixed-minus signed-index
argument of [the odd-index proof](EXPLORATION_ODD_INDEX_PELL_SIGNS.md)
recovers the same main index2r+1. The first-exponent growth hypotheses
hold before exponent decoding because r>=64 and X>=q^5>=4096:

    2^(3(2r+1))=8*64^r<X^(r+1)<a,
    X^3<=X^r<a.

The retained exponent and exact rounding arguments therefore give

    X=2^(2r+1), D0 divides binom(2r,r).                      (6)

Thus q is a power of two. Since(b-1)J=q-1 and b=2^d, the elementary
Mersenne divisibility criterion gives q=b^N for an integer N>=1.
The row width is not yet assumed aligned.

## 4. The mask types the fields before it aligns the rows

At q=b^N, M consists of three blocks of N radix-b digits:

    b-2, b-2,36.

Each Boolean mask b-2 has d-1 set bits;36 has two. Therefore

    popcount(M)=2dN,
    log2(L)=3dN,
    log2(L)+popcount(M)=5dN=log2(D0).                        (7)

For arbitrary0<=P,M<L, the exact carry lemma gives

    popcount((L-P)(L-1)+M)<=log2(L)+popcount(M),
    equality iff P AND M=0.

It includes P+M>=L, where the inequality is strict. Combining it with
(6) and the central-binomial valuation formula forces equality in(7).
The raw field bounds justify extraction and prove

    T,Y are Boolean radix-b words,
    each digit of U has bits2 and5 absent.                   (8)

No restriction on U's other high bits is assumed for larger b.

Now W divides q, so write W=2^e with e>=d+1. The geometric equation
implies e|dN, hence q=W^t and H=1+W+...+W^(t-1). If t=1 then
W=q is already a power of b. If t>=2, the exact temporal identity gives

    T=bI+bWY-bqF+H=bI+1+W modulo bW.

Here W is a multiple of b, so W^2 is a multiple of bW, and
0<I<A=W/b gives0<bI+1<W. The bit at position e in T is consequently1,
without a carry from its lower part. By Boolean typing in(8), every
set bit of T is at a position divisible by d. Hence d|e. In both cases

    W=b^m, q=W^t, m>=2, I<W/b.                            (9)

This is the initial-marker alignment argument of the76 source with
general radix. Its typed marker T=B+H is retained in full.

## 5. Recover the causal history without assuming C is Boolean

The temporal equation, C,Y<q and I<W first give F<W, and then the
base-W rows obey

    c_0=I, c_(j+1)=y_j for j<t-1, y_(t-1)=F.               (10)

Indeed, qF=I+WY-C<Wq, and reducing modulo W starts an ordinary
carry-free row decomposition. All y_j are Boolean radix-b words by(8).

Subtracting the row-start word H from Boolean T makes every row-start
digit of B=T-H belong to{0,b-2,b-1}. A zero start has no incoming or
outgoing borrow, leaving the rest of its row Boolean. The first start
is zero because B=bC. The input bound I<W/b makes the next start zero,
as it is the highest digit of c_0=I. Each subsequent c_j is a Boolean
Y row, so its highest digit is0 or1; the corresponding next B start,
which belongs to{0,b-2,b-1}, can only be0. Induction proves that B is
Boolean and every source row begins with zero. This proof uses masked
Y, not the local Rule110 predicate that remains to be decoded.

The neighbor words bB and C=B/b are now Boolean, and bB=b^2 C<q was
already proved. Equation(1) is exactly

    U=18(bB)+23B+23C+42Y.

Every raw local digit lies in[0,106], below every permitted radix.
There are no carries, including at b=256 and larger. Consequently(8)
and the scalar table give the exact Rule110 output at each digit.
At row starts Rule110(a,0,c)=c removes the preceding-row dependence.
At row ends the following row begins with zero. Beyond the stored
source, Rule110(a,0,0)=0 supplies the zero exterior.

The top digit of the entire B word is zero because B<q/b, and its
corresponding output digit is zero. Together with(10), this proves
F<W/b and yields the genuine positive-height moving history

    b_0=bI,
    b_(j+1)=b Rule110(b_j),
    bF=b Rule110(b_(t-1)).                                (11)

It also recovers Boolean typing of both numerical parameters I,F.

## 6. Full positive converse at the new actual index

Conversely, take a genuine t>=1 history(11) between positive Boolean
radix-b parameters. Choose m sufficiently large that I<b^(m-1) and
all source and raw-output rows fit with two high blank columns. Put

    W=b^m, q=W^t, A=W/b, quot=q/W,
    H=(q-1)/(W-1), J=(q-1)/(b-1), alphaI=A-I.

Pack the source and raw output rows into B,Y and set C=B/b. These are
positive: the source is nonempty, and its highest occupied cell remains
alive in the raw rule. All eight outer coordinates are positive, all
temporal equations hold, and B,T,Y are Boolean with the stated bounds.
The local scalar table gives U AND(36J)=0. Although its individual
digits may be zero, the whole U is strictly positive because C>0 and
lambda_b>0. No all-ones offset is needed for this positivity.

The fields have P<L and P AND M=0, so define r by(3). The exact mask
lemma gives D0|binom(2r,r). Moreover H and T are odd, q is even,
P is odd and M is even. Thus r is odd.

All sixteen remaining positive kernel witnesses are chosen at this
new actual index. Write I_p=2r+1 and use standard Pell sequences
chi,psi. An explicit choice is

    X=2^I_p, Z=floor((X+1)^(2r)/X^r), w=X/D0, s=Z/D0,
    a=Z(X+1), A_p=a+2, Delta=A_p^2-1, P_p=2XZ^2+1,
    c=psi_(A_p)(I_p), d_p=chi_(A_p)(I_p),
    k=psi_(P_p)(r+1), eta=c-Zk, zeta=k-eta,
    tau=(chi_(P_p)(r+1)-1)/2,
    h=(k-r-1)/(XZ), gamma=(d_p-X-ac)/(4a+3),
    m_aux=2cI_p, f=chi_(A_p)(m_aux),
    R_aux=Delta psi_(A_p)(m_aux), i=R_aux/c^2,
    y_aux=psi_(R_aux)(I_p), u=chi_(R_aux)(I_p)/R_aux,
    j=(u+I_p)/c, o=(u+c)/f.                               (12)

The same nonsquare-scale converse proved in the positive Life bootstrap
applies: D0<r^2<X, both are powers of two, and the binomial congruence
makes both w and s positive integers. The retained ratio and exponential
proofs make eta,zeta,tau,h,gamma positive integral. The auxiliary
construction has c^2|R_aux. Since r is odd, its congruences are
u=-I_p modulo c and u=-c modulo f, giving positive integral j,o.
Pell norms and these identities establish every equation(4).

This is a full positive extension, not a reuse of the old radix16 index
or witnesses. Enormous Pell coordinates are specified by the proved
construction, rather than materialized in the finite checker.

## 7. Evidence and boundary of the result

The checker independently compares all16 source polynomials for each
of b=128,256,512, with the same75-operation ledger and domains. Its
radix128 pre-power tests include2,160 arithmetic candidates,268 with
positive index, of which266 have non-power q; these are bootstrap
tests, not claimed kernel solutions. It checks65,519 initial marker
blocks, rejecting all49,009 misaligned ones.

The complete one-cell mask check examines every2,097,152 possible P,
including606,078 overflow cases. The bounded history enumeration
examines23,500 Boolean T words, including7,936 misaligned strides,
and17,544 compatible final words. All15 accepted outer tuples are
actual histories. There are30 further canonical histories at radix128
and60 at radices256,512, using five inputs and heights1,2,3,4,8,16.
Every accepted tuple checks the complete outer equations, strict
positivity, field extraction, exact mask valuation, odd parity, and
the nonsquare kernel range hypotheses.

The affine discovery was a bounded search, not a lower bound for other
local encodings. The truth table proves the selected local law, and
Sections2-6 prove the full unbounded certificate. The endpoint predicate
is decidable: its highest occupied digit advances by exactly one per
moving step, determining the only possible positive height. The general
universal input and halting interface remains separate.

Review status: author and independent complete scoped proof/source review
pass. The independent fresh run matches the saved JSON exactly and keeps
the proof, source and receipt hashes unchanged. It covers all48 source
comparisons, all2,097,152 mask values and all90 canonical histories.
