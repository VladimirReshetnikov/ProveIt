# A 77-operation radix-sixteen Rule 110 history certificate

The one-field local relation and a nonuniform mask with a zero padding
block give a complete finite-history certificate with **77 operations:
44 multiplications and 33 additions/subtractions, 25 positive unknowns
and 16 equality comparisons**. Numerals and equality comparisons are free.

For positive parameters I,F its exact meaning is: I and F are Boolean
radix-sixteen words, and a positive number of zero-exterior moving Rule 110
steps b -> 16 Rule110(b) carries 16I to 16F. This endpoint relation is
decidable. It is the radix-sixteen counterpart of the published
79-operation radix-eight history, not numerical equivalence for unchanged
I,F, and it supplies no universal input or halt interface. The established
universal certificate bound remains 90.

The complete source and finite checker are
`../verification/explore_one_field_rule110_history.py`, with an adjacent
JSON receipt. The six-operation local component remains separately frozen
in `EXPLORATION_RULE110_THREE_BIT_FIELD.md`.

## 1. Complete source and operation count

Supply eight strictly positive outer unknowns

    q,v,quot,H,C,Y,J,alphaI

and seventeen strictly positive kernel unknowns

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

The notation separates the local output Y from Y_pell below. Define the
following quantities by counted arithmetic, rather than supplying them:

    W=v^4, L=q^4, D0=q^6,
    B=16C, T=B+H, U=307C+4Y+J,
    P=T+qY+q^3U,
    M=J(q+1)(4q^2+14)
     =J(14+14q+4q^2+4q^3).

The six outer equations are

    q=v*quot,
    q-1=H(W-1),
    I+alphaI=v,
    I+WY=C+qF,
    15J=q-1,
    r=(L-P)(L-1)+M.                              (1)

For the fixed-minus base-two kernel, put

    U_pell=wD0, Y_pell=sD0,
    D_pell=a^2+4a+3, K=D_pell(f^2-1),
    u=jc-(2r+1).

The ten retained kernel equations are

    U_pell Y_pell^2(U_pell Y_pell^2+1)k^2=tau(tau+1),
    c=Y_pell k+eta,
    k=eta+zeta,
    k=r+1+h U_pell Y_pell,
    a=Y_pell(U_pell+1),
    d=U_pell+ac+gamma(4a+3),
    d^2=D_pell c^2+1,
    (ic^2)^2=D_pell(f^2-1),
    K(u^2-y_aux^2)=1-y_aux^2,
    u=of-c.                                      (2)

This is exactly the base-two odd-index sign variant proved in
`EXPLORATION_ODD_INDEX_PELL_SIGNS.md`. Its arithmetic differs from the
retained even-index kernel at just two additions/subtractions. It still
costs 43=25M+18A. All other first-index, first-exponent and rounding
equations are present.

| Outer component | M | A | Total |
|---|---:|---:|---:|
| q^2,L=q^4,D0=q^6 | 3 | 0 | 3 |
| v*quot,v^2,W=v^4,q-1,W-1,H(W-1) | 4 | 2 | 6 |
| U=307C+4Y+J | 2 | 2 | 4 |
| I+alphaI | 0 | 1 | 1 |
| Temporal equation | 2 | 2 | 4 |
| B=16C and T=B+H | 1 | 1 | 2 |
| P=T+q(Y+q^2U) | 2 | 2 | 4 |
| M=J(q+1)(4q^2+14) | 3 | 2 | 5 |
| 15J=q-1, reusing q-1 | 1 | 0 | 1 |
| r=(L-P)(L-1)+M | 1 | 3 | 4 |
| Outer subtotal | 19 | 15 | 34 |
| Retained fixed-minus kernel | 25 | 18 | 43 |
| Total | 44 | 33 | 77 |

There is no supplied U, B or T and no explicit field-bound slack. The
checker verifies every primitive against all sixteen fresh source
polynomials. The penultimate norm comparison has precisely the usual
triangular correction

    [(ic^2)^2-D_pell(f^2-1)](u^2-y_aux^2),

whose first factor is the preceding exact equation. No field decoding is
used to justify that algebraic source comparison.

## 2. Positivity supplies the missing field bounds before the kernel

Consider an arbitrary positive integer source solution. From the input
bound v>=2, and from the geometry q>=W=v^4>=16. Also 15J=q-1. Because
the four coefficients of M are positive and at most 15,

    0<M<=15J(1+q+q^2+q^3)=q^4-1<L.              (3)

All this holds without knowing that q or v is a power of two.

If P>=L+1, the last equation of (1) gives r<=-(L-1)+M<=0,
contradicting positive r. Hence P<=L. Its positive lower terms T+qY
then imply q^3U<L, so U<q. The local definition gives

    C<q/307, Y<q/4,
    B=16C<16q/307<q/16, A:=16B<q.               (4)

The geometric word has H=(q-1)/(W-1)<q/15. Therefore

    T=B+H<(16/307+1/15)q<q.                     (5)

All three actual packed fields T,Y,U are now strictly positive integers
below q. The unused q^2 field is zero. In particular

    P<=q^3(q-1)+q(q-1)+(q-1)
      =q^4-q^3+q^2-1<L,
    L-P>=q^3-q^2+1.                             (6)

Equations (3),(6) prove

    q^3<r<q^8.

For the lower inequality use r>=(q^3-q^2+1)(q^4-1)+M; for the
upper use P>=1 and M<L. Set n0=q^3. We consequently have

    n0>=64, n0<=r<2n0^3, D0=n0^2.               (7)

These are the exact preliminary range hypotheses of the retained
base-two kernel. No bit predicate, power conclusion, field sparsity or
canonical-history premise has entered this bootstrap.

## 3. The kernel, geometry and heterogeneous mask

The fixed-minus kernel theorem uses (7), positivity and (2). Its
soundness does not assume parity and yields

    U_pell=2^(2r+1), D0 divides binom(2r,r).      (8)

The sign change affects only the final auxiliary index identification:
u=jc-(2r+1)=of-c supplies the same squared congruence and hence the same
main index as the plus version. Its complete proof, including the
possibility of a signed computed u before the Pell classification, is
the cited base-two odd-index note.

Since q^6 divides a power of two, q is a power of two. Since v divides q,
write v=2^m with m>=1. The divisor W-1=v^4-1 of q-1 implies

    W=16^m, q=W^t=16^(mt),
    H=1+W+...+W^(t-1)                            (9)

for an integer t>=1. This uses the elementary criterion
2^a-1 divides 2^b-1 iff a divides b. Thus every field boundary is aligned
before the mask is decoded. Write N=mt, so J=(q-1)/15 is the length-N
radix-sixteen all-one word.

For arbitrary 0<=P<L=2^b and 0<=M<L, the exact popcount inequality
proved in the one-field component is

    popcount((L-P)(L-1)+M)<=b+popcount(M),

with equality exactly when P & M=0. Its proof includes P+M>=L: such an
overflow makes the inequality strict. Here b=16N. The four N-digit
blocks of M have radix-sixteen digits 14,14,4,4, respectively. Thus
popcount(M)=8N, and

    D0=q^6=2^(24N).

By (8) and v2(binom(2r,r))=popcount(r), equality is forced at 24N.
Hence P & M=0. Bounds (6) identify the four fields of P as T,Y,0,U.
The first two mask blocks forbid bits 1,2,3; the last two forbid bit 2.
Consequently T and Y have radix-sixteen digits zero or one, and U has
digits in

    S={0,1,2,3,8,9,10,11}.                       (10)

The zero third field causes no restriction. Its one forbidden bit per
cell raises the valuation threshold to an integral power q^6 without
adding a supplied plane or any arithmetic to P.

## 4. Recover Boolean source rows and the actual local transitions

The subtraction argument used for the 79-operation history transfers
with its hypotheses now proved anew. If m=1, H=(q-1)/15=J is the largest
Boolean radix-sixteen word below q. Boolean T=B+H is strictly larger,
a contradiction. Thus m>=2, and I<v<=W/16.

Since C,Y<q and I<W, the temporal equation first implies F<W.
Indeed, qF=I+WY-C<Wq. Its base-W expansion then gives, for the source
rows c_j and output rows y_j,

    c_0=I, c_(j+1)=y_j for j<t-1, y_(t-1)=F.     (11)

Subtract the Boolean row-start word H from Boolean T. At each row start
the normalized radix-sixteen digit of B=T-H lies in {0,14,15}. A zero
start has zero incoming and outgoing borrow, making the rest of that
B row Boolean. The first start is zero because B=16C. The input bound
I<W/16 makes the next start zero: that start is the highest digit of
c_0=I. Every later c_j in (11) is a Boolean Y row. Its highest digit
is zero or one, while the corresponding next B row start is in
{0,14,15}; it must be zero. Induction proves that B is Boolean and every
row starts with zero. This argument uses the independently masked Y,
not the local rule that is still to be recovered.

Both neighbors A=16B and C=B/16 are now Boolean, and (4) gives A<q.
The definition of U is precisely

    U=J+A+3B+3C+4Y,

since 16^2+3*16+3=307. Every raw digit lies between 1 and 12, below
the radix. There are no carries. For Boolean a,b,c,y, the exact scalar
table in the one-field component states

    1+a+3b+3c+4y in S iff y=Rule110(a,b,c).

Thus each output digit is correct. At row starts, Rule110(a,0,c)=c
is independent of the possibly adjacent-row left input. At row ends,
the right input is zero because the next row starts with zero. Outside
the stored row, Rule110(a,0,0)=0. These observations give the genuine
finite zero-exterior rule on each row and resolve both seams.

The highest digit of the entire B word is zero by B<q/16. Its highest
Y digit is therefore zero too, as its right neighbor is zero. Thus
F<W/16, including the final moving row. Equation (11) gives exactly

    b_0=16I,
    b_(j+1)=16 Rule110(b_j),
    16F=16 Rule110(b_(t-1)).                     (12)

It also proves that I and F are Boolean radix-sixteen words. There is
no additional filter requiring a source occurrence of 111.

## 5. Full positive converse and automatic odd parity

Conversely, suppose positive Boolean radix-sixteen I,F are related by
t>=1 actual moving steps (12). Choose m large enough that v=2^m>I
and every source and raw output row fits in m cells with two blank
high columns. Set W=16^m, q=W^t, quot=q/v and H as in (9), and pack
the actual source and raw output rows into B,Y. Put

    C=B/16, J=(q-1)/15, alphaI=v-I.

All eight outer coordinates are positive integers. In particular the
rightmost source one has right neighbor zero and remains one under
the raw rule, so Y is positive. The first source is positive, so C is
positive. Their packed shifts are exact and the temporal equation holds.

The first column of every B row is zero, so T=B+H is Boolean. The scalar
relation constructs the unique U with digits in S, each at least one;
U is positive without a separate positivity argument for local Boolean
auxiliaries. The chosen high blank columns ensure A=16B<q. Hence
T,Y,U<q, P<L and P & M=0. Define r by (1). It is positive and satisfies
(7), either directly from the field bounds or from the bootstrap above.
The exact mask theorem gives D0 | binom(2r,r).

Finally H is odd, B=16C is even and q is even. Thus T, and hence P,
is odd. The mask M is even. Since L is even,

    r=(L-P)(L-1)+M is odd.                       (13)

The fixed-minus kernel therefore supplies every required positive
coordinate. Explicitly, use Jmain=2r+1 and the canonical main/first
Pell witnesses with U_pell=2^Jmain and
Y_pell=floor((U_pell+1)^(2r)/U_pell^r). The scale divisibilities give
positive integral w,s, and the existing ratio proof gives positive
eta,zeta,tau,h,gamma. For the auxiliary part, with A_pell=a+2, choose

    m_aux=2c Jmain, f=chi_(A_pell)(m_aux),
    R_aux=D_pell psi_(A_pell)(m_aux), i=R_aux/c^2,
    y_aux=psi_(R_aux)(Jmain), u=chi_(R_aux)(Jmain)/R_aux,
    j=(u+Jmain)/c, o=(u+c)/f.

The proved odd-index congruences and growth make these integers strictly
positive and establish every equation in (2). This is a full positive
converse at the actual newly computed index, not reuse of the old
radix-eight index or its even-sign witnesses. Huge Pell coordinates
are specified by the proved construction rather than materialized.

## 6. Exact scope and finite evidence

Every nonempty source retains its rightmost one in the raw rule. The
moving shift advances that position by one. Any accepted height must
therefore equal floor(log_16 F)-floor(log_16 I). Checking the Boolean
digits and simulating that many steps decides this endpoint predicate.
The reduction from 79 to 77 concerns this changed-radix finite-history
component; it is not a reduction of the universal 90-operation bound.

The fresh checker validates all 77 primitives, all sixteen source
comparisons, the single norm correction, and all supplied-coordinate
counts. It additionally checks 150 preliminary integer candidates,
including four nonpower-q positive-index tuples, to exercise the
pre-decoding bound argument. Those preliminary tuples are not claimed
to solve the Pell equations.

The complete bounded row-word enumeration examines 27,912 Boolean T
words, 371 surviving boundary candidates and 9,697 compatible final
words. Fifteen complete outer tuples are accepted and all produce the
actual moving history. Thirty further canonical histories cover five
inputs and heights 1,2,3,4,8,16. Each checks all six numerical outer
equations, positivity of every outer coordinate, every mixed-mask field,
the exact odd parity, central-binomial valuation and all kernel range
hypotheses. These finite checks supplement the general soundness and
positive converse; they do not replace either proof or establish a
universal interface. Author and two independent complete proof/source
reviews pass, and fresh verification reproduces the saved receipt.
