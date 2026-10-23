# Independent audit of the bounded-degree exponent replacement

This note checks the replacement of radix-five monomial exponents in the
Sun source-coding stage. It is an ordinary mathematical audit, not a proof
assistant certificate. All later Lucas and relation-combining theorems are
inherited unchanged. In particular, this note does not independently prove
Sun's ten-integer theorem or the K215/compiler endpoint.

## 1. Exact hypotheses and the zero padding coordinate

Let

    P(z_1,...,z_31) = sum_(|alpha|<=4) p_alpha z^alpha

be the fixed shifted quartic, with integer coefficients, P(0)>0, and
L=max |p_alpha| >=1. Let 0=w_0<w_1<...<w_31=W be integers for which sums
of four elements, repetitions allowed, determine the multiset uniquely.
Define e(alpha)=sum_i alpha_i w_i. Then e is injective on |alpha|<=4:
pad each multiset of |alpha| nonzero weights by 4-|alpha| copies of w_0=0.
The padding multiplicity is determined along with the positive weights.

The zero weight is the homogenizing/constant coordinate, NOT an additional
Diophantine unknown. The source input a is already fixed to zero and is
absent from P. There are exactly 31 positive weights for 31 source
unknowns. A B4 set with only 31 elements, or omission of the zero padding
coordinate in the verification, would not prove the required assertion.

Take any H>=4W (equality is allowed) and define

    c_alpha = (4-|alpha|)! product_i(alpha_i!) p_alpha,
    D(B) = sum_alpha c_alpha B^(H-e(alpha)).

All exponents are nonnegative. All exponents belonging to different alpha
are different, and |c_alpha|<=24L. The coefficient of B^H is 24P(0)>0;
every nonconstant monomial has positive e(alpha) and lies below this term.
Thus if B-1>24L, then

    D(B) >= 24P(0) B^H - 24L sum_(r=0)^(H-1) B^r >0.

There is no need to use H=4W+1. A constant term in D causes no difficulty.

## 2. Exact coefficient isolation, including off-central terms

For 0<=z_i<b put

    C_z(T)=(1+sum_i z_i T^w_i)^4.

Its multinomial coefficient at e(alpha) is

    24 z^alpha / ((4-|alpha|)! product_i alpha_i!).

Since e is injective, the coefficient of T^H in C_z(T)D(T) is precisely
24P(z). For any other exponent k, use nonnegativity of the coefficients
of C_z and the bound on the individual coefficients of D to obtain

    |[T^k] C_z(T)D(T)|
      <= 24L sum_j [T^j] C_z(T)
      = 24L(1+sum_i z_i)^4.

This is the needed off-central bound. It does NOT multiply L by the number
of source monomials. Each coefficient of D has only one alpha because of
the B4 property; convolution can have many summands, which the sum of all
coefficients of C_z already bounds.

Suppose B is a power of two and

    B/2 > 24L(1+31(b-1))^4.

Let m=H+4W and

    K=C_z(B)D(B)+(B/2)sum_(k=0)^m B^k.

Every base-B digit of K is an integer strictly between 0 and B, and its
digit at H is B/2+24P(z). The binary mask (B/2-1)B^H tests exactly the
lower binary digits of that digit. Among integers in (0,B), only B/2
is disjoint from B/2-1. Consequently

    K AND ((B/2-1)B^H) = 0  iff  P(z)=0.

If J=2K, multiplication of both operands by 2 gives

    J AND ((B-2)B^H) = 0  iff  P(z)=0.

One must use this binary-shift argument. Doubling K may introduce
base-B carries, so it would be incorrect to assert without qualification
that J has the same carry-free base-B digits.

## 3. Two-variable polynomial source code

Keep the old fixed coefficient constant beta_S=2^4269882 and put

    b=1+3f, B=beta_S b^4, cap=b B^W,
    ell=sum_(i=1)^31 B^w_i,
    N0=B^(W+1), N1=4B^(H+4W+1), N=N0 N1,
    M=N0-1-(b-1)ell,
    T=M+(B-2)B^H N0,
    J=2(1+g)^4D(B)+sum_(i=0)^(H+4W) B^(i+1),
    S=g+JN0,
    R=(S+T+1)N+T+1,
    X=(N-1)R, Y=N^2.

Every sum and exponent is fixed. These expressions are polynomials in f,g
with fixed integer coefficients. The index source constant is unchanged;
only monomial exponents and the resulting masks and block lengths change.

The existing coefficient certificate implies

    beta_S > 48*33^4*L.

For f!=0 and b a square, b=1 mod3 implies b>=4 and f>0. Thus B>2b and
the bound in Section 2 follows. For arbitrary 0<=g<2cap, not just correctly
encoded g, we have g+1<=2bB^W. Write A=48L(2b)^4. The displayed beta_S
bound gives A<B-2. From 0<D(B)<=24L sum_(j=0)^H B^j, therefore,

    0<J
      <= A B^(4W) sum_(j=0)^H B^j
         + B sum_(j=0)^(H+4W) B^j
      < 2 B^(H+4W+1) < N1.

This proves the required bounds BEFORE assuming that the mask accepts.
Also 0<=g<N0, 0<=M<N0, 0<=T<N, and 0<=S<N. The first two facts use
2b<=B and the literal mask digits B-b at w_i, B-1 elsewhere. The bound
on T follows from H+1<=H+4W+1 and the factor4 in N1.

When b is a power of two, B,N0,N1,N are powers of two. Binary block
separation, together with the mask lemma, now gives

    S AND T =0
      iff g AND M=0 and J AND ((B-2)B^H)=0
      iff there exist z_i in [0,b) with
           g=sum_i z_i B^w_i and P(z)=0.

The first equivalence uses canonical low blocks g,M<N0 and N0 a power
of two. The standard carry/binomial identity gives

    S AND T=0 iff Y divides binomial(2X,X).

This last identity applies to arbitrary S,T in [0,N) and any power-of-two
N, with the displayed R and X. It has no monomial-exponent hypothesis.

## 4. Completeness, converse, and bridge size promises

Given a nonnegative zero z of P, choose b=2^(2r) arbitrarily large, so
b=1 mod3 and b exceeds all z_i. Set f=(b-1)/3 and
g=sum_i z_i B^w_i. Since P(0)>0, some z_i>0. Every w_i>=1, whence
g>=B>=b. The standard digit bound gives g<bB^W=cap. Thus all forward
source-code promises hold, including the arbitrarily-large f promise.

Conversely, if f!=0, b is both a square and a power of two,
0<=g<2cap, and the displayed binomial divisibility holds, the preceding
mask and coefficient-isolation argument recovers a genuine nonnegative
zero of P. No new existential coefficient or witness has been introduced.

The bridge also requires 3|X and size bounds even before b is known to be
a power of two. The exponent4269882 is even, so beta_S=1 mod3; b=1 mod3
then gives B=1 mod3 and N=4B^(H+5W+2)=1 mod3. Therefore 3|X.
Furthermore S,T>=0 gives R>=N+1>B>=b, so X>3b. Finally Y=N^2>max(b,256).
The cap remains exactly of the required form

    cap=2^(4269882 W) b^(4W+1),

whose exponent of2 is even. All old bridge statements apply with this
new pair of fixed positive exponents. With H=4W, N=4B^(9W+2).

## 5. Audit conclusion and source dependence

There is no remaining use of positional radix-five uniqueness. It is
replaced exactly by the finite B4 certificate. The target coefficient,
off-central carry bound, positivity of D, arbitrary-g bounds, low/high
mask split, forward cofinality, and bridge size/congruence promises have
all been re-established above. The modified source encoding therefore
has the same existence predicate as the literal shifted quartic.

Primary source checks:

* Sun, Further results on Hilbert's Tenth Problem,
  arXiv:1704.03504v7, Lemma2.2 (binomial/carry conversion), Lemma2.4
  (arbitrary increasing mask positions), Lemma2.6 (coefficient isolation),
  and proof of Theorem3.1 (block sizes and bridge promises).
* Bayer--David--Hassler--Matiyasevich--Schleicher,
  arXiv:2506.20909v3, Definition1.5 and Lemma1.6, independently state the
  mask lemma for arbitrary strictly increasing positions. The argument
  here does not require importing any new conclusion of that paper.

The classical Bose--Chowla construction explains the origin of the B4
weights. The exhaustive check of the literal 52,360 four-element
multisets suffices to verify the specific weights independently of all
finite-field implementation choices. Finite enumeration supports the
specific numerical lemma; the generic proof above supplies the unbounded
arithmetic implication.
