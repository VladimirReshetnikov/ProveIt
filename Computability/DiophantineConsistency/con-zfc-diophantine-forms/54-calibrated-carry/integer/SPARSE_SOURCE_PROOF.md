# Source-parametric sparse padding and exact-mask popcount bridge

The sparse signed-borrow padding and exact-mask popcount idea are inherited
from the eighth incoming archive `ZFC_Diophantine_Selective_Quadratic_2026-10-23`,
reviewed at repository pin `4b4349064a750ba6347293b55874a7f92abdd0db`.
This note supplies a self-contained adaptation to interior padding, arbitrary
certified target schedules, the new selective twelve-coordinate shift,
and the coherent native tuple in `../native/COEFFICIENT_BINDING.json`.
It does not claim these two source mechanisms as newly discovered here.

## 1. Fixed finite source and extraction certificate

Use the source in `../source/selective12_source.json`. Its natural zero set
is bijective to the old positive source zero set by the elementary proof
in `../source/SELECTIVE_POSITIVITY_PROOF.md`. There are 31 coordinates and
22 quadratic residuals, 109 symbolic nonzero coefficient records. The
four ports are beta,K0,MC,MF, specialized together to the coherent native
tuple; MF is already MF_source and is not shifted again.

For a selected positional certificate, write p for the padding position,
w_i for the 31 distinct coordinate positions, and W=max(p,w_i). They are
nonnegative integers, and p differs from every w_i. Each row may be
multiplied by its specified sign +/-1 without changing its zero predicate.
Let r_j(n)=sum p_(j,alpha)n^alpha denote these sign-adjusted residuals, and
put

    c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) p_(j,alpha),
    e(alpha)=(2-|alpha|)p+sum_i alpha_i w_i,
    D(B)=sum_(j,alpha)c_(j,alpha) B^(H_j-e(alpha)),
    Z(B)=sum_j B^H_j,
    Dmax=max_(j,alpha)(H_j-e(alpha)), K=Dmax+2W.

The certificate proves all reverse exponents nonnegative and, for every
used source monomial alpha, every padded quadratic monomial gamma, and
all target indices k,

    H_j-e(alpha)+e(gamma)=H_k iff j=k and gamma=alpha.

It follows exactly, over the four symbolic native ports, that

    [B^H_j] (B^p+sum_i n_i B^w_i)^2 D(B)=2r_j(n).

The factorial coefficients cancel the quadratic multinomial denominators.
Support-local isolation is sufficient; no full Sidon property is asserted.
All supplied certificates additionally have distinct targets, positive
leading coefficient of D, and K>=max_j H_j+2. These conditions are checked
independently as finite arithmetic statements.

## 2. Literal source polynomials

Define the actual fixed integer

    C0=1+sum_(j,alpha)|c_(j,alpha)|.

Choose the least even e at least bit_length(8192C0), and set betaS=2^e.
Then betaS>8192C0 and betaS=1 modulo 3. Both betaS and every other fixed
coefficient leaf are materialized and hashed. Set, in the two integer
unknowns f,g,

    b=1+3f; B=betaS b^2; cap=bB^W;
    ell=sum_i B^w_i; N0=B^(W+1); N1=B^(K+1); N=N0 N1;
    mask=N0-1-(b-1)ell;
    Tcode=mask+N0(B-2)Z(B);
    Jcode=2(B^p+g)^2D(B)+Z(B);
    Scode=g+N0 Jcode;
    X=N^2+(Scode+Tcode)N+(N-1-Scode).

Let n=31, m=22 and Hpop=2W+K+3+m. Define

    Y=2^(e Hpop+1-m) b^(2 Hpop-n).

For a smaller live circuit, the exact division-free form used is

    Y=Yscale * B^(Hpop-16) * b,
    Yscale=2^(16e+1-m).

This is a fixed scalar power of two, not a variable exponent or an extra
unknown. All exponents are explicitly nonnegative. The cap is precisely
`2^(eW)b^(2W+1)`, the required positive monomial form.

## 3. Size and congruences before power-of-two recovery

Suppose f!=0, b is a square, and 0<=g<2cap. As b=1 modulo 3, these imply
b>=4 and f>0. In particular B>8192C0 b^2, B>=16, and B>2b.
Since D has a positive integer leading coefficient and all its coefficient
absolute values sum to less than C0, the leading term dominates its lower
terms at B>C0; therefore D(B)>0. Also `|D(B)|<C0 B^Dmax`.

Because p<=W and g<2bB^W,

    B^p+g <3bB^W,
    0<2(B^p+g)^2D(B)<18C0 b^2 B^K<N1/256.

Here 18/8192<1/256. Distinct targets and max(H)<=K-2 give

    0<Z(B)<2B^(K-2),
    0<(B-2)Z(B)<B^(K-1).

It follows that Jcode<N1/4. Also g<N0 and 0<=mask<N0, since the latter
has base-B digits B-b at the coordinate positions and B-1 elsewhere.
As N1>=16,

    Scode<N/4+N0<=5N/16,
    Tcode<N0+N0B^(K-1)<=2N/B^2<=N/128.

Hence Scode,Tcode are nonnegative and Scode+Tcode<N. In particular,
N-1-Scode>=0 and X>=N^2>3b. The explicit formula also gives
Y>max(b,256). These bounds do not assume b is a power of two.

Finally b,B,N0,N are 1 modulo 3. Thus mask=0 modulo 3 and
Tcode=-22 modulo 3, whence

    X=1+Tcode=1-22=0 modulo 3.

This is the integer-only top-word-1 bridge. It must not be confused with
other calibrated source variants whose block contains an additional
factor 2 or whose top word is 10; their modulo-three checks differ.

## 4. Exact source decoding with signed borrows

Now also assume b is a power of two. B,N0,N1,N are then powers of two.
The binary no-overlap condition `g & mask=0`, with 0<=g<N0, is equivalent
to the unique representation

    g=sum_i n_i B^w_i, 0<=n_i<b.

Let h_t be the coefficient of B^t in
`(B^p+sum_i n_i B^w_i)^2 D(B)`. This polynomial has degree at most K, and

    |h_t|<=C0(1+sum_i n_i)^2<1024C0 b^2<B/8.

In particular |2h_t|<B/4, stronger than the |2h_t|<B/2 needed below.
If delta_t indicates the selected targets, the formal expansion is

    Jcode=sum_(t=0)^K (2h_t+delta_t) B^t.

It need not initially be a digit expansion. Normalize it by Euclidean
borrows: start epsilon_0=0, set

    epsilon_(t+1)=floor((2h_t+delta_t+epsilon_t)/B),
    d_t=2h_t+delta_t+epsilon_t-B epsilon_(t+1).

The stated bounds imply inductively epsilon_t is -1 or 0 and 0<=d_t<B.
At a target, the mask digit B-2 permits exactly the binary-disjoint digits
0 and 1. If h_t=0, its normalized digit is 1+epsilon_t in {0,1}. If
h_t>=1, the unnormalized digit is at least 2 and below B. If h_t<=-1,
it lies strictly between -B+1 and 0, so its normalized digit is at least
2. Therefore the target passes exactly when h_t=0, independent of the
incoming borrow. Positivity of Jcode has already been proved, so these
are the ordinary digits of a nonnegative integer.

The low/high block boundary is N0. Consequently

    Scode & Tcode=0 iff every r_j(n)=0.

Here low-digit no overlap recovers the tuple, and high-digit no overlap
imposes the 22 selected coefficient tests, using h_(H_j)=2r_j(n).

## 5. Calibrating the binomial threshold to the actual mask

Write N=2^u. Since Scode+Tcode<N, the three terms

    X=N^2+(Scode+Tcode)N+(N-1-Scode)

occupy disjoint binary blocks. The bottom block is the u-bit complement
of Scode, so

    popcount(X)=1+u+popcount(Scode+Tcode)-popcount(Scode)
               =1+u+popcount(Tcode)-c,

where c=popcount(Scode)+popcount(Tcode)-popcount(Scode+Tcode) is the
nonnegative number of carries counted with propagation. It is zero
exactly when Scode & Tcode=0. Legendre's factorial valuation identity
`v2(binomial(2X,X))=popcount(X)` therefore proves

    2^(1+u+popcount(Tcode)) | binomial(2X,X)
      iff Scode & Tcode=0.

Put b=2^k and B=2^v, so v=e+2k. The low mask contains W+1 base cells,
of which 31 have k low bits removed; the high mask has 22 cells, each
with v-1 set bits. Thus

    popcount(Tcode)=(W+1+22)v-31k-22,
    u=(W+K+2)v,
    1+u+popcount(Tcode)=Hpop v-31k+1-22.

This is exactly the exponent defining Y. Thus the reverse source
implication holds with precisely the displayed polynomial Y.

## 6. Forward source witnesses and inherited endpoint

Given a natural source zero, choose b=4^q larger than all its coordinates
and arbitrarily large, and put f=(b-1)/3. Encode g by its coordinate
digits. It satisfies g<cap. In the selective source, both unshifted
coordinates D and Delta are positive at every solution. Distinct positions
mean at least one of their two positions is positive, so g>=B>=b.
The exact digit argument gives no overlap and hence
Y divides binomial(2X,X). This proves the full source interface required
by the inherited Sun bridge.

Combining the source interface with `CONDITIONAL_SEPARATOR_PROOF.md`, the
unchanged intersective quintic merger, and the inherited Sun/native endpoint
therefore proves, in ordinary mathematics formalizable in ZFC and without
assuming consistency,

    exists ten unrestricted integers with F10=0 iff not Con(ZFC).

Classical negation gives the requested lack-of-solutions equivalence.
The finite artifact verifier certifies construction data, identities and
exact degree; it is not an end-to-end proof-assistant certificate.
