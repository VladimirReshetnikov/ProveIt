# Direct quadratic-system source coding: independent proof

This note verifies a proposed replacement for the source-coding portion of
package 31's ten-integer equation. The downstream Sun Lucas/binomial bridge
is unchanged. It is a mathematical proof of the source adapter, not a new
formal certificate for that bridge or for the inherited K215 compiler.

## General data

Let r_1,...,r_m be fixed integer polynomials of degree at most two in n
nonnegative integer variables. Assume their common zero set omits the origin.
Reorder and, if necessary, negate one residual so that the constant term of
the last residual is a positive integer. Neither operation changes the zero
set. In the ProveIt instance n=31,m=22, the fifth residual, after the positive
shift, has constant +1 and can be put last without negation.

Choose 0=a_0<a_1<...<a_n=M so that all unordered pair sums a_i+a_j
(including i=j) are distinct. Put d=2M+1,

    e_j=2M+(j-1)d   (1<=j<=m),
    K=2M+md-1=e_m+2M.

For multi-indices alpha with |alpha|<=2 put

    c_(j,alpha)=(2-|alpha|)! product_i(alpha_i!) [n^alpha]r_j,
    e(alpha)=sum_i alpha_i a_i.

These are fixed integers; zero coefficients are omitted. Let A be their
maximum absolute value. Select a fixed square power of two
beta>4(n+1)^2 A and beta>36A; beta>4096A suffices for n=31.
The concrete release uses beta=2^2134940 and verifies beta>8192A.
All facts below are uniform in b.

## Explicit polynomials

For the outer source parameters f,g set

    b=1+3f, B=beta*b^2,
    ell=sum_(i=1)^n B^(a_i),
    D=sum_(j,alpha) c_(j,alpha) B^(e_j-e(alpha)),
    N0=B^(M+1), N1=4 B^(K+1), N=N0*N1,
    Mlow=N0-1-(b-1)ell,
    Thigh=sum_(j=1)^m (B-2)B^(e_j),
    T=Mlow+N0*Thigh,
    J=2(1+g)^2 D+sum_(i=0)^K B^(i+1),
    S=g+N0*J,
    R=(S+T+1)N+T+1,
    X=(N-1)R, Y=N^2, Ccap=b B^M.

All exponents are fixed nonnegative integers; e_j-e(alpha)>=0. Geometric
sums and powers admit finite division-free straight-line circuits.

## Lemma 1: positivity and size before digit recovery

Suppose b>=2 and 0<=g<2Ccap. Then B>2b and g<N0. The largest exponent
in D is e_m, whose coefficient is the positive integer 2r_m(0)>=2.
Every other exponent is strictly smaller, by pair-sum uniqueness and the
separation of the reversed blocks. Those reversed blocks are disjoint,
and within each block every coefficient exponent is distinct. Thus every
coefficient of D has absolute value at most A, and

    D >= 2B^e_m - A sum_(i=0)^(e_m-1) B^i > 0,
    D <= A sum_(i=0)^e_m B^i < 2A B^e_m.

The lower bound uses B>A+1. The upper estimate remains valid when the
leading coefficient exceeds two.
Also 1+g<3b B^M. Thus

    0<2(1+g)^2D<36A b^2 B^K<B^(K+1).

The geometric padding is less than 2B^(K+1), so 0<J<3B^(K+1)<N1.
Consequently 0<S<N. Every digit of Mlow is B-1 except at the a_i,
where it is B-b, so 0<=Mlow<N0. Likewise 0<=Thigh<B^(K+1), whence
0<T<N. In particular all these inequalities hold without having first
decoded g or assumed any residual vanishes. This is the needed noncircular
size check for the reverse bridge.

## Lemma 2: binomial divisibility is exactly no binary carry

Write N=2^u and 0<=S,T<N. The above X has the exact identity

    X=(S+T)N^2+(N-1-S)N+(N-1-T).

Its three nonnegative summands occupy disjoint binary blocks (the high
block may extend above bit 3u). Hence

    popcount(X)=2u+popcount(S+T)-popcount(S)-popcount(T).

Legendre's factorial valuation identity gives
v_2(binomial(2X,X))=popcount(X). Binary addition cannot increase popcount
above the sum of the input popcounts; equality holds precisely when
S&T=0. Therefore Y=N^2 divides binomial(2X,X) if and only if S and T
add without binary carries. This proof does not require S+T<N.

## Lemma 3: low digits recover the bounded source tuple

Assume b and B are powers of two and 0<=g<2Ccap. In the low N0 block,
the no-carry condition is g&Mlow=0. At positions different from a_i the
mask digit B-1 forces digit zero. At a_i, the mask B-b has precisely its
lowest log_2(b) bits zero, so the corresponding digit lies in [0,b).
Thus the condition is equivalent to

    g=sum_i n_i B^(a_i),  0<=n_i<b.

Conversely every tuple of this form has g<Ccap. Indeed the largest
position is M, and
(b-1)sum_i B^(a_i)<(b-1)B^M B/(B-1)<bB^M.

## Lemma 4: each marked high digit tests one signed residual

After low-digit recovery, expand

    (1+g)^2 D=sum_(i=0)^K theta_i B^i

as a formal polynomial in B, keeping the decoded n_i as coefficients.
At a marked centre e_j, no other block contributes: every contribution
from block k lies in [e_k-2M,e_k+2M], while distinct marked centres are
separated by at least 2M+1. Product blocks can overlap away from the
marked centres, which causes no difficulty for the convolution bound.
The pair-sum property (padding degree-zero and degree-one terms by a_0=0) implies

    theta_(e_j)=2r_j(n_1,...,n_n).

The factorial coefficient is essential: multinomial coefficients in
(1+g)^2 cancel it to give the common factor 2.

Every coefficient of D has absolute value at most A. Convolution with
the nonnegative-coefficient polynomial (1+g)^2 therefore gives

    |theta_i|<=A (1+sum n_i)^2<=A n^2 b^2,
    |2theta_i|<B/2.

The integer J is represented by the nominal base-B coefficients
B+2theta_i at i=0,...,K. Starting with incoming carry zero, all carries
are 0 or 1 because these coefficients lie strictly between B/2 and
3B/2. Therefore the actual digit at position i is

    (2theta_i+epsilon_i) mod B, epsilon_i in {0,1}.

Since B is a power of two, adding the digit B-2 creates no binary carry
exactly when the other digit is 0 or 1. Under |2theta_i|<B/2 this happens
if and only if theta_i=0. Indeed theta_i>=1 produces a digit at least 2
and less than B, while theta_i<=-1 produces a digit between B/2 and B-1.
Thus the high no-carry condition J&Thigh=0 is equivalent to all m
residuals being zero. Negative residual values are fully covered; no
positivity or sum-of-squares assumption on individual residuals is used.

## Source theorem and bridge interface

For b a power of two and b>=2, with 0<=g<2Ccap,

    Y divides binomial(2X,X)

is equivalent to the bounded nonnegative system r_j(n)=0 being decoded
from g. Given any nonnegative common zero, take arbitrarily large b=4^t
above all its coordinates and set f=(b-1)/3. The decoded g is nonzero
because the origin is not a common zero. Since all a_i>=1, g>=B>b.
Thus b<=g<Ccap, exactly the positive source interval needed by package
31's downstream bridge. Also X>3b and Y>max(b,256) follow from the
huge fixed beta and N>=4B^2. The cap has the prescribed fixed-power form

    Ccap=beta^M b^(2M+1).

If b is a square and f!=0, b=1+3f implies b>=4. The reverse Lucas bridge
supplies the required additional fact that b is a power of two; that is
an inherited Sun dependency, not inferred merely from b being a square.
Since beta is a square power of two and b is a power of two, B is a
power of four. Consequently N=4B^(M+K+2)=1 modulo 3, and 3 divides X.
This additional source normalization is used by the inherited Lucas bridge.

## Concrete independently checked B2 list

The following 32-element list, obtained from the Bose--Chowla construction
over GF(1024), then multiplied by a unit and translated modulo 1023, has 528 distinct pair sums modulo 1023:

    0,10,35,55,62,105,144,145,159,168,232,245,306,323,325,353,
    371,374,382,494,499,525,566,578,610,647,681,685,741,777,783,799.

For reproducibility, use GF(2)[x]/(x^10+x^3+1) with theta=x and take
the exponents i for which (theta^i+theta)^32=theta^i+theta. The nonzero
theta powers exhaust all 1023 nonzero field elements. Rotate that set
to minimize (diameter,sum,list) lexicographically; this gives the
901-diameter intermediate list. Apply a ->47a-342 modulo 1023 and sort
to obtain the displayed list. Since gcd(47,1023)=1, this preserves all
modular pair-sum inequalities. The accompanying checker independently
reconstructs this procedure and verifies all 528 final pair sums.
The modular check alone certifies the required integer pair-sum property.
It has M=799. For m=22, d=1599, e_m=35177, K=36775,
and N=4B^37576. (The coefficient of 4 in N is literal.)

## Limits and attribution

The pair-sum construction is classical Bose--Chowla additive coding;
the novelty here is applying bounded-degree additive coding directly to
all quadratic residuals, with separated target digits, within the fixed
Sun source bridge. The elementary high-digit argument above replaces the
single sum-of-squares target. No smaller universal unknown-count theorem
is claimed. The final ten-integer equation still depends on the same
external Sun theorems and inherited K215/compiler calibration.
