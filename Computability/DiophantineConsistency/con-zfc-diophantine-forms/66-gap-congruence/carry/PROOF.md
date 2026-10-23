# Reflected degree-separated extraction with independently positive kernels

## Status and source boundary

The source coordinate changes are proved in `../source/GAP_SOURCE_PROOF.md`. This packet supplies exact finite
positional certificates and the local unbounded positivity/bounds argument.
It does not prove the inherited refutation compiler or numerical Pell
representation theorems. Finite checks establish polynomial identities and
finite isolation, not consistency and not an end-to-end kernel proof.

The primary reflected certificate `gapNmirror116_H2057_code.json` uses the
86-record gapN source, whose exact hash is stored in the certificate. It
reflects the original 116 labels by w_i ->117-w_i and reverses the sign of
row 2. A sign reversal does not change a common zero set. All 31 positions
remain distinct positive integers, with maximum W=116.

Let rho_j be the gapN residuals after the indicated row signs. For a witness
monomial x^alpha of degree d<=2, put e(alpha)=sum_i alpha_i w_i. The coefficient
of x^alpha in rho_j is a_(j,alpha). Define the weight

 c_(j,alpha)=2a_(j,alpha) for d=0,1 or a diagonal square;
 c_(j,alpha)=a_(j,alpha) for a quadratic cross term.

The three reversed kernels are

 D_d(T)=sum_(j,|alpha|=d) c_(j,alpha) T^(q_j-e(alpha)).

For U(T,x)=sum_i x_i T^w_i, put

 G(T,x)=D_2(T)U(T,x)^2+D_1(T)U(T,x)+D_0(T).

The finite certificate verifies every reversed exponent is nonnegative and
checks all 22,481 record/monomial interactions against all 22 target positions.
It proves that a degree-d source record contributes to target q_k only when
k=j and its witness monomial is alpha. The quadratic cross multiplicity 2
and the displayed weighting therefore give the formal polynomial identities

 [T^q_j]G(T,x)=2rho_j(x), for j=1,...,22.

The checker reconstructs each side as a sparse polynomial in all 31 witnesses
and four independent coefficient ports; it does not evaluate the identities
only on a bounded set. No cross-degree separation is required, since kernels
multiply different homogeneous powers.

## 1. Numerical data and simpler positivity

For the reflected certificate:

 W=116, Q=max q_j=2031;
 deg D_0=1935, deg D_1=1941, deg D_2=1825;
 H=max_d(deg D_d+dW)=2057.

The leading coefficients of D_0,D_1,D_2 are respectively 2K0, 2, beta. All
are positive integers for either coherent native coefficient tuple. A uniform
integer M strictly greater than every absolute kernel coefficient therefore
has the following elementary consequence for B>M+1: a kernel of degree d
and positive leading coefficient is greater than

 B^d-M(B^d-1)/(B-1)>0.

Thus D_0(B),D_1(B),D_2(B)>0 separately. In particular G(B,U)>0 for every
real U>=0, with no need to recover digits, bound g, or compare the quadratic
and linear leading degrees. This avoids the earlier strict layer-gap proof.

For the coherent original31 tuple, the inherited conservative choice
M=2^2134927 and B=2^2134939 b^2 is sufficient. The equation-composition
builder must recheck the coefficient bound for the exact bound tuple it
actually uses; no port is mixed between tuples. Changing a sign does not
alter an absolute coefficient bound.

The quadratic and linear leading degrees TIE after substituting the positive
word U=ell+g, ell=sum_i B^w_i: both have leading B-height2057. Consequently
the leading coefficient of G in B is beta+2, not beta. Its positivity prevents
cancellation; exact final equation degree certificates must retain this tie.

## 2. Uniform bounds for carry adapters

Let b>=1, g>=0, ell=sum_i B^w_i and U=ell+g. Distinct positive weights give
ell<2B^W. On a branch g<cbB^W, where c is any fixed positive integer,
U<(c+2)bB^W. Since a polynomial with coefficients bounded by M has absolute
value less than 2M B^d for B>=2, one has

 0<G(B,U)<2M[1+(c+2)b+(c+2)^2 b^2] B^H.

For c=4 and b>=1 this is at most86 M b^2 B^H. In particular, for
B=4096 M b^2, 2G/B^(H+1)<172/4096<1/16. This conservative estimate suffices
for the source block range; one must not silently assert a smaller 1/32
bound from this loose estimate. A sharper geometric-series estimate gives
G<43 M b^2 B^(H+1)/(B-1), hence 2G/B^(H+1)<86 M b^2/(B-1)<1/32 for B>=4.

Let A=sum_j B^q_j and Z=B^(H+1). The maximum target gap H-Q=26 gives
A<2B^Q<Z/64 and (B-2)A<2B^(Q+1)<Z/64. Set

 N0=B^(W+1), Mask=N0-1-(b-1)ell,
 Jcode=2G+A, S=g+N0 Jcode, T=Mask+N0(B-2)A.

The low block g is less than N0 under g<4bB^W and the stated huge base.
Together with 0<=Mask<N0, these estimates imply S+T<N0 Z. This is the precise
range required by the standard two-block population-count calibration.

When the low bit mask recovers g=sum_i n_iB^w_i, 0<=n_i<b, U codes positive
coordinates x_i=n_i+1. Each coefficient of G is bounded in absolute value by
M[(sum x_i)^2+sum x_i+1]<=993 M b^2<B/4. Consequently the sparse +1 signed-
borrow test from the inherited source proof applies unchanged to Jcode.
All targets are below the final high-word boundary; there is no reliance on
bits of negative numbers.

Every sufficiently large admissible base encodes any fixed positive source
zero. The all-one tuple is not a zero because row5 remains E*X+E-a*X=1.
Since every weight is positive, a zero's packed difference word is at least
B. This supplies g>=b where the integer finalizer requires it, and shows the
packed word is a multiple of B (hence of b^2) before any exact division by a
fixed divisor of the base scale is used by a later adapter.

## 3. Other frozen layouts

The packet also retains two unreflected layouts, useful for operation-count
tradeoffs:

- gapN116_H2068: 86 records, W116, Q2036, kernel degrees1571,1927,1836.
  The leading quadratic coefficient is1. Quadratic dominance gaps are25,497.
- gapNq116_H2082: 85 records, W116, Q2050, kernel degrees1627,1941,1850.
  The leading quadratic coefficient is1. Dominance gaps are25,455.

For these, D2(B)>B^d2/2, and the two lower-layer contributions relative to
B^d2 U^2 are bounded by2M/B^gap. With U>=B^W, B>=4096M and the stated positive
gaps, G>0 follows. Their interaction counts are22,481 and22,450 respectively.
The 85-record source is NOT compatible with the old incoming targets; only
the new certificate here repairs its extra Js collision.

Search logs and binaries are optional discovery provenance, never proof
premises. The read-only checker needs only the frozen certificate, kernel,
and source JSON. No global minimality claim is made.
