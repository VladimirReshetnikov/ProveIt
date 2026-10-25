# Reciprocal pooling of distinct-base Pell certificates

Theorem developed in this iteration, 25 October 2026. The proof below is
complete ordinary arithmetic and has received the separate AI-assisted review
recorded in `RECIPROCAL_POOLING_INDEPENDENT_REVIEW.md`. No claim
of literature-wide novelty is made. The arithmetic parent is package 158's
literal P225 over unrestricted integers, pinned to repository commit
953fb4d82d4229f4efc5f9db4cc2bf38ae329bb4.

## Exact theorem for the two consecutive bases

Let W be an integer with W>=258, let A be an integer with |A|>W^W, and put
b=floor(sqrt(W-1)), so b>=16. Let the two bases n_0=q and n_1=q+1 be nonzero.
For each request i in either of two blocks I_j, let m_i,k_i be integers and
let X_i,Y_i be canonical signed Pell coordinates at parameter A and signed
index k_i. Assume n_j^2,m_i^2,k_i^2<W, and let the total number of requests
r=|I_0|+|I_1| be at most 15 (the parent has 3+11=14).

Set T_j=2*A*n_j-n_j^2-1. The T_j are nonzero. Since q,q+1 are nonzero
consecutive integers, their signs agree. Moreover
|T_j| >= 2|A|-W > W^W, and sign(T_j)=sign(A*n_j), so T_0,T_1 have the
same sign.

Put Z_i=A*Y_i, D_i=m_i-X_i+Z_i,

    H_j = sum_{i in I_j} Y_i*(m_i-X_i),
    S_j = sum_{i in I_j} (D_i^2-Y_i^2),
    E_j = S_j-2*n_j*H_j.

These are polynomials (H_j,S_j quadratic, E_j at most cubic). Then all
the exact powers m_i=n_j^{k_i} hold, with k_i>=0 whenever |n_j|>=2,
if and only if there is an integer z such that

    E_0*T_1 + E_1*T_0 - z*T_0*T_1 = 0.             (RP)

For unit bases the output means the canonical signed-index unit power;
no nonnegativity conclusion for those indices is asserted.

## Proof of the nontrivial direction

For each i in block j define delta_i=D_i-n_j*Y_i. The exact polynomial
identity established in the parent is

    sum delta_i^2 = E_j-T_j*sum Y_i^2.

Thus (RP) says that the rational number

    sum_{j=0,1} sum_{i in I_j} delta_i^2/T_j

is an integer. No coprimality assumption on T_0,T_1 is involved.

Let C=[q(q+1)]^b, a nonzero integer. Since |k_i|<=b, define the integer

    d_i = C*m_i - (C/n_j^b)*n_j^(b+k_i).

Both exponents are nonnegative and C/n_j^b is an integer. The canonical
Pell congruence is

    X_i+(n_j-A)*Y_i == n_j^{k_i}  (mod T_j),

where negative exponents are meaningful since T_j=-1 mod n_j. Multiplying
by C gives C*delta_i == d_i mod T_j. Therefore

    sum d_i^2/T_j

differs by an integer from C^2*sum delta_i^2/T_j and is itself an integer.

Each |n_j|,|m_i|,|k_i|<=b. We have |C|<=b^(2b),
|C/n_j^b|<=b^b, and |n_j^(b+k_i)|<=b^(2b). Consequently

    |d_i| <= b^(2b+1)+b^(3b) <= 2*b^(3b),
    sum d_i^2 <= 4*r*b^(6b) < W^(3b+1) <= W^W.

The strict inequality uses 4r<=60<W and b^2<W. The last inequality uses
3b+1<=b^2+1<=W, true for b>=3. Since each |T_j|>W^W,

    |sum d_i^2/T_j| <= (sum d_i^2)/min(|T_0|,|T_1|) < 1.

All summands have the same sign, because T_0,T_1 have the same sign. The
integer sum must be zero, and every d_i must be zero. Cancellation cannot
occur. Dividing in Q by C gives m_i=n_j^{k_i}. When |n_j|>=2 a negative
k_i would imply m_i*n_j^{-k_i}=1, which is impossible in integers.

## Converse

True powers and canonical Pell congruences give T_j|delta_i for every i,
also for unit bases with negative indices. The displayed identity implies
T_j|E_j. Thus z=E_0/T_0+E_1/T_1 is integral and satisfies (RP).

## Application to P225 and bootstrap order

Retain the first three singleton requests: (F^2+1)^t=V, B^x=N,
(BH)^x=q. The unchanged normalized remainder norm and rounded-factorial
rows prove B!=0, |B|>=2, |F|<|B| and V<|B|^2 before interpretation of
the q and q+1 blocks. H is odd and nonzero. The retained B and BH singleton
requests then imply x>=0 and q=(BH)^x, hence q!=0 and q!=-1. Therefore
q+1!=0, and the reciprocal-pooling theorem applies even if q=1 (the x=0
case) or q+1=-1. It recovers every request formerly recovered by the two
separate same-base pools. The unchanged equation B*d=M and |B|>=2 then
excludes x=0 through M=q^x=1. The rest of the parent's bootstrap is unchanged.

## Polynomial cost and exact transformations

The two old pools have four private integer coordinates K_0,L_0,K_1,L_1
and four quadratic rows:

    K_j-2H_j-(2A-n_j)L_j=0,
    S_j-n_j*K_j+L_j=0.

Replace these four rows and four coordinates by (RP) and z. The residual
(RP) has degree at most five, and its square has degree at most ten.
Together with all other unchanged quadratic residual squares this gives
a literal polynomial in 222 integers, provided the parent coordinate
and row membership checks confirm that the removed coordinates are private.

For forward zero-existence, old witnesses give z=L_0+L_1. For reverse
zero-existence, the theorem gives T_j|E_j, so restore L_j=E_j/T_j and
K_j=2H_j+(2A-n_j)L_j. This restoration is integral on the solution set;
it is not a global polynomial coordinate bijection. The exact sets of
remaining witnesses are equivalent after existentially quantifying the
private coordinates.

The delivered construction first applies seven exact integral projections
to obtain the 218-variable quartic. A protected change of residual basis
preserves the four private pool rows and coordinates. Applying the theorem
to that literal system gives the delivered 215-variable degree-ten companion.
The independent finite checker verifies the projections, the protection,
and every coefficient of the resulting polynomial. See `PROJECTION_PROOF.md`,
`STAGES_AND_REPRODUCTION.md`, and the final report for the complete pipeline.

## Scope and generalization

This works because rational integrality plus a common sign and a strict
height bound can replace many separate divisibility conditions. The
moduli need not be coprime, and no modulus coordinate is needed.
For more bases, oriented weights n_j make n_j/T_j have common sign,
and a common product of base powers clears negative indices. The same
argument applies with an appropriately checked size budget; no such
multi-base compiler is claimed here.
