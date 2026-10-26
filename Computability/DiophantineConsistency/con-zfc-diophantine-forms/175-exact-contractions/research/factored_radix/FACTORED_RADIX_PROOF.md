# Eliminate the self-radix coordinate with an anisotropic frame

This exploratory companion retains the final, unscaled-frame version.
It is not an improved point on the release's variable/degree frontier.
The literal final source uses W=2 plus 35 explicit squares and no new
frame variable; superseded experiments are omitted from this release.

## Completed mathematical change

Factor the semantic identity q=(BH)^x as

    N=B^x,        P=H^x,        q=N*P,

where H=1+2*sum_i a_i is the existing affine odd majorant. Retain N,
reuse the old q coordinate as P, and eliminate both the old independent
q coordinate and the BH multiplication coordinate. This replaces three
coordinates N,q,BH by two coordinates N,P. Every occurrence of q is
replaced by N*P; every occurrence of the stored old q+1 is replaced by
N*P+1. The former BH power modulus and quotient are reused for H.

After this change, both the B and H requests still have their original
single-request form. Their modulus coordinates can subsequently be
eliminated while keeping every residual of degree at most three.

The exact changed source in `factored_radix224/equation.json` has 224
unrestricted integer variables, 161 residuals, and exact total degree
six after summing their squares. Its literal expansion has 9,936 terms
and height 128,846. These are source-stage metrics, before the additional
exact projections recorded in `factored_radical219/`.

## Literal replacement formulas

Let (X,Y) be the principal signed Pell pair at index x and parameter A,
and let D=X-A*Y be the existing difference coordinate. Keep

    T_B=2*A*B-B^2-1,
    N=D+B*Y-T_B*u_B.

Replace the former BH request by

    T_H=2*A*H-H^2-1,
    P=D+H*Y-T_H*u_H.                                  (1)

There is no separate q=N*P residual; q is now a quadratic abbreviation
substituted into all the other literal rows. H is affine and is also
substituted, so it requires no coordinate. The BH defining row is deleted.

In the source P225 coordinate system, the actual A is `shared.A+1`,
the actual old q is `pow2.output-1`, and

    H = -1 + 2*(crt.encoded.a + crt.encoded.b + crt.encoded.c
                + crt.encoded.d + crt.encoded.S + crt.encoded.Sp
                + crt.encoded.u + crt.encoded.vq
                + crt.encoded_index_minus_one).

The independent checker verifies that this is exactly the affine factor in the
old BH definition before making any change. The old `pow2.output`
coordinate is renamed `self_radix.powerH` and denotes P in the new
equation.

## The new frame and its exact bounds

Start from the old list of 36 actual semantic atoms. Delete its three
entries q, q+1, BH and insert P,H. Keep every other entry, including N,
t, t+1, x, every other power output, and every requested Pell index.
Set

    W=2+sum_(a in the resulting 35-entry list) a^2.      (2)

All entries in this list are affine expressions in semantic front
coordinates. There is no private Pell ordinate, modulus, or power
quotient in (2). In particular the frame is still quadratic and is
computed before A is chosen in completeness.

Every requested index k and proposed output m has

    k^2 < W,             m^2 < W.                      (3)

The initial bases F^2+1, B and H also have their squares below W.
The two remaining bases satisfy the weaker, sufficient bounds

    |q|=|NP| <= (N^2+P^2)/2 <= (W-2)/2 < W,
    |q+1| <= |q|+1 <= W/2 < W.                         (4)

The frame contains t^2, and the unchanged cofinal-horizon row gives
t=16+h_0^2. Hence W>=258. No positivity of N or P is assumed in (4).

## Canonical Pell indices do not need the old base-square bounds

The signed frame equation is unchanged:

    A^2-W^3*(W+2)*(2z+1)^2=1.

Its classification argument gives |A|>W^W and |A-1|>4W^3 for W>=258.
It uses W and the odd multiplier, not the individual frame atoms.

The retained squared cap and indexed anchor first bound all classified
principal indices by |h|<W. The orientation-first argument then compares
the residues of both principal coordinates modulo A-1. Its error budget
uses only the number of pairs, the bound on these classified indices,
and the bounds |k|<W on the requested indices. All those index squares
remain in (2). Neither q nor BH was a requested index, and changing the
self-radix output from q to P does not change the requested index x.

Consequently all principal pairs are still canonical signed pairs before
interpreting any exact power. No old assertion that every base square
lies below W is being silently reused.

## Generalized block lemma: bases may have absolute value below W

Let W>=258 and |A|>W^W, and put b=floor(sqrt(W-1)). Suppose a block
has at most fifteen requests at a nonzero integer base n satisfying
|n|<W. Each requested index and proposed output has its square below W,
and all Pell pairs are canonical signed pairs. Retain the same two
polynomial block rows as the parent. They imply

    T divides sum_i delta_i^2,
    T=2*A*n-n^2-1,
    delta_i=m_i-X_i+(A-n)*Y_i.

Since gcd(n,T)=1, multiplication by n^b clears every possible negative
index and shows that T divides the nonnegative integer

    E = sum_i [m_i*n^b - n^(b+k_i)]^2.                 (5)

Here |m_i|,|k_i|<=b. As |n|<W and b>=16,

    |m_i*n^b - n^(b+k_i)| <= b*W^b + W^(2b)
                              <= 2*W^(2b).

Therefore

    0<=E<=60*W^(4b)<W^(4b+1)<=W^W.                    (6)

The strict comparison uses 60<W. The last comparison uses
4b+1<=b^2+1<=W, since b>=16. Meanwhile

    |T| >= 2*|A|-(W-1)^2-1 > W^W.                    (7)

For (7), |A|>W^W and W^W>(W-1)^2+1 suffice. Thus E=0. Every request
is an exact power. A negative index at |n|>=2 would imply the impossible
integer identity m_i*n^(-k_i)=1; unit bases retain their signed-index
values. The converse follows from the same canonical congruences and
is unchanged.

The difference from the parent is precise: the old proof bounded all
three quantities n,m,k by b, whereas this proof bounds n by W and
the other two by b. The larger error budget is still strictly below
the same existing modulus. No polynomial row, additional witness or
larger frame constant is required.

## Soundness and the sign-recovery order

The retained normalized-remainder norm gives M != 0. The retained
identity B*v_B=M gives B != 0. Since H is odd, H != 0. The initial
request at F^2+1 and t>=16 is unchanged and supplies
V=(F^2+1)^t>=1. The unchanged rounded-factorial bound

    |FB-V|<|B|/2

then proves |B|>=2, |F|<|B|, and V<|B|^2 exactly as in the parent.

The B request now gives x>=0 and N=B^x. The H request (1) gives
P=H^x, including H=1 or H=-1. Both requests satisfy the original
stronger square-frame bounds, because their actual bases, indices
and outputs are explicit atoms in (2). Therefore

    q:=N*P = B^x*H^x = (BH)^x,

so q is nonzero. Apply the generalized block lemma above to the q
block, using (3) and (4). If x=0 then N=P=q=1 and that block gives
M=q^x=1, contradicting B*v_B=M and |B|>=2. Hence x>=1 and |q|>=2.
The retained q^t normalization ratio gives x>=t, thus |q|>=2^16.
In particular |q+1|>=2. The generalized lemma applies to the q+1
block and recovers all remaining exact powers and nonnegative
representatives. All subsequent factorial, digit, CRT and Horn-flow
arguments are unchanged in semantic content.

The source change has therefore produced a finite C222 refutation from
every integer zero. This is an acyclic derivation: canonical indices
precede powers, the half-width factorial bound precedes |B|>=2,
the independent B,H requests precede q's nonvanishing, and the q
block precedes the large-radix conclusion used for q+1.

## Completeness

From a finite C222 refutation choose the parent's cofinal horizon,
factorial, beta-CRT code, and positive semantic representatives.
Construct B,H,x,N=B^x and P=H^x, and use q=N*P=(BH)^x everywhere
the old arithmetic proof used q. These are exactly the same positive
semantic front values, with an additional factored representation.

Compute W from (2). It depends exclusively on already chosen semantic
data. Choose A and the canonical signed-Pell witnesses only afterward
by the retained odd-frame and dominant-anchor construction. The requested
indices are unchanged, so the earlier cofinal choice making h dominate
them remains valid. The canonical H congruence supplies an integer u_H
for (1); all other unchanged quotient and normalized-remainder witnesses
are constructed as before. This fills every literal row of the new
equation.

Both directions therefore give, in ZFC,

    new polynomial has an integer zero
       iff there is a finite C222 refutation
       iff there is a finite ZFC refutation.

Negating gives the requested equivalence with Con(ZFC). The second
equivalence is the named inherited C222/ZF calibration followed by
constructible-model Choice transport. It uses ordinary set-model
arguments formalizable in ZFC, not merely finite polynomial arithmetic.

## Exact further projections and evidence boundaries

`replay_factored_radical.py` rechecks the five inherited common-radical
directions against the actual changed source. Each pivot is a unit,
occurs only linearly after its integral shear, and has the recorded
integer polynomial restoration. Every resulting residual remains of
degree at most three. The inherited reversible row operations are
also replayed on the changed residual list, using the current indices
stored in `factored_radical219/certificate.json`. The checker explicitly
reverses both kinds of shear and compares every endpoint coefficient and
all endpoint metadata with `factored_radical219/equation.json`. This gives
the literal 219-variable intermediate.
Any additional monic contraction must be independently checked against
that intermediate, rather than inferred from a different source's count.

The unbounded proof does not rely on an observed finite test. Conversely,
finite coefficient and substitution checks do not establish the whole
arithmetical or logical calibration. No fresh full Lean/Rocq build or
encoded object-language ZFC derivation is claimed. The existence claim
does not assert that the polynomial actually has, or lacks, integer zeros.
