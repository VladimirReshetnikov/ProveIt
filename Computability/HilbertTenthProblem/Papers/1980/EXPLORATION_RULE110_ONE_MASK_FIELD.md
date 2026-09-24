# Why the two Rule110 auxiliaries do not fit one two-bit mask field

The proved 80-operation component uses the exact scalar relation

    2a-b-c+4y=2u+3v,                              (1)

with Boolean u,v. Its four allowed values are {0,2,3,5}. A natural
further proposal is to replace the two auxiliary planes by one
digit field whose only allowed bits are at two fixed binary
positions. Such a field has allowed values

    {0,2^i,2^j,2^i+2^j}.

The following result rules out every affine scalar projection of
that form, including arbitrary offsets and arbitrary real
coefficients. It does not rule out nonlinear projections, more
allowed bits, several relations, carry-based encodings, or other
changes of verifier architecture.

## 1. Exact classification theorem

Let 0<s<=t. There exist real constants alpha,beta,gamma,delta,epsilon
such that, for every Boolean a,b,c,y,

    y=b+c-bc(a+1)
        iff alpha*a+beta*b+gamma*c+delta*y+epsilon
            belongs to {0,s,t,s+t}                (2)

if and only if t/s=3/2.

In particular, choosing s=2^i,t=2^j with i<=j is impossible: their
ratio is an integer power of two, never 3/2. This obstruction is
stronger than a bounded coefficient search, but applies only to
the single affine membership predicate (2).

Sufficiency follows by dividing (1) by two and scaling by s:

    a-(b+c)/2+2y belongs to {0,1,3/2,5/2}

is exactly the Rule110 truth table.

## 2. A direct proof of necessity

Normalize s=1 and put rho=t/s>=1, S={0,1,rho,1+rho}. Denote
the affine expression in (2) by F(a,b,c,y). Its coefficient alpha
cannot vanish: otherwise the true row (0,1,1,1) and false row
(1,1,1,1) would have the same value. Replacing F by 1+rho-F
preserves membership in S, so assume alpha>0.

Write the following true-row values as

    p0=F(0,0,0,0)=epsilon,
    p1=F(0,0,1,1),
    p2=F(0,1,0,1),
    p3=F(0,1,1,1),
    p7=F(1,1,1,0).

Both p_i and p_i+alpha belong to S for i=0,1,2, because changing
a does not change the required output in those three cases. Also
p0 differs from p1 and p2. For example, if p0=p1 then
gamma+delta=0, and the true value p3 would equal the false value
F(0,1,0,0)=epsilon+beta. The other inequality is symmetric.

For the last two cases, the forbidden opposite outputs give

    p3 belongs to S but p3+alpha does not,
    p7 belongs to S but p7-alpha does not.         (3)

Suppose first rho>1 and rho!=2. Among positive differences between
elements of S, only 1 and rho occur for two distinct pairs.
Since p0 and p1 are distinct elements of S intersect (S-alpha),
it follows that alpha is either 1 or rho. In each case this
intersection has exactly two elements. As p0 differs from both
p1 and p2, one has p1=p2, hence beta=gamma. Therefore

    p3=p1+beta,
    p7=epsilon+alpha+2beta.                       (4)

If alpha=1, the two overlap values are {0,rho}. Condition (3)
requires p3 in {1,1+rho} and p7 in {0,rho}.

* If epsilon=0 and p1=rho, equation (4) gives beta=1-rho or
  beta=1. The second choice makes the false value F(0,1,0,0)=1
  belong to S. For beta=1-rho, the condition on p7 is
  3-2rho in {0,rho}, giving rho=3/2 or rho=1. Only 3/2 is in
  the current domain.
* If epsilon=rho and p1=0, then beta=1 or 1+rho. The first
  choice makes the same false value equal to 1+rho. The second
  gives p7=3rho+3, outside {0,rho}.

If alpha=rho, the overlap values are {0,1}. Now p3 belongs to
{rho,1+rho} and p7 belongs to {0,1}.

* If epsilon=0 and p1=1, then beta=rho-1 or rho. The latter
  again makes F(0,1,0,0) belong to S. The former gives
  p7=3rho-2>1 for rho>1, impossible.
* If epsilon=1 and p1=0, then beta=rho or rho+1. The first
  makes the false value equal to rho+1, and the second gives
  p7=3rho+3 outside {0,1}.

This leaves only rho=3/2 in the nonexceptional case.

For rho=2, S={0,1,2,3}. The distinct overlap values force
alpha=1 or 2. The alpha=2 case is excluded by the same alpha=rho
argument just given. If alpha=1, then p0,p1,p2 lie in {0,1,2},
while (3) forces p3=3 and p7=0. Without assuming beta=gamma,
the identities beta=p3-p1 and gamma=p3-p2 give

    0=p7=epsilon+1+beta+gamma
        =epsilon+7-p1-p2.

But p1+p2<=4 and epsilon>=0, a contradiction.

Finally, for rho=1, S={0,1,2}. Two distinct overlap values force
alpha=1, with p0,p1,p2 in {0,1}, p3=2 and p7=0. The same
identity gives 0=epsilon+5-p1-p2, again impossible. This proves
the theorem over the whole real parameter domain.

## 3. An independent exact finite classification

`../verification/explore_rule110_two_subset_weights.py` and its
JSON receipt implement a second, exhaustive proof strategy using
exact rational arithmetic. There is no coefficient bound or ratio
cutoff. Write each candidate allowed value as a pair representing
p+q*rho, where the four pairs are (0,0),(1,0),(0,1),(1,1).

Choose the allowed values of the five true rows

    (0,0,0,0), (0,0,1,1), (0,1,0,1),
    (0,1,1,1), (1,0,0,0).

There are exactly 4^5=1024 choices. These values determine all
five affine coefficients uniquely as linear expressions in rho.
For each choice, membership of the other three true rows imposes
either an identity, a finite set of exact rational ratios, or an
inconsistency. The program intersects these conditions and then
rejects every ratio at which any of the eight false rows enters S.
It separately tracks possible generic real families, for which
only finitely many ratios could be excluded by the false rows.

The exact output is

    1024 branches,
    surviving ratios: {3/2},
    generic families: none.

Every surviving representative is rechecked against all sixteen
Boolean assignments. This classification agrees with the direct
proof and with the achieved coefficient pair 2,3 in (1).

The result closes the proposed affine compression into a single
two-bit allowed-value field. It neither changes the published
80-operation finite-history component nor supplies a lower bound
for more general certificate constructions.
