# Cofinal strict bounds and a linear beta base

Prepared 25 October 2026. This is an ordinary mathematical proof for a semantic
source transformation, not a newly checked proof-assistant certificate.
The exact parent is the 245-variable `equation.json` in the incoming
`ConZFC_Joint_Norm_2026-10-25.zip`, inspected at ProveIt commit
`a0ef2df5bb1f73c35cd334bbc7f53553350ef06a`. Its source identity is recorded
in `certificate241.json` and checked against the literal byte string by the
reproduction script. The inherited arithmetic calibration is the one named
in the parent proof: finite C222 refutations are equivalent to finite ZF
refutations, which are equivalent to finite ZFC refutations. This note changes
only the arithmetic representation of those refutations.

## 1. Two distinctions that matter

The horizon t is existentially selected from the cofinal set 16+z^2. It may
be increased before F=t!, the pending-multiset states, or the beta-CRT code x
are constructed. Thus completeness need not realize every old horizon.

The derived-label expression J is evaluated in two different places.
Its value on each small, local proof-rule tuple can be required to be less
than t. Its value h=J(A,B,C,D) on the large global CRT representatives is
usually much larger than t and is the semantic Pell anchor. We do NOT impose
h<t. The binomial divisibility tests force the small local values below t
by reduction modulo the selected prime powers.

## 2. Strict ranges at one denominator

The parent tests the four local schema parameters and the derived label by
binom(A_j,t+1) divisibility. It tests the encoded row index by binom(C,t).
Replace the five lower indices t+1 by t. The affected ranges now assert

    0 <= a,b,c,d < t,       0 <= J(a,b,c,d) < t

on the decoded local tuples. Every old soundness argument needed only the
weaker bounds <=t, so its local arithmetic and Horn-flow conclusions remain
valid. In particular, weight separation for labels <=t remains applicable.
The ordinary source majorant L<R^E is valid on this smaller input box.

The one-sided prime-power range lemma used by the parent states that, for
p prime and k,e>=1,

    p^e | binom(a,k),  a>=0  ==>  a mod p^e < k.

Its application with k=t gives exactly the new strict ranges. For the
derived label, polynomial congruence identifies J(local tuple) with the
least residue of J(global representatives); both are below p^e because
the unchanged amplification estimate gives J(local tuple)<2^x<=p^e.
The range residue is below t, so J(local tuple)<t follows. No global upper
bound on h is used here.

For completeness, begin with a finite C222 proof tree of falsity. Let L be
the number of its rule-expansion steps. List every parameter tuple used by
the tree and include the fixed truth-padding tuple. Compute every full
local derived-label sum J on those finitely many tuples, including unused
branch codes. Choose t=16+z^2 strictly larger than L, every parameter, and
every such J. This is possible because 16+z^2 is cofinal. The choice precedes
F=t! and all accumulator values.

The parent precision-2x CRT construction then gives the required global
representatives. For a prime power p^{xm} dividing N=B^x, every target local
value w lies in [0,t-1]. The corresponding global representative a is
congruent to w modulo p^{2xm}. If a<t, binom(a,t)=0. Otherwise the falling
factorial defining binom(a,t) contains a-w, and

    v_p(t!) <= t-1 < xm

because x>=t. Thus p^{xm} divides binom(a,t). The same argument applies to
the derived polynomial J by polynomial congruence. This proves completeness
of each tightened test. There is no demand that an old witness at its old
horizon be extended unchanged.

## 3. Removing the q^(t+1) power request

Write M=q^x and let r_t=M/q^t be the existing normalization ratio. In the
parent, the exact factorial digit and the encoded-index range use r_t;
the four schema ranges and the derived-label range use the second ratio
r_{t+1}=M/q^(t+1). After Section 2, all seven use r_t. Therefore delete:

* the proposed q^(t+1) output;
* its power-congruence quotient;
* the private Pell-discriminant wire used only by the one-step formula;
* the now unused ratio r_{t+1}.

Keep the canonical t pair. It is needed for (F^2+1)^t and q^t. Keep the
power q^t, its quotient, and the ratio r_t. All other requested powers and
all fourteen independent principal Pell pairs remain.

Delete the square of the removed power output from the frame definition.
The remaining frame still has W=2+sum(atom^2), contains every actual base,
exponent and output of every retained request, and satisfies W>=258 because
t>=16 is retained. Keeping an additional redundant atom such as t+1 would
also be harmless. The signed-frame, semantic-anchor and pooled-orientation
proofs apply unchanged to the retained request family. The deleted request
had used a derived pair and was not an independent anchor.

The literal centered-parent edits are exactly these (zero-based indices):

    deleted variables: 114,172,173,235;
    deleted residuals: 124,125,175;
    in residuals 93,94,95,96,103: replace variable 235 by variable 234;
    in residual 159: remove the term -X114^2.

Every retained row remains quadratic. The result has 241 integer variables,
178 residuals, degree four, 5,217 collected monomials, and coefficient height
128,446. These exact counts are separately recomputed by the finite checker.

## 4. The early bootstrap needs a real adjustment

The parent rounded-factorial proof had inferred x>=t+1 from the integer
identity q^(t+1) r_{t+1}=q^x. That identity is now absent. The retained ratio
q^t r_t=q^x instead implies x>=t. We give the full changed estimates rather
than appeal to the obsolete stronger bound.

The shared remainder norm and the ceiling normalization still imply
M!=0, B!=0, and |FB-V|<|B|/2. The factorial-numerator request still gives
V=(F^2+1)^t. With b=|B|, the same elementary argument as in the parent gives

    b>=2,   |F|<b,   V<b^2.

The odd self-radix factor H=1+2 sum a_i is nonzero before any sign is known.
The signed-base power lemma gives x>=0, N=B^x and q=(BH)^x. The case x=0
would give q=M=1 and contradict B|M and b>=2. Thus x>=1 and |q|>=2. The
retained ratio q^t r_t=q^x now yields x>=t>=16. Put Q=|q|; then

    Q>=b^x>=b^t>=2^16.

The q+1 exponent requests therefore recover all actual representative
signs and h>0, just as before, so H>=1. Neither y nor the eventual beta
base restriction is needed at this stage.

If F!=0, the parent coefficient estimate remains
binom(F^2+t,j)<=V for 0<=j<=t. Its low signed remainder r0 satisfies

    |r0|/Q^t < V/(Q-1) < 2/b^(x-2)
                             <= 2/2^14 < 1/32.

Also binom(F^2+t,t)<=V<b^2 and b+b^2<b^t<=Q. Centered remainder uniqueness
therefore still forces B=binom(F^2+t,t)>0.

If F=0, then V=1 and FB-V=-1. The half-width ceiling bound forces b>=3.
All coefficients binom(t,j) are at most 2^t, and hence

    |r0|/Q^t < 2^t/(Q-1) < 2*(2/3)^t
                             <= 2*(2/3)^16 < 1/32.

The last strict comparison is the integer inequality
2^22=4,194,304 < 3^16=43,046,721. Again centered recovery would force B=1,
contradicting b>=3. Thus F=0 is excluded.

The parent nearest-integer factorial lemma now gives F=t! without change.
After the endpoint inequalities have been recovered, the stronger bound
x>=2+(t+1)y follows again. The early weakened x>=t bound was needed only to
cross the noncircular bootstrap stage; it causes no later precision loss.

The eleven canonical digit remainders retain their <M/32 bounds. The five
changed lower indices have decreased, so their old coefficient-majorant
bounds are still valid. The factorial ceiling error is the twelfth term in
the same norm. Its completeness budget 4*12*(M/32)^2<M^2 is unchanged.

## 5. Linearizing the beta base

A second cofinal use eliminates one further coordinate. Replace

    y=V(V-1)

by

    y=V-1,       V=(F^2+1)^t.

The new identity is affine. Its completeness follows from the strict tree
length condition already selected in Section 2. Starting with one pending
formula, each backward proof-tree expansion replaces one formula by at most
two premises. Thus every pending multiset has at most L+1<=t members.
Every formula label lies below t, and each weight is 1+jF. Since F=t!>=t,

    1+jF <= 1+(t-1)F < F^2+1.

If b0=F^2+1, every positive pending-state product is therefore less than
b0^t=V, including states consisting only of truth weights. Consequently each
state is at most V-1=y. Padding with truth steps leaves the state unchanged.
This is a strict bound on the actual finite proof witness, not a bound
assumed of arbitrary integer solutions.

Furthermore V=1 modulo F (in fact modulo F^2), so F divides y. The t+1 beta
moduli 1+j y, j=1,...,t+1, are pairwise coprime: a common prime divisor would
divide a nonzero difference of indices of absolute value at most t, hence
would divide t!=F and y, which contradicts its division of 1+j y. Every
state lies below each relevant modulus, so ordinary CRT supplies x and the
nonnegative quotients just as in the inherited construction. We can choose
x arbitrarily large in its CRT class.

For soundness, the frame and factorial bootstrap in Section 4 do not use
the old product identity for y. After F=t! has been proved, the replacement
gives y=V-1>F+2, since t>=16 and F=t!>=3. The first endpoint

    x=F+1+(y+1)u0

and x>=t>0 exclude u0<0. Thus x>=F+1. The last endpoint

    x=1+[1+(t+1)y]ut

forces ut>=1 and x>=2+(t+1)y. All remaining range lower indices t,y+1,x are
at most x. Also y>=F+1, so

    x-(2+t+y+F) >= t(y-1)-F > 0.

The inherited bound R=2+t+x+y+F<2x and its strict amplification estimate
R^E<2^x therefore remain valid. The derived-label coefficient estimate is
also unchanged: the old inequality ell(t+1)<2F<x remains available. The
factorial-weight Horn-flow proof needs only the actual bounds S,S'<=y,
positive weights, and the endpoint residues, all of which have just been
re-established.

Changing y changes the canonical beta code x, the global CRT representatives,
and the eventual Pell frame. Completeness reconstructs these witnesses in
that order from the finite proof. It does not keep their old values.
The anchor's large global representatives can still be chosen by the same
parity-prescribing CRT shifts. All fixed front indices are below N^2 by the
same estimates; reducing y cannot invalidate those estimates.

In the centered P245 coordinate system, actual y=X2-1 and V=X6. The original
row 162 is -1+X2+X6-X6^2. Replace it by X2-X6. It then has the exact integral
elimination X2=X6, which may be substituted into every other quadratic row
without increasing degree. This semantic source change followed by an exact
algebraic contraction removes one variable and one row. It can be composed
with the strict-range reduction and with independent exact circuit changes.

## 6. The logical conclusion and evidence boundary

The modified arithmetic system has an integer zero if and only if there is
a finite C222 refutation. Soundness is obtained by the signed-Pell bootstrap,
rounded-factorial recovery, strict range decoding, and the unchanged
factorial-weight Horn argument. Completeness chooses a sufficiently large
cofinal horizon, builds the smaller beta base, and then constructs all CRT,
remainder and Pell witnesses.

Composing with the named inherited finite syntactic translations gives, in
ZFC, equivalence of integer solvability to the existence of a finite ZFC
refutation. Negating gives equivalence of integer unsolvability to Con(ZFC).
These are ordinary finite arithmetic and syntactic arguments formalizable in
ZFC; no consistency assumption is made and no actual absence of solutions
is asserted.

Literal coefficient checks authenticate the supplied finite polynomial and
its changes. They do not substitute for the quantified argument above or for
the inherited calibration. All claims of improvement are relative to the
inspected parent and metric, not assertions of absolute minimality or
literature-wide priority.
