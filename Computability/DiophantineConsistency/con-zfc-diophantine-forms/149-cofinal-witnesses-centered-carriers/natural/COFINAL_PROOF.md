# Even descending factorials give a cofinal beta bound

This note proves the new change to the direct natural graph. Every variable is
in N={0,1,...}. It supplements the retained shift-free descending proof and the
positive-center/pooled-digit composition; it is not a new formal kernel proof.

## Exact finite change

In the uncontracted descending graph replace t=t0+12 by t=2t0+4 and replace

    y=F+endpoint.r0+1

by

    y+1=V,

where V is the already existing exact-power output for n^t and n+1=F².
Delete the now unused endpoint.r0 coordinate. No power request, frame atom,
Pell seed, denominator request, source expression or label polynomial is added.
The coefficient transformation substitutes old_t0=2 new_t0-8 in every raw
quadratic residual; this is a finite polynomial identity, NOT an unrestricted
natural-coordinate bijection. Its new natural-domain soundness and completeness
are the ordinary arguments below. The final contraction is separately certified.

## Sound bootstrap before factoriality

The row for the exact-power modulus at n is T_n+n²+1=2An. At n=0 it is
impossible. Together with n+1=F² it gives F>=2,n>=3 without using any power.
The first endpoint still gives x>=F+1>=3. Every exponent t,x,y+1 is positive
because t>=4 and all variables are natural. Thus the retained common scale,
canonical index anchor and positive power proof apply without knowing y>=F+1.
The pooled-bound restoration and positive-center restoration are performed
first exactly as in the composition proof. The low-digit rows still orient
all their consecutive Pell seeds: zero ordinate would give previous_Y=1 and
0=1+nonnegative terms. Deleting the factorial output bound does not affect this.

Recover the six powers V=n^t,N=B^x,q=(NS)^x,D_t=q^t,D_y=q^(y+1),D_x=q^x.
Now y=V-1. For F>=2 and t>=4,

    V=(F²-1)^t >=(F²-1)² > F+2,

so y>=F+1. Consequently the last endpoint has positive quotient and gives
x>=2+(t+1)y>max(t+1,y+1). This proves the common-root denominator divisibilities
before the first binomial interpretation.

The unchanged descending floor rows are V=BF+r and B=r+s+1. They give
B>=1 and V<B(F+1); also V>F(F+1). Therefore B>F>=2 and

    V<B(F+1)<=B²<=N<=q.

Every coefficient binom(n,j),0<=j<=t, is at most n^t=V<q. Hence the missing
output slack is restored naturally by o=q-B-1, the factorial digit is decoded,
and B=binom(n,t)>0. The descending fixed-point theorem (valid for t>=3)
then yields F=t!. There is no use of factoriality in the preceding deductions.

## Majorant and label budgets at the smaller horizon

Now t>=4 and F=t!>=24. Thus n>=575 and

    y=(F²-1)^t-1 >=575^4-1 >2^36,
    x>=2+(t+1)y >2^38.

Since t,F<y and t>=4, R=2+t+x+y+F<2x. The retained local-source ledger has
E=2^23. For all integers x>=2^38, (2x)^E<2^x: at the starting value this is
39E<2^38, and the induction step follows from
(1+1/x)^E<2 for x>=2E (expand and majorize its binomial series by the geometric
series in E/x). Thus the local source value is below2^x as required.
The derived-label ledger has ell=2^22; because y>ell,

    ell(t+1)<(t+1)y<x.

It follows that all derived-label coefficients needed through t+1 are <S^x<q.
All remaining range decoding, strict quotient ranges, descending reciprocal
CRT and Horn-flow soundness are exactly the retained arguments.

## Constructive completeness: the bound is genuinely cofinal

Start with a finite C222 refutation and expand it into a finite proof tree.
Choose an EVEN t>=4 at least its number of rule occurrences, every used local
parameter, every relevant full label sum, and the truth-padding label sum.
These are finite numbers determined before F or the pending-state products.
Set F=t!, n=F²-1,V=n^t, y=V-1.

The pending proof-tree multiset has at most t nontruth leaves at every stage.
Indeed these leaves are distinct roots of as-yet-unexpanded subtrees of the
fixed proof tree, and their count is bounded by the total number of rule nodes.
Truth leaves have weight1. Every nontruth label j is <=t, so its weight is
W_j=1+jF<=1+tF. For t>=3,F=t!, one has F>=t+3 and
1+tF<F²-1. Hence every pending product satisfies

    S_i <=(1+tF)^t < (F²-1)^t=V,

and is an integer <=y. Also y>=F+1. Since n≡-1 mod F and t is EVEN, F divides
y=n^t-1. The beta moduli 1+(i+1)y for0<=i<=t are pairwise coprime: a common
prime would divide an index difference<=t but not y, contradicting F=t!|y.
CRT therefore supplies x with the exact prescribed pending-state residues,
including the initial state F+1 and final state1. Add a sufficiently large
multiple of their product if needed; all quotient coordinates are natural.
This proves the entire local path with precisely the new fixed y.

Continue with the original descending d_i=F²/i-1, B=product d_i,N=B^x.
Choose the precision-N² CRT representatives, lift the a representative by N²,
and thereby make the existing derived label J at least twice every nonanchor
seed index. Define S and q=(NS)^x only after these representatives. Define the
three distinct denominator powers, frame W and lower Pell witness next. Choose
A in the common-root congruence class and sufficiently large; then choose the
principal and seed Pell pairs, fresh positive-center auxiliary/comparison
pairs, and the merged error quotient. None of these choices changes x,y or
the already chosen indices. The order remains acyclic.

For pooled-digit completeness the ordinary coefficients below every range
position are <=S^x; those for J are also <=S^x by ell(t+1)<x. Factorial low
coefficients are <=V<B²<=N. A group has at most five members, so its coefficient
sum is <=5S^x+N<q=N^x S^x (N>=4,x>=2,S>=2). Thus every group's canonical low
remainders sum to at most D-1, supplying its nonnegative shared slack. All
remaining natural witnesses are the inherited constructive ones.

## Measured output and proof boundary

The modified raw source has324 natural variables and276 quadratic rows.
The fixed-priority low-height endpoint has219 variables,171 quadratic rows,
9253 quartic terms and coefficient height560710452. The sparse cap32 endpoint
has221 variables,173 rows,6269 terms and height83847181. These are finite exact
contraction checks, not empirical evidence for the unbounded lemma.
