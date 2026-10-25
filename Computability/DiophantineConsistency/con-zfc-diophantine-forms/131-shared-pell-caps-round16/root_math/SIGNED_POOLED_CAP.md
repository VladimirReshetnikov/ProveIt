# A signed pooled Pell index certificate

This is a new arithmetic lemma for possible integration into the direct
proof-rule equation. It is not by itself a completed consistency equation.
The unsigned pooled-cap idea is inherited from the authenticated incoming
Shared Pell Bound 261 package. The additional contribution here is recovering
both signs of every principal Pell pair through the same bounded congruence.

## Statement

All parameters and coordinates in this note are integers. For A >= 2 define X_0=1, Y_0=0 and

    X_(j+1)=A X_j+(A^2-1)Y_j,
    Y_(j+1)=X_j+A Y_j.

Let W>=4 and 1<=m<=W. Suppose A-1>4W^3, V=Y_W(A), and
1<=k_i<W for every i=1,...,m. All x_i,y_i,Q,u,v,w below are unrestricted
integers. Impose

    x_i^2-(A^2-1)y_i^2=1                    for every i,
    V^2-1-sum_i y_i^2=u^2+v^2+w(w+1),
    sum_i [(y_i-k_i)^2+(x_i-1)^2]=(A-1)Q.

Then x_i=X_(k_i)(A), y_i=Y_(k_i)(A) for every i. Conversely all these
canonical pairs extend to a solution of the two aggregate rows.

## Soundness

The ternary form u^2+v^2+w(w+1) is nonnegative at every integer tuple.
Thus y_i^2<V^2, so |y_i|<V. The complete elementary Pell classification
over the integers gives a unique j_i>=0 and signs sigma_i,epsilon_i in
{1,-1} with x_i=sigma_i X_(j_i)(A) and
y_i=epsilon_i Y_(j_i)(A). The sign epsilon_i is immaterial when j_i=0.
Strict monotonicity of Y_j gives 0<=j_i<W.

Modulo A-1 the recurrence gives X_j=1 and Y_j=j. Hence A-1 divides

    E=sum_i [(epsilon_i j_i-k_i)^2+(sigma_i-1)^2].

This is a sum of nonnegative integers. Since both j_i and k_i belong to
[0,W-1],

    0<=E<=4m((W-1)^2+1)<=4W((W-1)^2+1)<4W^3<A-1.

Therefore E=0. Every sigma_i=1 and epsilon_i j_i=k_i>0, so epsilon_i=1
and j_i=k_i. No initial sign guard on x_i,y_i or Q was used. In
particular the zero-index and negative-coordinate branches are excluded
by the argument, not omitted from the classification.

## Completeness

For canonical pairs, every summand in the pooled congruence is divisible
by A-1 (indeed by its square), so its quotient Q is an integer.
Every k_i<W gives y_i<=Y_(W-1). The recurrence implies

    Y_W> (2A-1)Y_(W-1).

Since A-1>4W^3 and m<=W, (2A-1)^2>m+1. Consequently

    V^2-1-sum_i y_i^2 >= 0.

Every nonnegative integer G is u^2+v^2+w(w+1). To see this, Legendre's
three-square theorem represents 4G+1 as a sum of three squares: its residue
1 modulo4 guarantees exactly one odd square. Write the even squares as
(2u)^2,(2v)^2 and the odd square as (2w+1)^2, then divide by4.
This supplies the aggregate slack witnesses.

## Polynomial and compilation boundary

The displayed A and V are semantic parameters at this stage. An ordinary
equation must still certify V=Y_W(A), and establish A-1>4W^3 and all index
bounds before using this lemma. In the inherited square-frame construction
A>= (W+1)^W suffices: for W>=4,

    (W+1)^W-1 >= (W+1)^4-1 >4W^3.

The requested indices may include doubled ones provided the actual frame
bounds 2k_i<W. This must be checked from its literal atom ledger.

All displayed rows are polynomial. A quartic final sum of squares additionally
requires quadratic gates for A^2 and the products in the individual Pell
rows. Existing square registers can be reused in the pooled row, which is
quadratic in the displayed coordinates, without expanding a large square
of a long sum unnecessarily. The anchor certificate remains an explicit
proof obligation. No assumption of consistency or a refutation is used.

## A stronger aggregate sharing the anchor lower bound

Suppose in addition W>=2 max_i k_i+1. Replace the square-cap row by

    V=W+1+sum_i y_i^2+u^2+v^2+w(w+1).

This implies V>W and |y_i|<sqrt(V)<V, so both the preceding soundness
argument and the anchor's required bound V>=W hold at once. It removes
the need for a separate anchor-lower-bound predicate.

For completeness put k=max_i k_i. The addition identity gives
Y_(2k)=2X_k Y_k>2Y_k^2. Since W>=2k+1,

    Y_W >= Y_(2k+1) > (2A-1)Y_(2k) > 2(2A-1)Y_k^2.

Thus Y_W-sum_i y_i^2 > (4A-2-m)Y_k^2 > W, since m<=W,
A-1>4W^3, and Y_k>=1. Its difference from W+1 is a nonnegative integer
and has the required ternary representation.

For the square frame W=2(2+sum_a a^2), both an atom k and a doubled atom
2k meet this stronger bound: W-4|k|>=2((|k|-1)^2+1)>0.
The literal compiler must include every relevant exponent atom in this sum.

## Signed index extension for bootstrap ordering

If some requested indices have unknown sign before factorial recovery,
replace 1<=k_i<W by |k_i|<W. The identical bounded-error proof gives
x_i=X_(|k_i|), and y_i=sign(k_i)Y_(|k_i|), with y_i=0 when k_i=0.
It does not by itself prove k_i>0. An application may first interpret an
independently positive t-index, derive the factorial sign from its raw
ceiling rows, and only then prove the remaining indices positive. This
ordering must appear in the full compilation proof.

The stronger aggregate's completeness remains valid if all k_i=0:
all y_i vanish and Y_W>W+1. Otherwise the preceding proof applies with
k=max_i |k_i|. This signed-index extension does not assert that n^k is
an integer when k<0; that assertion is neither needed nor licensed.
