# Unified factorial CRT product and one shared Pell cap

## Result and scope

The principal composed construction has 249 nonnegative integer variables and
186 quadratic residuals. The polynomial is the sum of the squares of every
residual in natural/equation.json. It has degree four. At the horizon offset
12, its collected polynomial has 27,078 nonzero monomials and coefficient
height 85,178,741. This is a composition, not a claim that the supplied shared
Pell cap is new: the incoming cap theorem supplies the shared-index mechanism;
round15 supplies the square-output factorial/product fusion. The additional
radix here is (NH)^K, where H is one plus the sum of the actual independent CRT
representatives. It needs neither a representative upper-bound equation nor
the factorial numerator in its base. The amplification budget is K=R.

The retained C222 calculus calibration and Horn-flow argument are dependencies.
With those dependencies the natural zero set is nonempty exactly when the
calculus has a finite refutation, and ZFC proves the equivalence between
unsolvability and Con(ZFC). This work does not prove consistency and does not
supply a new machine-checked object-language ZFC derivation.

All variable powers in this note denote ordinary finite Pell graphs in the
emitted arithmetic system. None remains as a primitive in the coefficient
artifact. All variables in the natural endpoint range over integers >=0.

## Definitions and order of interpretation

Let t=t0+h, h>=12, and let F be the proposed factorial. Put

    V=(F^2+1)^t, B=choose(F^2+t,t), R=2+t+x+y+F,
    K=R, N=B^K, H=1+C+A1+...+A8, q=(NH)^K.

The notation B=choose(...) is initially only a proposed binomial output. The
raw rows are

    V+B=BF+u+1, B=u+v+1.

The nine representatives C,A1,...,A8 are positive by their raw affine offsets.
Therefore H>=10. The raw shared-cap power theorem first applies to every
independently positive base. In particular it gives V=(F^2+1)^t>=1. The second
raw row gives B>=1 and subtracting the rows gives V+v=BF. Thus F>=1,
V>F^2 and BF>=V, whence B>F and V<B^2. The positive-base theorem now gives
N=B^K and q=(NH)^K. Since K>=2, N>=B^2>V and q>=N>V. Moreover N divides q.
This argument uses no binomial semantics, decoded representative, or factorial
identity, and hence is noncircular.

For positive r and n, every coefficient choose(r+n,j), 0<=j<=n, is at most
(r+1)^n. The proof is induction using Pascal's identity for j<n and the product
formula for j=n. Applying it with r=F^2,n=t shows that all coefficients relevant
to B are <=V<q. The exact digit graph therefore really gives
B=choose(F^2+t,t).

## The square factorial fixed point at horizon twelve

Write T=t! and f=V/B. The two ceiling rows are equivalent to F-1<f<=F, so
F=ceil(f). Also

    f=T product_(i=1)^t (F^2+1)/(F^2+i).

Every factor is <=1, hence F<=T. Each factor is nondecreasing in F^2; since
F>=1, f>=2^t/(t+1)>t^2 for t>=12. The last inequality starts from
4096>12^2*13=1872; its induction step uses t^2>=3t+2. Thus F>t^2.
For ai=(i-1)/(F^2+i),

    sum ai<t(t-1)/(2F^2)<1/(2F).

The finite product bound product(1-ai)>=1-sum ai gives
T(1-1/(2F))<f<=F. Consequently

    T<2F^2/(2F-1)=F+F/(2F-1)<=F+1.

Integrality gives T<=F, so F=t!. Conversely for F=T the same estimate gives
T-1/2<f<=T. The explicit natural ceiling witnesses therefore exist. This
extends round15's stated horizon-16 proof to horizon 12, without changing its
identity or introducing a new fixed point.

## CRT product and the self-sized radix

For 1<=i<=t set di=1+F^2/i. Since F=t!, every di is an integer congruent to one
modulo F. Every prime divisor of di is greater than t. If a prime divided di
and dj, it would divide i-j, so the di are pairwise coprime. Their product is
exactly B=choose(F^2+t,t).

Every independent representative n is strictly less than H. The lower index
of each of its range graphs is t, t+1, x+1 or y+1, and is at most R-1<K.
For every 0<=j<=k,

    choose(n,j)<=max(1,n^k)<H^K<=q.

Coefficients with j>n are zero. Thus these digit graphs recover exactly the
nine required divisibilities by N. This proof imposes no bound on the actual
representative and deletes the round15 aggregate-cap row and slack.

Let J be the derived nonnegative label sum. The retained literal majorant
certificate gives J(A)<= (n+1)^ell with ell=4,194,304 and n the largest of the
four encoded schema parameters. Since n+1<=H, J(A)<=H^ell. At t=12,
3ell(t+1)=163,577,856<958,003,200=2*12!. The inequality persists under increasing
t because factorial growth dominates t+1. Hence

    ell(t+1)<=2F/3<F<K.

All coefficients through index t+1 in the derived-label digit are consequently
<q. That graph therefore gives N dividing choose(J(A),t+1), without putting
J(A) in H or requiring an upper bound on its encoded value.

The retained local nonnegative source majorant has E=8,388,608. For t>=12,
F>=12!>2^28, 28E=234,881,024<2^28 and 2E<=2^28. At r=2^28 this proves r^E<2^r;
for successive r, (1+1/r)^E<2 follows by bounding the binomial sum by a geometric
series with ratio E/r<=1/2. Thus every local source value and local label sum
is <R^E<2^R=2^K. This is the required no-wrap bound with K=R, not 2R.

## CRT soundness and completeness

The inherited prime-power binomial lemma says that p^e dividing choose(a,k)
forces a modulo p^e to lie in [0,k-1]. For row i-1 choose p dividing di and
m=vp(di). The raw B divisibility of C+F^2+1 identifies C modulo p with i-1.
The index range then identifies its small residue modulo p^(Km) with exactly
that index. The other ranges decode every local coordinate in its prescribed
interval. The local divisibility by N and the preceding local bound force the
nonnegative local source value to be zero, not merely congruent to zero.
The derived-label range and its local bound likewise force J(local)<=t.
The unchanged beta consistency and pairwise-coprime weight flow then recover
a finite C222 refutation.

Conversely start with a finite refutation, expand to a proof tree, pad the
horizon beyond all required parameters and label sums, and choose t>=h.
The inherited beta construction gives x,y and the local source rows. Set
F=t!, then B,K,N. Choose positive independent representatives by CRT modulo
N^2. There is no restriction on their size. For each range, the precision-2K
congruence supplies at least 2Km prime-adic digits in the falling-factorial
numerator, while division by k! loses at most k-1<K<=Km. Thus N divides every
required binomial. The same proof applies to the derived polynomial J because
polynomial congruences preserve the local label. Choose H and q afterwards.
The carry bounds apply regardless of these representatives' sizes; take
Euclidean digit witnesses and the simultaneous positive-power witnesses. This
constructs every raw witness without a fixed-point dependence on the radix.

## Shared Pell cap interface and logical independence

The composed source retains exactly the incoming pooled cap theorem. Its W is
2 plus the sum of distinct actual power bases, exponent atoms and outputs.
There are 15 distinct positive independent index atoms and one additive
index. Each independent k is <W, and their number is <=W-2. The scale equation
forces A-1>W^3 before any power has been interpreted. One complete indexed-Pell
certificate gives Vcap=Y_W(A). The aggregate row

    Vcap=W+1+s+sum(Y_i)

bounds all independent principal ordinates; the pooled congruence is

    sum(Y_i-k_i)^2=(A-1)Q.

Positive Pell classification gives Y_i=Y_ji(A) with 0<=ji<W. Reduction modulo
A-1 identifies the pooled error with sum(ji-ki)^2, lying in [0,W^3). Thus every
ji=ki. All sign/domain assumptions here are the natural ones. The incoming
cap theorem gives constructive completeness, including a nonnegative Q and
the aggregate slack. The single additive index is supplied by exact Pell
addition, not by an unchecked seed. Power congruences then recover every
requested exponentiation. The cap witnesses do not enter the semantic frame.

The raw source is therefore equivalent to the retained source theorem. The
exact natural-domain contraction restores every eliminated coordinate and
preserves existence in both directions. Finite expansion and regression tests
verify emitted syntax and examples, not the unbounded source theorem itself.

## Alternate radices

The builder also emits q=(BH)^K and q=N H^K. Both are multiples of N=B^K, both
are >=N>V and >H^K, so all arguments above remain valid. At offset 12 they also
have 249 natural variables and 186 rows; the principal (NH)^K endpoint is less
dense. These alternates are recorded as measured comparisons, not additional
logical assumptions.

## Sparse companion and the density tradeoff

The sparse companion retains one inequality Y_i<Vcap and one congruence
Y_i-ki=(A-1)qi for each independent seed, rather than the aggregate and pooled
square rows. It also retains Vcap=W+margin. Positive Pell classification and
the cap give 0<=ji<W, while the individual congruence gives ji=ki modulo A-1.
Since both indices lie in [0,W-1] and W<A-1, they are equal. Canonical pairs
supply the nonnegative individual quotients and slacks, so completeness is
unchanged. This is the supplied incoming sparse theorem composed with exactly
the same fused factorial and pure self-sized radix.

At offset 12 the sparse endpoint has 278 nonnegative variables, 215 quadratic
rows, 5,524 quartic monomials and height 83,852,788. The incoming sparse endpoint
had 292 variables, 225 rows, 6,140 monomials and height 83,933,334. The new sparse
endpoint improves each of those four measures. The 249-variable principal
endpoint saves a further 29 variables but has 27,078 monomials. These are two
Pareto alternatives; lower variable count does not mean lower density.
