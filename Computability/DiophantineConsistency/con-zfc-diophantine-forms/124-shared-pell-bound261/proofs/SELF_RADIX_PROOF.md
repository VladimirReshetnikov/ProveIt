# A radix chosen from the actual representatives

This note proves a replacement of the common-radix and aggregate-bound part
of the frozen Round14 `derived16_cantor` natural-number construction. The
unchanged C222 calibration, arithmetic source, simultaneous Pell power
theorem, and nonnegative contraction theorem remain explicit dependencies.
This is an ordinary unbounded proof, not an object-ZFC or Lean proof object.

## The change

Write `N=B^K`, `K=R`, `R=2+t+x+y+F`, `t>=12`, and
`V=(F*t^2+1)^t`, with the meanings recovered in the inherited order. Let
`A_1,...,A_8,C` be the nine independently chosen positive CRT representatives,
and put

    S=C+A_1+...+A_8,       q=N*(V+1+S)^K.

Delete the equation `S+g=9N^2` and its slack `g`. No upper bound on a
representative is required anywhere in the new radix proof. In particular,
each free representative may be restricted to be at least two, as required
by the adjacent-coordinate Pell improvement, without any aggregate-cap
change.

`build_self_radix.py` changes exactly the radix part of the constructor;
`build_radix_R.py` additionally changes the amplification budget from 2R
to R. The
literal local source, all ten range requests, the two exact binomial
requests, factorial rows, and reciprocal index congruence are retained.

## Elementary carry lemma

Let N,V,S,K be positive integers, K>=2, and q=N*(V+S+1)^K.
Then N divides q, and

    q > V^K >= V^2,       q > (S+1)^K.

For 1<=n<=S and 1<=k<=K, every lower binomial coefficient satisfies

    0 <= binom(n,j) <= n^j <= max(1,S^k) < q,  0<=j<=k,

where binom(n,j)=0 for j>n. In the j=0 case the coefficient is one.

More generally, if a nonnegative derived argument J satisfies
J<=(S+1)^ell and ell*k<=K, then

    binom(J,j) <= max(1,J^k) <= (S+1)^(ell*k) < q,

for 0<=j<=k. Thus all the inherited quotient/remainder digit equations
recover the intended binomial coefficient, with no representative bound.

## Noncircular bootstrap

Before assigning factorial or binomial semantics, the raw reciprocal-index
row is

    C+F^2+1=B*i_q.

Its left side is positive, so the natural B is positive. The raw exponent
K=R is at least two. The base F*t^2+1 is positive, and the other radix
base V+S+1 is positive independently of V's intended meaning. The unchanged
simultaneous power theorem therefore gives V>=1, N=B^K>=1, and the stated
value of q. Hence q>V^2 before either binomial has been interpreted.

The unchanged ceiling equations for the proposed factorial output are

    V+D=D*F+u+1,          D=u+v+1.

They give D>=1 and V+v=D*F, so F>=1. Set rho=F*t^2; then rho>=t. For
0<=j<=t, the usual coefficient bound gives

    binom(rho+t,j) <= binom(rho+t,t) <= (rho+1)^t=V<q.

The first exact digit is now justified. The inherited self-bounding
factorial lemma proves F=t!. Independently of that intended value,

    F^2+t <= (F*t^2+1)^2,

so binom(F^2+t,j)<=V^2<q for 0<=j<=t. The second exact digit therefore
gives B=binom(F^2+t,t), the product of the pairwise-coprime reciprocal
moduli. Consequently B>=2 and N>=2^K. No decoded representative bound
has entered any preceding step.

## Ordinary ranges and the derived label range

Each of the nine independent representatives is at most S. Their lower
indices are t, t+1, x+1, or y+1, hence at most R-1<K. The elementary carry
lemma proves correctness of all nine corresponding range graphs.

The retained literal certificate for the nonnegative label polynomial J
states that J(a,b,c,d)<=(n+1)^ell whenever a,b,c,d<=n, with
ell=4,194,304. Taking n=S therefore gives J(A)<=(S+1)^ell. The old
factorial estimate is stronger than required:

    3*ell*(t+1) <= 2F       for t>=12, F=t!.

In particular ell*(t+1)<=2F/3<F<R=K. The derived range's lower binomial index is
t+1, so all its lower coefficients are strictly less than q by the same
lemma. This justifies exactly N | binom(J(A),t+1), and the unchanged
derived-range proof recovers J(local)<=t.

The factorial-floor argument gives L(local)<R^E<2^R=2^K. At the new
minimum, 12!=479,001,600>2^28, 28E=234,881,024<2^28, and 2E<=2^28.
Thus r^E<2^r for r>=2^28 by the inherited one-step induction, and R>=F
supplies that floor. The derived budget holds at t=12 since
3*4,194,304*13=163,577,856<2*12!=958,003,200, and persists when t
increases because factorial growth dominates t+1. All remaining source
padding and arithmetic arguments require only a positive horizon. The
original horizon-16 instance remains a valid alternate coefficient tuple.
Every range lower index is less than K; its factorial denominator loses
at most k-1<K prime-adic digits, so the existing precision-2K CRT proof
also remains valid at this smaller amplification. Prime-power
range decoding now recovers the same bounded local source rows and the
same Horn-flow refutation. Thus a zero of the modified arithmetic system
gives a finite C222 refutation.

## Constructive completeness, including the offset two

Start with the inherited padded finite-proof construction and fix
t,x,y,F,K,B,N before choosing CRT representatives. For every coordinate
choose a representative modulo N^2 satisfying the original precision-2K
congruences. Add a nonnegative multiple of N^2 if necessary to make that
representative at least two. This changes no congruence and preserves
all the inherited range divisibilities: their proof used the strengthened
period N^2 rather than an upper bound on the representative.

Compute S and q from these actual representatives. The carry estimates
above apply regardless of how large the chosen representatives are.
Use the exact Euclidean digit quotients and remainders, the same local
evaluation quotient, and fresh simultaneous Pell witnesses. All newly
required private data exist by the unchanged power theorem. No aggregate
slack needs to be supplied, and there is no circular choice of q and CRT
representatives: representatives come first, q follows, Pell witnesses
come last.

This proves both directions. Substituting the completed quadratic graphs
and taking the sum of their squares yields an ordinary integer polynomial
over nonnegative integer variables. The final coefficient artifacts and
the separate contraction certificates determine its actual size; the
number of source variables alone is not a final polynomial size claim.

## Adjacent-coordinate check

For a seed at exponent k, assume the main chart uses natural P,Y with
P>=1, and satisfies

    P^2+Y^2-2APY=1,       nY=P+m+Tq_0,

where n,m,T,q_0 are natural and n<A. The power row gives P<=nY<AY;
Y=0 would contradict P>=1. Therefore X=AY-P is a positive integer and
X^2-(A^2-1)Y^2=1. Ordinary positive Pell classification yields
(X,Y)=(X_j(A),Y_j(A)), j>=1. If j=1 then P=AY-X=0, impossible. Thus
j>=2 and Y>=Y_2(A)=2A. The existing shared frame gives A>W>k, hence
Y>=k without its former slack. This reasoning precedes index recovery
and uses no intended power value m=n^k. Each seed must occur in at least
one retained power row, and completeness requires its prescribed k>=2.
Those are explicit interface obligations to audit in the combined build.
