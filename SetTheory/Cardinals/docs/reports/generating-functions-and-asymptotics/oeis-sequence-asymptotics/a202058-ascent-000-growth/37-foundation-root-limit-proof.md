# A202058: upgrade from the exact radius to the full root limit

Research addendum, 1 October 2026. This uses only the uniform barriers already proved in radius-proof.md. That file is not modified by this addendum.

## Statement

With a_n=A202058(n) and T=3*pi^2/8,

lim_(n->infinity) (a_n/n!)^(1/n)=1/T=8/(3*pi^2).

Equivalently, log a_n=log(n!)-n log T+o(n). This still does not give a ratio limit, a prefactor, or a stretched-exponential equivalent.

## 1. Growing-state estimate

For the state x_N=(N,1,N), N>=1, the established barriers give

log F(t(q),x_N)=N p(q)+O(E(q)+q),

uniformly in N, where

p(q)=(1/2)log(2e^q-1),
E(q)=O((1+q)^3 e^(q/8)).

Indeed, the extra exponent qu-qr is qR/(N+R), between 0 and q. Here q is a real parameter and t(q) increases to T.

Set d(q)=(d/dq)log t(q), and

M(q)=p_q(q)/d(q)=t(q) p_t(t(q)).

As q tends to infinity,

p_q(q)=1/2+O(e^(-q)),
d(q)=q e^(-q/2)/(sqrt(2)T) (1+O(q e^(-q/2))),
M(q)=T e^(q/2)/(sqrt(2)q) (1+o(1)).

The displayed relative error for d follows from t(q)=T-O(q e^(-q/2)) and the explicit formula t_q=q/[sqrt(2e^q-1)(1-e^(-q))].

## 2. Uniform Chernoff lemma

For fixed N,q, put c_j=T^j 1(x_N), and define a probability distribution by

Pr(J=j)=c_j t(q)^j/[j! F(t(q),x_N)].

Let K=N M(q). For all sufficiently large q, all 0<epsilon<1/2, and eta=epsilon/8, the growing-state estimate implies

Pr(|J-K|>epsilon K)
 <=2 exp[-c N epsilon^2+2E(q+1)+O(q+1)]

for an absolute c>0, uniformly in N.

Here are the needed calculus bounds, to make the uniformity explicit. For |v|<=1 set

H_q(v)=p(q+v)-p(q)-M(q)[log t(q+v)-log t(q)].

Then H_q(0)=H_q'(0)=0. Uniformly on this fixed v-interval,

H_q''(v) -> (1/4)e^(-v/2),
M(q)d(q+v) -> (1/2)e^(-v/2).

These limits follow by differentiating the explicit formulas above; in particular d'(q)/d(q)->-1/2 uniformly after bounded shifts. Thus, for all q above one fixed threshold,

|H_q(v)|<=v^2/2 for |v|<=1,
M(q)|log t(q+eta)-log t(q)|>=eta/4,
M(q)|log t(q-eta)-log t(q)|>=eta/4.

For the upper tail, compare F(t(q+eta),x_N) with F(t(q),x_N), and multiply by [t(q)/t(q+eta)]^((1+epsilon)K). Its logarithm is at most

N H_q(eta)-epsilon N M(q)[log t(q+eta)-log t(q)]
 +2E(q+1)+O(q+1)
 <= -3N epsilon^2/128+2E(q+1)+O(q+1).

The lower tail uses q-eta and is identical. One can therefore take any fixed c<=3/128.

## 3. Extract a coefficient at almost every desired size

Let n tend through all positive integers. Choose

q=log n,
epsilon=(log n)^(-2),
N=floor((1-4epsilon)n/M(q)).

Then

N ~ (sqrt(2)/T)sqrt(n)log n,
K=NM(q)=(1-4epsilon)n+O(sqrt(n)/log n),
N epsilon^2 ~ (sqrt(2)/T)sqrt(n)/(log n)^3,
E(q+1)=O(n^(1/8)(log n)^3).

The last quantity is little-o of N epsilon^2. The Chernoff bound thus puts probability at least 1/2 in the interval |j-K|<=epsilon K, for every sufficiently large n. There is some integer j in this interval with

c_j t(q)^j/j! >= F(t(q),x_N)/(4epsilon K+6).

Consequently

log c_j >= log(j!)-j log t(q)+N p(q)-E(q)-O(log n).

The choice of N ensures, for sufficiently large n,

(1-6epsilon)n <= j,
N+j <= n.

The first follows because the floor error is o(epsilon n). For the second, j<=(1+epsilon)(1-4epsilon)n while N=o(epsilon n).

The original state reaches x_N by N-1 successive new-maximal-label steps. Therefore a_(N+j)>=c_j. Every 000-avoiding ascent sequence can be extended injectively to a longer length by repeatedly appending one plus its current number of ascents. That label is new because the maximum used label is at most the number of ascents. Hence a_n>=a_(N+j)>=c_j.

Finally,

log(a_n/n!)
 >= -j log t(q) - log(n!/j!) + Np(q)-E(q)-O(log n)
 >= -n log T-o(n),

because t(q)->T, j/n->1, log(n!/j!)<=6epsilon n log n=o(n), E(q)=o(n), and Np(q)>=0. This proves the liminf at least 1/T. The radius theorem already gives the matching limsup.

## 4. Optional explicit, non-optimal logarithmic error

The same proof provides the coarse bound

log(a_n/n!)+n log T=O(n^(9/13)(log n)^3).

For the lower bound, choose q=(8/13)log n and epsilon=n^(-4/13)(log n)^2. Then N is of order n^(9/13)log n, E(q+1)=O(n^(1/13)(log n)^3), while N epsilon^2 is of order n^(1/13)(log n)^5. Also N=o(epsilon n), and the loss log(n!/j!) is O(epsilon n log n)=O(n^(9/13)(log n)^3).

For the upper bound use the root-state superbarrier at the same t(q) and coefficient positivity:

a_n/n! <= A(t(q))/t(q)^n,
A(t)=1+integral_0^t F(v,x_0)dv <=1+t F(t,x_0).

The superbarrier gives log A(t(q))<=E(q)+O(q+1). Since T-t(q)=O(qe^(-q/2)), the Cauchy bound is

log(a_n/n!)+n log T <=O(E(q)+q+nq e^(-q/2))
 =O(n^(9/13)log n).

The exponent 9/13 is an artifact of deliberately coarse barrier errors. This estimate should not be presented as a prediction of the true subexponential scale.
