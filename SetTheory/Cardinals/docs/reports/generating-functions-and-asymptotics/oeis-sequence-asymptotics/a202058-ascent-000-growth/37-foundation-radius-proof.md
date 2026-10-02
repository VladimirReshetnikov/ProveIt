# A202058: exact exponential-generating-function radius

Research proof draft, 1 October 2026. This proves a radius / factorial-normalized limsup. It does **not** yet prove existence of the normalized root limit, an asymptotic equivalent, or any stretched-exponential correction.

## 1. Exact positive operator

Let a_n count 000-avoiding ascent sequences of length n, including a_0=1. Conway–Conway–Elvey Price–Guttmann (2022), Sections 2.2 and 2.6, prove the compaction of once-seen labels. Their recurrence is equivalently the following positive operator.

States are x=(s,u,k), with integers s>=0, u>=1 and 0<=k<s+u. Put m=s+u. Here s is the number of once-used active labels; u is the number of unused active labels; k is one plus the adjusted last label. Twice-used labels have been deleted and once-used labels compacted to 0,...,s-1. From x, for every integer i in [0,m-1], use one transition:

* If i<s and i<k: x_i=(s-1,u,i).
* If i<s and i>=k: x_i=(s-1,u+1,i).
* If i>=s and i>=k: x_i=(s+1,u,i+1).
* If i>=s and i<k: x_i=(s+1,u-1,i+1).

The final case can occur only when u>=2, so this state space is invariant. Define (Tf)(x)=sum_i f(x_i). The initial state is x_0=(1,1,1). Then T^n 1(x_0)=a_(n+1). Write

F(t,x)=sum_(n>=0) T^n 1(x) t^n/n!,

as an extended nonnegative real function for t>=0. Its radius at x_0 equals the radius of A(t)=sum a_n t^n/n!, because F(t,x_0)=A'(t).

## 2. Characteristic curve and rank profile

For q>=0 put

p(q)=(1/2)log(2e^q-1), R(q)=2-e^(-q),

b(q)=e^p(1-e^(-q))/q, with b(0)=1,

t(q)=integral_0^q [1/b(v)] dv, and T_* = t(infinity).

Let q=q(t) be the inverse for 0<=t<T_*. Then

q'=e^p(1-e^(-q))/q,
p'=e^(-p)(e^q-1)/q.

For state x, put

D=s+Ru,
h(k)=min(k,s)+R max(k-s,0),
r=h(k)/D,
psi(t,x)=exp(ps+qu-qr).

All parameter values in this section are evaluated at q(t). We have 0<=r<=1, psi(0,x)=1, and

exp(ps+qu-q) <= psi(t,x) <= exp(ps+qu).

Define A=e^(-p)(e^q-1), B=e^p(1-e^(-q)), so B=RA. The scalar

lambda=(As+Bu)/q = AD/q

has its removable q=0 value m.

## 3. Uniform residual estimate

Claim: for every state and t<T_*,

| (partial_t psi)/psi - (T psi)/psi | <= C(q),

where C(q)=8(1+q)e^(5q/8).

### 3.1 Frozen rank integral

For real y in [0,m], define

w(y)=exp[-p+q 1_(y>=k)] if y<s,
w(y)=exp[p-q 1_(y<k)] if y>=s,

and g(y)=w(y) exp[-q(r(y)-r(k))], where r(y)=h(y)/D uses the unshifted state.

The exact integral identity is

integral_0^m g(y)dy=lambda.

One way to verify it is to set phi(y)=exp[-q h(y)/D]. Its derivatives are lambda phi'=-A phi on (0,s) and lambda phi'=-B phi on (s,m), while phi(m)=e^(-q)phi(0). These relations verify the integral operator eigen-equation at one endpoint and then by differentiation on both intervals. This also follows by direct integration of the two exponentials.

On each of the at most three intervals separated by the integers s and k, g is decreasing and bounded above by sqrt(2)e^(q/2). Indeed p lies between q/2 and q/2+(log 2)/2. If a transition is an ascent then its target rank is at least k; for a descent use r(k)-r(y)<=1. Consequently

|sum_(i=0)^(m-1) g(i)-lambda| <=3 sqrt(2)e^(q/2).

### 3.2 Shifted-state correction

For each i let r_i denote the rank fraction at the exact child state, and r(i) its frozen counterpart. Their explicit forms are:

D descent: r_i=i/(D-1).
D ascent: r_i=i/(D+R-1).
N ascent: r_i=(h(i)+1)/(D+1).
N descent: r_i=(h(i)+1)/(D+1-R).

All denominators are positive, and direct subtraction gives

|r_i-r(i)|<=4/D.

The exact transition ratio psi(x_i)/psi(x) differs from g(i) only by replacing r(i) by r_i. In every case other than a D ascent, r_i>=r(i), so the exact ratio is no larger than the frozen ratio. For a D ascent, k<=i<s, and

r(k)-r_i <= k(R-1)/[D(D+R-1)]
             <= (D-2)/D^2 <=1/8.

Here k<=s-1 and D>=s+1. Thus every frozen or exact transition ratio is bounded by sqrt(2)e^(5q/8). The elementary exponential mean-value bound now gives

|psi(x_i)/psi(x)-g(i)| <= (4q/D)sqrt(2)e^(5q/8).

Since m<=D, summing produces an error at most 4sqrt(2)q e^(5q/8).

### 3.3 Time derivative

For fixed state, differentiation gives

(partial_t psi)/psi=lambda-q'[r+q e^(-q) partial_R r].

On either side of k=s,

-1/(4R) <= partial_R r <=0.

For k<=s this is -ku/D^2. For k>=s it is -s(m-k)/D^2. Hence the bracket has absolute value at most 1. Also q'<=sqrt(2)e^(q/2). Combining the three estimates gives a residual bound at most

sqrt(2)[4e^(q/2)+4q e^(5q/8)] <=8(1+q)e^(5q/8),

as claimed.

## 4. Two-sided comparison, including the infinite-state issue

Set

E(q)=integral_0^q C(v)/b(v) dv,
g_-(t,x)=e^(-E(q(t)))psi(t,x),
g_+(t,x)=e^(E(q(t)))psi(t,x).

The residual bound proves partial_t g_- <= T g_- and partial_t g_+ >= T g_+, with both initial functions identically 1.

To justify comparison with the minimal positive exponential series, consider the continuous-time Markov chain which takes each of the m transitions at rate 1. Its generator is L=T-mI. Its jump rate is m and each jump increases m by at most one. It is nonexplosive by domination with a Yule process. Let tau_N be the first exit from m<=N. The stopped state space is finite.

The Feynman–Kac expectation is

F(t,x)=E_x exp(integral_0^t m(X_v)dv),

with infinity allowed. This equality follows directly by summing over finite jump paths: the holding-time exponential cancels the Feynman–Kac factor, leaving t^n/n! for each n-step path.

For g_+, stopped Dynkin comparison gives

E_x[exp(integral_0^t m); tau_N>t] <= g_+(t,x).

Letting N tend to infinity proves F(t,x)<=g_+(t,x), hence finiteness for t<T_*.

For the lower inequality choose epsilon>0 with t+epsilon<T_*. Stopped Dynkin comparison gives g_-(t,x) bounded above by the desired stopped terminal expectation plus the exit contribution with remaining function g_-(t-tau_N,X_tau_N). Uniformly over v in [0,t] and states y,

g_-(v,y)/g_+(v+epsilon,y) <= C_(t,epsilon) exp[-eta_(t,epsilon) m(y)],

where eta>0 is the minimum over that compact interval of both p(v+epsilon)-p(v) and q(v+epsilon)-q(v). Both functions are strictly increasing. Applying the later supersolution to the stopped exit expectation bounds that contribution by

C_(t,epsilon)e^[-eta(N+1)] g_+(t+epsilon,x),

which tends to zero. Therefore

e^(-E(q))psi(t,x) <= F(t,x) <= e^(E(q))psi(t,x),  0<=t<T_*.

This later-supersolution estimate is needed: formal comparison of an arbitrary subsolution with an unbounded positive operator alone would not suffice.

## 5. Matching upper bound on the radius

For q>=1, b(q)>=c e^(q/2)/q with c=1-e^(-1). Hence

E(q)=O((1+q)^3 e^(q/8))=o(e^p).

The positive semigroup identity (valid with infinity allowed by Tonelli) is

F(t+delta,x_0)=sum_(n>=0) delta^n/n! (T^n F(t,.))(x_0).

For every n there is a deterministic path of n successive N steps from x_0 to x_n=(n+1,1,n+1). For this state r<1, and the lower comparison yields

F(t,x_n)>=exp[(n+1)p-E(q)].

Thus, for every fixed delta>0 and t<T_*,

F(t+delta,x_0)>=exp[p-E(q)+delta e^p].

Let t increase to T_*. The right side tends to infinity, since E=o(e^p). By monotonicity F(T_*+delta,x_0)=infinity. Together with Section 4, the radius is exactly T_*.

## 6. Exact integral evaluation

With y=sqrt(2e^q-1),

T_* = integral_1^infinity 2log((y^2+1)/2)/(y^2-1) dy.

Integrate by parts using the antiderivative log((y-1)/(y+1)) of 2/(y^2-1), and then put z=(y-1)/(y+1). The endpoint terms vanish and

T_* = -2 integral_0^1 log(z)(1+z)/[(1-z)(1+z^2)] dz.

The rational factor decomposes as 1/(1-z)+z/(1+z^2). Standard absolutely integrable geometric-series evaluations give pi^2/3 and pi^2/24 for the respective terms. Therefore

T_*=3pi^2/8.

## Conclusion and limitations

The theorem established by this draft is

radius(sum a_n t^n/n!)=3pi^2/8,
limsup_(n->infinity) (a_n/n!)^(1/n)=8/(3pi^2).

It is stronger than a numerical fit and proves the conjectured factorial exponential constant in the precise limsup sense. Existence of the full root limit, a ratio limit, the prefactor, and possible stretched/logarithmic corrections require further work. No numerical log-concavity observation is used here.

Source: A. R. Conway, M. Conway, A. Elvey Price and A. J. Guttmann, Pattern-Avoiding Ascent Sequences of Length 3, Electronic Journal of Combinatorics 29(4) (2022), P4.25, DOI 10.37236/11266, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v29i4p25/pdf/ . The recurrence/compaction is prior art; the barrier/radius argument above is the present research result, subject to independent audit.
