# A202058: a quadratic-logarithm upper bound

Research extension, 2 October 2026. The frozen 1 October report is not modified.

## Result

Let a_n count ascent sequences of length n in which every value occurs at most twice. Put T=3π²/8 and μ=1/T. Then

    log(a_n/(n! μ^n)) <= C (log(n+2))²

for an absolute finite constant C. In particular, no equivalent

    a_n ~ C0 n! μ^n exp(c n^σ) n^g (log n)^h

with C0>0, c>0, σ>0 and fixed real g,h is possible. This theorem neither proves a lognormal equivalent nor excludes a negative stretched-exponential correction.

The proof only uses the exact positive transfer operator and characteristic functions established and audited in the frozen report. The new ingredients are a weighted residual estimate and a padding supersolution.

## 1. Notation and previously established identities

States are x=(s,u,k), s>=0, u>=1, 0<=k<s+u. Let m=s+u. For i=0,...,m-1, the four child types are

    D descent: (s-1,u,i),       i<s, i<k
    D ascent:  (s-1,u+1,i),     i<s, i>=k
    N ascent:  (s+1,u,i+1),     i>=s, i>=k
    N descent: (s+1,u-1,i+1),   i>=s, i<k.

T_op f is the sum over these children. For x0=(1,1,1), F(t,x0)=A'(t), where F(t,x)=sum_j T_op^j 1(x)t^j/j! and A(t)=sum_n a_n t^n/n!.

For q>=0 define

    p=(1/2)log(2e^q-1), R=2-e^(-q),
    b=e^p(1-e^(-q))/q, t(q)=integral_0^q dv/b(v).

Their values at zero are defined continuously. The established endpoint is t(∞)=T. Put

    D=s+Ru,
    h(y)=min(y,s)+R max(y-s,0), r(y)=h(y)/D,
    ψ(q,x)=exp(ps+qu-q r(k)), λ=Db/R.

Define the frozen transition ratios g(i) exactly as in the report. On each interval separated by the integer breakpoints s,k, g is decreasing, and

    integral_0^m g(y)dy=λ,
    0 <= S-λ <= 3sqrt(2)e^(q/2),  S=sum_i g(i).

The lower inequality, implicit in the earlier report, follows because the left-endpoint sum on each of those intervals dominates its integral. Also

    ∂_t ψ/ψ = λ-b B,
    B=r(k)+q e^(-q) ∂_R r(k),  |B|<=1.

Every child rank r_i satisfies |r_i-r(i)|<=4/D. All except D ascents satisfy r_i>=r(i). For a D ascent,

    0 <= r(i)-r_i = i(R-1)/(D(D+R-1)) <=1/D.

## 2. Improved weighted residual estimates

Because ψ(x_i)/ψ(x)=g(i)exp(-q(r_i-r(i))),

    T_op ψ/ψ <= e^(q/D) S,
    T_op ψ/ψ >= e^(-4q/D) S >= e^(-4q/D) λ.

Consequently

    (T_op ψ-∂_t ψ)/(bψ)
      <= (D/R)(e^(q/D)-1)
         +3sqrt(2)[e^(q/2)/b]e^(q/D)+1
      <= q e^(q/D)+3sqrt(2)(q+1)e^(q/D)+1.                (U)

Here R>=1 and

    e^(q/2)/b = q/[sqrt(2-e^(-q))(1-e^(-q))] <=q+1.

The last inequality follows from e^q>=1+q. The formula is continuous at q=0.

In the other direction, for every state without any restriction on D,

    (∂_t ψ-T_op ψ)/(bψ)
      <= (D/R)(1-e^(-4q/D))+1 <=4q+1.                 (L)

This replaces the old exponentially large lower-barrier error by E_-(q)=2q²+q.

## 3. Padding removes small-state upper errors

Fix Q>0 and choose an integer L>=Q. Map states by

    I_L(s,u,k)=(s+L,u,k+L).

This is an invariant-state-space map. Each transition from x indexed by i maps to the transition from I_Lx indexed by i+L: check all four child formulas directly. The padded state additionally has L transitions indexed below L. Therefore for every nonnegative f,

    T_op(f∘I_L)(x) <= (T_op f)(I_Lx).                  (P)

For padded states, D>=L+1>=Q. Thus for 0<=q<=Q, e^(q/D)<=e. Let

    H(q)= [e(1+3sqrt(2))/2]q² +(3sqrt(2)e+1)q.

Its derivative dominates the right side of (U). Define

    G_Q(t,x)=exp(H(q(t))) ψ(q(t),I_Lx), 0<=t<=t(Q).

Equations (U) and (P) imply ∂_t G_Q>=T_op G_Q. Its initial value is 1.

The stopped Feynman–Kac supersolution comparison in the frozen report applies without alteration: stop the nonexplosive chain when m exits a finite set, discard the positive exit term, and let the cutoff increase. Hence

    F(t(q),x)<=exp(H(q)) ψ(q,I_Lx), 0<=q<=Q.          (1)

Only an upper comparison is used here; there is no claim that padding commutes with T_op or that it gives a lower barrier.

For x=x0 and L=ceil(Q),

    log F(t(Q),x0) <= H(Q)+(L+1)p(Q)+Q
                     =O(Q²),                       (2)

since p(Q)<=Q/2+(log2)/2.

The same supersolution at time t+ε justifies the lower comparison for exp(-2q²-q)ψ by the later-supersolution method from the frozen report. The padded upper comparison still decays exponentially against growing unpadded states because its extra L is fixed during this argument. Thus

    F(t(q),x)>=exp(-2q²-q)ψ(q,x)                     (3)

for every state and every fixed finite q. This lower function estimate is useful, but does NOT give a quadratic-logarithm coefficient lower bound.

## 4. Coefficient upper bound

Coefficient positivity gives

    a_n/n! <= A(t(Q))/t(Q)^n,
    A(t)<=1+t F(t,x0),

since F(t,x0) has nonnegative coefficients and is increasing. Moreover

    T-t(Q)=O((Q+2)e^(-Q/2)).

Choose Q=2log(n+2). Then

    n log(T/t(Q))=O(log(n+2)),
    log A(t(Q))=O((log(n+2))²).

Combining these inequalities proves the result stated at the start.

## 5. What is still missing

This is a one-sided coefficient theorem, substantially sharper than the frozen symmetric O(n^(9/13)(log n)^3) error. It rules out positive stretched-exponential growth after factorial normalization. It does not determine a quadratic-logarithm coefficient, a power or logarithmic prefactor, a ratio limit, or an asymptotic equivalent.

The lower function bound (3), even together with (1), does not determine an individual coefficient. The existing growing-state Chernoff argument only places most tilted mass in a broad window and extracts some coefficient there. Moving that coefficient to the requested index using the deterministic padding path loses much more than log²n. A local limit estimate, coefficientwise regularity such as normalized log-concavity, or a substantially more exact generating-function analysis is needed before claiming matching fine asymptotics.
